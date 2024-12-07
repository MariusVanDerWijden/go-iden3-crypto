package poseidon

import (
	"errors"
	"fmt"
	"math/big"

	"github.com/iden3/go-iden3-crypto/ff"
	"github.com/iden3/go-iden3-crypto/utils"
)

// NROUNDSF constant from Poseidon paper
const NROUNDSF = 8

// NROUNDSP constant from Poseidon paper
var NROUNDSP = []int{56, 57, 56, 60, 60, 63, 64, 63, 60, 66, 60, 65, 70, 60, 64, 68}

const spongeChunkSize = 31
const spongeInputs = 16

func zero() *ff.Element {
	return ff.NewElement()
}

var big5 = big.NewInt(5)

// exp5 performs x^5 mod p
// https://eprint.iacr.org/2019/458.pdf page 8
func exp5(a *ff.Element) {
	a.Exp(*a, big5)
}

// exp5state perform exp5 for whole state
func exp5state(state []*ff.Element) {
	for i := 0; i < len(state); i++ {
		exp5(state[i])
	}
}

// ark computes Add-Round Key, from the paper https://eprint.iacr.org/2019/458.pdf
func ark(state, c []*ff.Element, it int) {
	for i := 0; i < len(state); i++ {
		state[i].Add(state[i], c[it+i])
	}
}

// mix returns [[matrix]] * [vector]
// while utilizing the scratch space to save on allocations
func mixWithScratch(state []*ff.Element, m [][]*ff.Element, scratch []*ff.Element) []*ff.Element {
	for i := 0; i < len(state); i++ {
		scratch[i].SetZero()
		for j := 0; j < len(state); j++ {
			scratch[i].Add(scratch[i], new(ff.Element).Mul(m[j][i], state[j]))
		}
	}
	for i := 0; i < len(state); i++ {
		state[i].Set(scratch[i])
	}
	return state
}

// HashWithState computes the Poseidon hash for the given inputs and initState
func HashWithState(inpBI []*big.Int, initState *big.Int) (*big.Int, error) {
	res, err := HashWithStateEx(inpBI, initState, 1)
	if err != nil {
		return nil, err
	}
	return res[0], nil
}

// OBS: assumes scratch and state are of equal length
func hashElements(state []*ff.Element, scratch []*ff.Element) []*ff.Element {
	t := len(state)
	nRoundsF := NROUNDSF
	nRoundsP := NROUNDSP[t-2]
	C := c.c[t-2]
	S := c.s[t-2]
	M := c.m[t-2]
	P := c.p[t-2]

	ark(state, C, 0)

	for i := 0; i < nRoundsF/2-1; i++ {
		exp5state(state)
		ark(state, C, (i+1)*t)
		state = mixWithScratch(state, M, scratch)
	}
	exp5state(state)
	ark(state, C, (nRoundsF/2)*t)
	state = mixWithScratch(state, P, scratch)
	newState0 := zero()

	for i := 0; i < nRoundsP; i++ {
		exp5(state[0])
		state[0].Add(state[0], C[(nRoundsF/2+1)*t+i])

		newState0.SetZero()
		for j := 0; j < len(state); j++ {
			newState0.Add(newState0, new(ff.Element).Mul(S[(t*2-1)*i+j], state[j]))
		}

		for k := 1; k < t; k++ {
			state[k] = state[k].Add(state[k], new(ff.Element).Mul(state[0], S[(t*2-1)*i+t+k-1]))
		}
		state[0].Set(newState0)
	}

	for i := 0; i < nRoundsF/2-1; i++ {
		exp5state(state)
		ark(state, C, (nRoundsF/2+1)*t+nRoundsP+i*t)
		state = mixWithScratch(state, M, scratch)
	}
	exp5state(state)
	state = mixWithScratch(state, M, scratch)
	return state
}

// OBS: assumes nOuts = 1
// assumes the last element of the state is the initState
// assumes scratch and state are of equal length
func hashWithStateExBytes(state []*ff.Element, scratch []*ff.Element) (*ff.Element, error) {
	if len(state) == 1 || len(state)-1 > len(NROUNDSP) {
		return nil, fmt.Errorf("invalid inputs length %d, max %d", len(state), len(NROUNDSP))
	}

	state = hashElements(state, scratch)

	return state[0], nil
}

func HashWithStateEx(inpBI []*big.Int, initState *big.Int, nOuts int) ([]*big.Int, error) {
	t := len(inpBI) + 1
	if len(inpBI) == 0 || len(inpBI) > len(NROUNDSP) {
		return nil, fmt.Errorf("invalid inputs length %d, max %d", len(inpBI), len(NROUNDSP))
	}
	if !utils.CheckBigIntArrayInField(inpBI) {
		return nil, errors.New("inputs values not inside Finite Field")
	}
	if nOuts < 1 || nOuts > t {
		return nil, fmt.Errorf("invalid nOuts %d, min 1, max %d", nOuts, t)
	}
	inp := utils.BigIntArrayToElementArray(inpBI)

	state := make([]*ff.Element, t)
	if !utils.CheckBigIntInField(initState) {
		return nil, errors.New("initState values not inside Finite Field")
	}

	state[0] = ff.NewElement().SetBigInt(initState)
	copy(state[1:], inp)

	scratch := make([]*ff.Element, len(state))
	for i := 0; i < len(scratch); i++ {
		scratch[i] = zero()
	}

	state = hashElements(state, scratch)

	r := make([]*big.Int, nOuts)
	for i := 0; i < nOuts; i++ {
		rE := state[i]
		r[i] = big.NewInt(0)
		rE.ToBigIntRegular(r[i])
	}
	return r, nil
}

// Hash computes the Poseidon hash for the given inputs
func Hash(inpBI []*big.Int) (*big.Int, error) {
	return HashWithState(inpBI, big.NewInt(0))
}

// HashEx computes the Poseidon hash for the given inputs and returns
// the first nOuts outputs that include intermediate states
func HashEx(inpBI []*big.Int, nOuts int) ([]*big.Int, error) {
	return HashWithStateEx(inpBI, big.NewInt(0), nOuts)
}

// HashBytes returns a sponge hash of a msg byte slice split into blocks of 31 bytes
func HashBytes(msg []byte) (*big.Int, error) {
	return HashBytesX(msg, spongeInputs)
}

// HashBytesXLessAlloc returns a sponge hash of a msg byte slice split into blocks of 31 bytes.
// uses less allocations than the original implementation.
func HashBytesXLessAlloc(msg []byte, frameSize int) ([]byte, error) {
	if frameSize < 2 || frameSize > 16 {
		return nil, errors.New("incorrect frame size")
	}

	state := make([]*ff.Element, frameSize+1)   // one additional item for initState, always 0
	scratch := make([]*ff.Element, frameSize+1) // Scratch space to reduce allocations
	for i := 0; i < len(state); i++ {
		state[i] = new(ff.Element)
		scratch[i] = new(ff.Element)
	}

	dirty := false
	currentHash := new(ff.Element)

	k := 0
	for i := 0; i < len(msg)/spongeChunkSize; i++ {
		dirty = true
		state[k].SetBytesLessMod(msg[spongeChunkSize*i : spongeChunkSize*(i+1)])
		if k == frameSize-1 {
			hash, err := hashWithStateExBytes(state, scratch)
			if err != nil {
				return nil, err
			}
			currentHash.Set(hash)
			dirty = false
			state[0].Set(hash)
			for j := 1; j < len(state); j++ {
				state[j].SetZero()
			}
			k = 1
		} else {
			k++
		}
	}

	if len(msg)%spongeChunkSize != 0 {
		// the last chunk of the message is less than 31 bytes
		// zero padding it, so that 0xdeadbeaf becomes
		// 0xdeadbeaf000000000000000000000000000000000000000000000000000000
		var buf [spongeChunkSize]byte
		copy(buf[:], msg[(len(msg)/spongeChunkSize)*spongeChunkSize:])
		state[k].SetBytesLessMod(buf[:])
	}

	if dirty {
		// we haven't hashed something in the main sponge loop and need to do hash here
		hash, err := hashWithStateExBytes(state, scratch)
		if err != nil {
			return nil, err
		}
		currentHash.Set(hash)
	}

	hash := currentHash.Bytes()
	return hash[:], nil
}

// HashBytesX returns a sponge hash of a msg byte slice split into blocks of 31 bytes
func HashBytesX(msg []byte, frameSize int) (*big.Int, error) {
	if frameSize < 2 || frameSize > 16 {
		return nil, errors.New("incorrect frame size")
	}

	// not used inputs default to zero
	inputs := make([]*big.Int, frameSize)
	for j := 0; j < frameSize; j++ {
		inputs[j] = new(big.Int)
	}
	dirty := false
	var hash *big.Int
	var err error

	k := 0
	for i := 0; i < len(msg)/spongeChunkSize; i++ {
		dirty = true
		inputs[k].SetBytes(msg[spongeChunkSize*i : spongeChunkSize*(i+1)])
		if k == frameSize-1 {
			hash, err = Hash(inputs)
			dirty = false
			if err != nil {
				return nil, err
			}
			inputs = make([]*big.Int, frameSize)
			inputs[0] = hash
			for j := 1; j < frameSize; j++ {
				inputs[j] = new(big.Int)
			}
			k = 1
		} else {
			k++
		}
	}

	if len(msg)%spongeChunkSize != 0 {
		// the last chunk of the message is less than 31 bytes
		// zero padding it, so that 0xdeadbeaf becomes
		// 0xdeadbeaf000000000000000000000000000000000000000000000000000000
		var buf [spongeChunkSize]byte
		copy(buf[:], msg[(len(msg)/spongeChunkSize)*spongeChunkSize:])
		inputs[k] = new(big.Int).SetBytes(buf[:])
		dirty = true
	}

	if dirty {
		// we haven't hashed something in the main sponge loop and need to do hash here
		hash, err = Hash(inputs)
		if err != nil {
			return nil, err
		}
	}

	return hash, nil
}

// SpongeHash returns a sponge hash of inputs (using Poseidon with frame size of 16 inputs)
func SpongeHash(inputs []*big.Int) (*big.Int, error) {
	return SpongeHashX(inputs, spongeInputs)
}

// SpongeHashX returns a sponge hash of inputs using Poseidon with configurable frame size
func SpongeHashX(inputs []*big.Int, frameSize int) (*big.Int, error) {
	if frameSize < 2 || frameSize > 16 {
		return nil, errors.New("incorrect frame size")
	}

	// not used frame default to zero
	frame := make([]*big.Int, frameSize)
	for j := 0; j < frameSize; j++ {
		frame[j] = new(big.Int)
	}
	dirty := false
	var hash *big.Int
	var err error

	k := 0
	for i := 0; i < len(inputs); i++ {
		dirty = true
		frame[k] = inputs[i]
		if k == frameSize-1 {
			hash, err = Hash(frame)
			dirty = false
			if err != nil {
				return nil, err
			}
			frame = make([]*big.Int, frameSize)
			frame[0] = hash
			for j := 1; j < frameSize; j++ {
				frame[j] = new(big.Int)
			}
			k = 1
		} else {
			k++
		}
	}

	if dirty {
		// we haven't hashed something in the main sponge loop and need to do hash here
		hash, err = Hash(frame)
		if err != nil {
			return nil, err
		}
	}

	return hash, nil
}
