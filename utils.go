package utils

import (
	"fmt"
	"iter"
	"os"
	"sort"
	"strings"
	"sync/atomic"
)

// ConcurrentQueue

type ConcurrentQueue[T any] struct {
	Items atomic.Pointer[NList[T]]
}

// make holder with Pointer[*NList], add method, etc
type NList[T any] struct {
	Processed atomic.Bool
	Item      T
	Next      *NList[T]
}

func (q *ConcurrentQueue[T]) Dequeue() iter.Seq[T] {
	head := q.Items.Swap(nil)
	return func(yield func(T) bool) {
		for ; head != nil && head.Processed.CompareAndSwap(false, true); head = head.Next {
			if !yield(head.Item) {
				break
			}
		}
	}
}

func (q *ConcurrentQueue[T]) Enqueue(item T) {
	newHead := &NList[T]{Item: item}
	for {
		newHead.Next = q.Items.Load()
		if q.Items.CompareAndSwap(newHead.Next, newHead) {
			return
		}
	}
}

func (q *ConcurrentQueue[T]) IsEmpty() bool {
	return q.Items.Load() == nil
}

// Set

type Set[T comparable] map[T]bool

func NewSetSeq[T comparable](it iter.Seq[T]) Set[T] {
	result := make(Set[T])
	for item := range it {
		result[item] = true
	}
	return result
}

func NewSet[T comparable](elements ...T) Set[T] {
	l := len(elements)
	if l == 0 {
		l = 8
	}
	result := make(Set[T], l)
	for _, item := range elements {
		result[item] = true
	}
	return result
}

func (s Set[T]) ToSlice() []T {
	items := make([]T, len(s))
	i := 0
	for item := range s {
		items[i] = item
		i += 1
	}
	return items
}

func (s Set[T]) Merge(s2 Set[T]) Set[T] {
	if s == nil && len(s2) > 0 {
		// this won't alter the receiver but the returned set will at least be correct
		s = NewSet[T]()
	}
	for k, v := range s2 {
		s[k] = v
	}
	return s
}

func (s Set[T]) Copy() Set[T] {
	return Set[T]{}.Merge(s)
}

func (s Set[T]) Union(s2 Set[T]) Set[T] {
	if len(s) == 0 {
		return s2
	} else if len(s2) == 0 {
		return s
	}
	return s.Copy().Merge(s2)
}

func (s Set[T]) Complement(s2 Set[T]) Set[T] {
	return s.Copy().Subtract(s2)
}

func (s Set[T]) Subtract(s2 Set[T]) Set[T] {
	for item := range s2 {
		delete(s, item)
	}
	return s
}

func (s Set[T]) Add(els ...T) Set[T] {
	if s == nil {
		return NewSet(els...)
	}
	for _, el := range els {
		s[el] = true
	}
	return s
}

func (s Set[T]) Remove(els ...T) Set[T] {
	for _, el := range els {
		delete(s, el)
	}
	return s
}

func (s Set[T]) Has(els ...T) bool {
	for _, el := range els {
		if !s[el] {
			return false
		}
	}
	return true
}

func (s Set[T]) Contains(s2 Set[T]) bool {
	if len(s) < len(s2) {
		return false
	}
	for item := range s2 {
		if !s.Has(item) {
			return false
		}
	}
	return true
}

func (s Set[T]) Intersection(s2 Set[T]) Set[T] {
	result := make(Set[T], 0)
	if len(s2) < len(s) {
		s, s2 = s2, s
	}
	for el := range s {
		if s2.Has(el) {
			result.Add(el)
		}
	}
	return result
}

func (s Set[T]) Intersects(s2 Set[T]) bool {
	if len(s2) < len(s) {
		s, s2 = s2, s
	}
	for item := range s {
		if s2.Has(item) {
			return true
		}
	}
	return false
}

func (s Set[T]) IsEmpty() bool {
	return len(s) == 0
}

func (s Set[T]) Seq() iter.Seq[T] {
	return func(yield func(item T) bool) {
		for item := range s {
			if !yield(item) {
				return
			}
		}
	}
}

func (s Set[T]) Seq2() iter.Seq2[int, T] {
	count := 0
	return func(yield func(key int, item T) bool) {
		for item := range s {
			if !yield(count, item) {
				return
			}
			count++
		}
	}
}

func (s Set[T]) String() string {
	sl := s.ToSlice()
	var f func(i, j int) bool
	var strs []string
	sortStrings := false

	switch x := any(sl).(type) {
	case []int:
		f = func(i, j int) bool { return x[i] < x[j] }
	case []int8:
		f = func(i, j int) bool { return x[i] < x[j] }
	case []int16:
		f = func(i, j int) bool { return x[i] < x[j] }
	case []int32:
		f = func(i, j int) bool { return x[i] < x[j] }
	case []int64:
		f = func(i, j int) bool { return x[i] < x[j] }
	case []uint:
		f = func(i, j int) bool { return x[i] < x[j] }
	case []uint8:
		f = func(i, j int) bool { return x[i] < x[j] }
	case []uint16:
		f = func(i, j int) bool { return x[i] < x[j] }
	case []uint32:
		f = func(i, j int) bool { return x[i] < x[j] }
	case []uint64:
		f = func(i, j int) bool { return x[i] < x[j] }
	case []uintptr:
		f = func(i, j int) bool { return x[i] < x[j] }
	case []float32:
		f = func(i, j int) bool { return x[i] < x[j] }
	case []float64:
		f = func(i, j int) bool { return x[i] < x[j] }
	default:
		// defer sorting until after string conversion
		sortStrings = true
	}
	if f != nil {
		sort.Slice(sl, f)
	}
	strs = make([]string, len(sl))
	for i, v := range sl {
		strs[i] = fmt.Sprint(v)
	}
	if sortStrings {
		sort.Strings(strs)
	}
	return fmt.Sprintf("Set[%s]", strings.Join(strs, ", "))
}

// Iters

type Seqable[T any] interface {
	Seq() iter.Seq[T]
}

type Seqable2[K any, T any] interface {
	Seq2() iter.Seq2[K, T]
}

type sliceSeqs[T any] []T
type mapSeqs[K comparable, T any] map[K]T

func SliceSeq[T any](slice []T) iter.Seq[T] {
	return SliceSeqs(slice).Seq()
}
func SliceSeq2[T any](slice []T) iter.Seq2[int, T] {
	return SliceSeqs(slice).Seq2()
}
func SetSeq[T comparable](set Set[T]) iter.Seq[T] {
	return set.Seq()
}
func SetSeq2[T comparable](set Set[T]) iter.Seq2[int, T] {
	return set.Seq2()
}
func MapSeq[K comparable, T any](m map[K]T) iter.Seq[T] {
	return MapSeqs(m).Seq()
}
func MapSeq2[K comparable, T any](m map[K]T) iter.Seq2[K, T] {
	return MapSeqs(m).Seq2()
}

func SliceSeqs[T any](slice []T) sliceSeqs[T] {
	return sliceSeqs[T](slice)
}

func (it sliceSeqs[T]) Seq() iter.Seq[T] {
	return func(yield func(item T) bool) {
		for _, item := range []T(it) {
			if !yield(item) {
				return
			}
		}
	}
}

func (it sliceSeqs[T]) Seq2() iter.Seq2[int, T] {
	return func(yield func(key int, item T) bool) {
		for i, item := range []T(it) {
			if !yield(i, item) {
				return
			}
		}
	}
}

func SetSeqs[T comparable](set Set[T]) Set[T] {
	return set
}

func MapSeqs[K comparable, T any](m map[K]T) mapSeqs[K, T] {
	return mapSeqs[K, T](m)
}

func (it mapSeqs[K, T]) Seq() iter.Seq[T] {
	return func(yield func(item T) bool) {
		for _, item := range map[K]T(it) {
			if !yield(item) {
				return
			}
		}
	}
}

func (it mapSeqs[K, T]) Seq2() iter.Seq2[K, T] {
	return func(yield func(key K, item T) bool) {
		for key, item := range map[K]T(it) {
			if !yield(key, item) {
				return
			}
		}
	}
}

func JoinStrings(iter Seqable[string], sep string) string {
	sb := &strings.Builder{}
	first := true
	for str := range iter.Seq() {
		if first {
			first = false
		} else {
			fmt.Fprint(sb, sep)
		}
		fmt.Fprint(sb, str)
	}
	return sb.String()
}

func Flatten[T any](iters ...Seqable[T]) iter.Seq[T] {
	return func(yield func(item T) bool) {
		for _, it := range iters {
			for item := range it.Seq() {
				if !yield(item) {
					return
				}
			}
		}
	}
}

func Flatten2[K comparable, T any](iters ...Seqable2[K, T]) iter.Seq2[K, T] {
	return func(yield func(key K, item T) bool) {
		for _, it := range iters {
			for key, item := range it.Seq2() {
				if !yield(key, item) {
					return
				}
			}
		}
	}
}

// misc
func EnsliceStrings(item any) []string {
	if item == nil {
		return nil
	} else if s, ok := item.(string); ok {
		return []string{s}
	} else if sA, ok := item.([]string); ok {
		return sA
	} else if a, ok := item.([]any); ok {
		t := make([]string, 0, len(a))
		for _, element := range a {
			if elStr, ok := element.(string); ok {
				t = append(t, elStr)
			} else {
				fmt.Fprintf(os.Stderr, "bad string value: %s\n", elStr)
			}
		}
		return t
	}
	fmt.Fprintf(os.Stderr, "bad string array value: %s\n", item)
	return nil
}

func PropStrings(value any) iter.Seq[string] {
	return func(yield func(item string) bool) {
		yieldif := func(str string) bool {
			if str != "" {
				return yield(str)
			}
			return true
		}
		if vstr, isString := value.(string); isString {
			yieldif(vstr)
		} else if vstrs, isStrings := value.([]string); isStrings {
			for _, str := range vstrs {
				if !yieldif(str) {
					return
				}
			}
		} else if varray, isArray := value.([]any); isArray {
			for _, item := range varray {
				if str, isString := item.(string); isString {
					if !yieldif(str) {
						return
					}
				}
			}
		}
	}
}
