## Worker report

The module defines `RingHom.integralExtensionDimension`, stating that an integral ring
homomorphism `f : R →+* S` satisfies `ringKrullDim S ≤ ringKrullDim R` and that every
maximal ideal of `S` contracts along `f` to a maximal ideal of `R`. The hypothesis
`hf : f.IsIntegral` renders the node's assertion that every element of the target is
integral over the source. The first conclusion renders the Krull-dimension inequality;
the second renders the maximal-ideal-over-maximal clause as
`∀ I : Ideal S, I.IsMaximal → (I.comap f).IsMaximal`.

The statement uses Mathlib's `RingHom.IsIntegral` (the root-of-a-monic-polynomial
condition for every target element), `ringKrullDim`, and ideal `comap`/`IsMaximal`.
The dependency declarations are `integralClosure`, `IsIntegral`, and
`IsIntegrallyClosedIn` from `Mathlib.RingTheory.IntegralClosure.Algebra.Basic`, and
`ringKrullDim` from `Mathlib.RingTheory.KrullDimension.Basic`.

Edge cases checked include the zero ring (where `ringKrullDim` is bottom), zero-length
prime chains, and arbitrary universe levels for source and target rings. No additional
hypotheses are introduced.

Searches: the node's recorded LeanSearch, LeanFinder, Loogle, and grep searches found
no single Mathlib theorem for the dimension inequality; they found only the component
incomparability and maximal-contraction results (`Ideal.IsIntegral.comap_lt_comap` and
`isMaximal_comap_of_isIntegral_of_isMaximal'`). Searches of the project source and
`lean/Sheaf` found no existing declaration of this statement.

## Earlier second reading (a previous round; superseded)

Reading the node and module together, the Lean signature matches every clause of the
node: `f` is the commutative-ring map, `hf` is integrality, the conjunction gives the
dimension bound and contraction of each maximal ideal. No mismatch was found.

## Second reading by F1

I independently read the node, its Stacks source citation (Algebra, Tag 00OJ,
with 00GT and 00OI), and `Sheaf.RingTheory.IntegralExtensionDimension`.
The objects and hypotheses match item by item:

* The source and target commutative rings A,B are rendered by
  `{R : Type u} {S : Type v} [CommRing R] [CommRing S]`; the ring map
  A → B is `f : R →+* S`.
* “B is integral over A” is exactly `hf : f.IsIntegral`, Mathlib's predicate
  that every target element satisfies a monic polynomial over the source image.
  No injectivity, Noetherian, finiteness, characteristic, or universe
  restriction is added.
* The dimension conclusion is exactly `ringKrullDim S ≤ ringKrullDim R`,
  using the dependency node's `ringKrullDim` definition.
* The maximal-ideal conclusion is exactly
  `∀ (I : Ideal S), I.IsMaximal → (I.comap f).IsMaximal`; contraction is the
  ideal-theoretic preimage along the given map.

The conjunction has the same two clauses and quantifier order as the node. The
module proof is `sorry` only, as required for stage 2, and its docstring records
the node's proof: contract prime chains and use incomparability for the dimension
bound, then use maximal contraction for the second clause. The imports are the
Mathlib Going-Up and Krull-dimension modules supplying the recorded notions.

Edge cases were checked against the definitions: the zero ring has bottom Krull
dimension and the universal maximal-ideal quantifier is vacuous when there are no
maximal ideals; length-zero prime chains are included by `ringKrullDim`; empty
index sets do not occur; arbitrary independent ring universes `u` and `v` are
allowed; no characteristic or nonzero assumption is present. Thus the Lean
statement covers the node's zero and dimension-zero cases.

I searched Mathlib and the project source by concept and by name using `msearch.py`
LeanSearch, LeanFinder, and Loogle queries for integral-extension Krull dimension
and maximal contraction, plus `rg` over Mathlib, `WeilConjectures/`, and
`lean/Sheaf`. Only the component Mathlib results
(`Ideal.IsIntegral.comap_lt_comap` and
`Ideal.isMaximal_comap_of_isIntegral_of_isMaximal'`) were found; no existing
declaration states this conjunction. The module therefore remains the single
declaration of this statement. No mismatch was found and no source or Lean file
required a change.
