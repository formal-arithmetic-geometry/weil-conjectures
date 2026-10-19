## Worker report

The module `lean/Sheaf/RingTheory/QuasiRegularNoetherianLocal.lean` states the
node as `RingTheory.Sequence.quasiRegularNoetherianLocal`; its proof is exactly
`by sorry`.  The canonical map is the existing
`Ideal.regularSequenceGradedPolynomialMap` from
`Sheaf.RingTheory.RegularSequenceGradedPolynomial`, so no private helper or
duplicate definition is introduced.

The statement correspondence is as follows.  The commutative ring is
`{A : Type u} [CommRing A]`; the local, nonzero ring is `[IsLocalRing A]`, which
supplies the unique maximal ideal `IsLocalRing.maximalIdeal A` and
nontriviality; Noetherianity is `[IsNoetherianRing A]`.  The finite ordered
family is `(b : ℕ) (f : Fin b → A)`, and the maximal-ideal condition is
`hf : ∀ j, f j ∈ IsLocalRing.maximalIdeal A`.  Its generated ideal is
`Ideal.span (Set.range f)`, its quotient is
`A ⧸ Ideal.span (Set.range f)`, and the associated graded ring is
`Ideal.associatedGraded (Ideal.span (Set.range f))`.  The polynomial algebra
map is `Ideal.regularSequenceGradedPolynomialMap f`, whose variables map to
the degree-one classes of `f j` and whose constants use the canonical quotient
algebra map.  `hiso : Function.Bijective ...` expresses that this canonical
graded algebra map is an isomorphism.  The conclusion is
`RingTheory.Sequence.IsRegular A (List.ofFn f)`, including both weak
regularity and the nonzero final quotient clause.

The source is Stacks Project, Algebra, Tags 061P and 061S.  Its proof is
represented in the theorem docstring: containment in the maximal/Jacobson
radical and cyclic prefix quotients; truncation to every prefix quotient;
Krull intersection to obtain nonzero initial forms; injectivity of the next
polynomial variable transported through the graded map; and the regular
sequence criterion, including the empty sequence.

Recorded dependencies read were `Ideal.associatedGraded` and its algebra
structure from `WeilConjectures.RingTheory.AssociatedGradedRing`,
`MvPolynomial` from Mathlib, `IsNoetherianRing`, and
`RingTheory.Sequence.IsRegular`; the polynomial-map theorem module is
`Sheaf.RingTheory.RegularSequenceGradedPolynomial`.

Edge cases checked: `b = 0` gives `Fin 0`, the zero-variable polynomial ring,
`J = 0`, and the empty regular sequence on the nonzero ring; the zero ring is
excluded by `IsLocalRing`; fields (zero maximal ideal), arbitrary
characteristic, zero or repeated generators, and zero divisors are allowed as
inputs, with a noninjective canonical map correctly failing the hypothesis.
There are no independent test-object universes or finiteness assumptions.

Searches for an existing whole statement or duplicate notion were made with
LeanFinder, Loogle, LeanSearch, and direct `rg` over Mathlib,
`WeilConjectures`, and `lean/Sheaf`; the searches are recorded in
`searches.jsonl`.  They found only regular-sequence infrastructure and the
Mathlib TODO for quasi-regular sequences, not this criterion.  The existing
canonical polynomial map was found and reused.

## Second reading by Q35

I independently read the node, Stacks `algebra.tex` Tags 061P and 061S, the
current module, and each recorded dependency declaration.  The source's
specialization from a nonzero finite module `M` to `M = A` is exact: `A` is
cyclic over itself, and `[IsLocalRing A]` supplies the required nontriviality.
The hypotheses match item by item: commutative `A`; local nonzero structure;
Noetherianity; `b : ℕ`; ordered `f : Fin b → A`; membership in the unique
maximal ideal; and no domain, field, characteristic, or dimension assumption.

`Ideal.span (Set.range f)` is the same generated ideal as the ordered list
`List.ofFn f`.  The quotient coefficient ring and
`Ideal.associatedGradedAlgebra` are the dependency constructions.  The map
`Ideal.regularSequenceGradedPolynomialMap f` is the existing canonical
`MvPolynomial.aeval` map sending each variable to the degree-one quotient
class; it has no regularity hypothesis and no arbitrary coefficient map.
Because it is this canonical degree-preserving map, bijectivity is equivalent
to the stated graded algebra isomorphism.  The conclusion uses Mathlib's
`RingTheory.Sequence.IsRegular` on exactly the ordered list, with both its
successive nonzerodivisor and final nonvanishing conditions.

No mismatch was found and no statement correction was needed.  In particular,
the prior duplicate helper declaration is absent: the module imports and uses
the landed canonical map directly.  All variables and the universe are bound,
there is no file-local notation or instance, and the only postponed proof is
the owning theorem.  Edge cases `b = 0`, the zero ring exclusion, fields,
arbitrary characteristic, repeated/zero generators, and empty polynomial
variables all agree with the node.  The cited search results report no exact
Mathlib or project match.
