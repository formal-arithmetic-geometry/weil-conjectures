## Worker report

The module defines and states `FieldTheory.exists_smooth_subalgebra_fraction_field`.
It formalizes the node's assertion for a finitely generated separable field extension
`K/k`: the hypotheses are `[Field k]`, `[Field K]`, `[Algebra k K]`,
`hfg : Algebra.FiniteType k K` (finite generation), and
`hsep : Algebra.IsSeparableExtension k K` (the recorded separability notion). The
conclusion chooses `B : Subalgebra k K`, rendering a `k`-subalgebra of `K`; the
conjunction's first clause is `Algebra.Smooth k B`, rendering smoothness of the
ring map `k → B`; its second clause says that for every `x : K` there are
`b b' : B` with `(b' : K) ≠ 0` and `x = (b : K) / (b' : K)`, exactly the stated
fraction-field condition. The ambient field makes `B` a domain and the displayed
quotient condition is the node's explicit meaning of fraction field.

Dependencies used are `Mathlib.Algebra.Algebra.Defs.Algebra` for the field-extension
convention (`[Field]` and `[Algebra]`), `Sheaf.FieldTheory.SeparableExtension`
(`Algebra.IsSeparableExtension`), and `Mathlib.RingTheory.Smooth.Basic`
(`Algebra.Smooth`). The latter is the recorded Mathlib declaration for the node's
smooth ring-map notion (formal smoothness plus finite presentation, equivalent to
the naive cotangent-complex formulation in the node).

Edge cases checked: `Algebra.FiniteType k K` allows zero generators (for example
`K = k`); the quantifier over `x : K` includes zero, whose denominator can still
be nonzero; no characteristic, nontriviality, or algebraic-extension hypothesis
was added; universes `u` and `v` are explicit and independent as for a field
extension.

Searches made: `msearch.py ... leanfinder` for “finitely generated separable field
extension fraction field smooth algebra” (returned only formal smoothness and
smooth-algebra descent results, no matching theorem); `msearch.py ... loogle`
for `IsFractionRing, Algebra.Smooth` (no hits); grep/rg in Mathlib and
`WeilConjectures` for smooth/fraction-field declarations (no theorem stating this
existence); and grep/rg in the project for the three dependency notions. The
recorded declarations above were read in full. No statement correction or
`STATEMENT-DISPUTED` applies.

## Earlier second reading (a previous round; superseded)

I reread the node and source place (Stacks Algebra Tag 037X). The field hypotheses and finite-generation and separability assumptions are rendered by the binders and the two named hypotheses. The existential `B : Subalgebra k K` is exactly the stated subalgebra. `Algebra.Smooth k B` renders the smooth map clause. The universal quotient clause includes every `x : K`, two elements of `B`, a nonzero denominator in `K`, and the equality. The zero element and the case `K = k` remain included.

## Second reading by C1

I opened the node, its Stacks source place, all three statement dependencies, and the
Lean file. The node's objects and hypotheses match as follows:

* The field extension $K/k$ is rendered by `{k : Type u} {K : Type v}` with
  `[Field k] [Field K] [Algebra k K]`; the two universes are independent, as the
  node permits.
* Finite generation is rendered by `hfg : Algebra.FiniteType k K`. This is the
  Mathlib finite-type algebra notion used for a finitely generated field extension.
* The node's separability notion is rendered by
  `hsep : Algebra.IsSeparableExtension k K`, the recorded declaration in
  `Sheaf.FieldTheory.SeparableExtension`, whose definition quantifies over every
  finitely generated intermediate field and is separably generated.
* The existential subalgebra is exactly `∃ B : Subalgebra k K`.
* The smooth map clause is `Algebra.Smooth k B`. The dependency record identifies
  this with the node's finite-presentation plus naive-cotangent-complex definition
  (formal smoothness and vanishing first cotangent homology).
* The fraction-field clause is exactly
  `∀ x : K, ∃ b b' : B, (b' : K) ≠ 0 ∧ x = (b : K) / (b' : K)`.
  Thus every element, including zero, has the required quotient. Since `B` is a
  subalgebra of the field `K`, the stated domain and localization consequences are
  represented by this explicit clause without adding a stronger conclusion.

No hypothesis or conclusion was added, dropped, strengthened, or weakened. The
source's assumptions at Tag 037X were checked against the node; no characteristic,
nontriviality, algebraicity, or Noetherian hypothesis is present. The empty finite
generating family and the case `K = k` remain allowed by `Algebra.FiniteType`; the
universal quantifier includes zero, and all characteristics are covered. The
independent universes `u` and `v` do not exclude an edge case.

I searched Mathlib and the slopmaster2 `WeilConjectures` tree with LeanSearch,
LeanFinder/Loogle, and `rg` for a theorem combining smoothness with a fraction-field
existence assertion; none exists. I also searched for the exact declaration name and
the three dependency notions. The dependency declarations were opened and match the
node, so no new definition or dependency module is needed. The module compiles with
`scompile.py`; its only proof is the required `sorry`. No mismatch was found and no
file was changed in the second reading.
