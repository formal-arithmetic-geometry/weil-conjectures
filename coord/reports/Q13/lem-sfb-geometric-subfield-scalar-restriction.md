## Worker report

The module `Sheaf.FieldTheory.GeometricSubfieldScalarRestriction` states
`Algebra.geometric_subfield_scalar_restriction`, with its proof postponed by `sorry`.
It introduces no definitions, instances, or extra theorems. Only the item's `lean`
record changes; there are no statement corrections, new nodes, or dependency repairs.

The node-to-Lean correspondence is as follows.

- Four fields: `(k₀ : Type u) (k : Type v) (E : Type w) (F : Type x)` with their four
  `Field` instances, using the Mathlib notion recorded on `def-weil-field`.
- The inclusions `k₀ ⊆ k ⊆ E` are `[Algebra k₀ k] [Algebra k E] [Algebra k₀ E]`
  and `[IsScalarTower k₀ k E]`. Field algebra maps are injective. The scalar tower
  says that the composite inclusion equals the supplied `k₀ → E` inclusion.
- The inclusions `k₀ ⊆ F ⊆ E` are `[Algebra k₀ F] [Algebra F E]` and
  `[IsScalarTower k₀ F E]`, using the same `k₀ → E` structure. There is no
  `Algebra k F` or `Algebra F k` assumption.
- Separable algebraicity of `k/k₀` is `[Algebra.IsSeparable k₀ k]`, exactly the
  dependency's recorded declaration. Its `isAlgebraic` instance supplies algebraicity;
  no finite-degree assumption is made.
- Algebraicity of `E/F` is `[Algebra.IsAlgebraic F E]`, meaning that each element
  satisfies some nonzero polynomial over `F`, with no degree bound or separability.
- Geometric reducedness over `k` is the binder `hgeom`, quantifying over every field
  `K` with `[Algebra k K]` and requiring `IsReduced (E ⊗[k] K)`.
- The first conclusion quantifies over every field `L` with `[Algebra k₀ L]` and
  requires both `IsReduced (E ⊗[k₀] L)` and `IsReduced (F ⊗[k₀] L)`.
- The first transcendence-degree equality is
  `Cardinal.lift.{w} (Algebra.trdeg k₀ F) =
  Cardinal.lift.{x} (Algebra.trdeg k₀ E)`. Both sides are in `Cardinal.{max w x}`.
  The second equality is `Algebra.trdeg k₀ E = Algebra.trdeg k E`, whose sides already
  lie in the same universe. These express precisely the node's chain of equalities.
- The tensor multiplication is Mathlib's usual commutative algebra multiplication
  from `Mathlib.RingTheory.TensorProduct.Basic`; `IsReduced` means that every nilpotent
  is zero. No geometric integrality, finite generation, finite dimension, or group
  action is assumed.

All universes are explicit: `u v w x t`. Both test-field quantifiers use
`Type (max u v w x t)`, a common universe at least as large as every field in the
statement. The independent `t` allows arbitrarily large tests, and smaller test fields
can be lifted into this common universe. Thus the quantifier cannot become vacuous
by choosing a universe too small for an embedding of the base field. No universe
identification between the four fields is imposed. `Cardinal.lift` retains infinite
transcendence degrees and compares different universes without cardinal cancellation.

Dependency declarations read and used:

- `Mathlib.Algebra.Field.Defs`: `Field` (`def-weil-field`).
- `Mathlib.Algebra.Algebra.Defs`: `Algebra` and its `algebraMap`
  (`def-pc-field-extension`).
- `Mathlib.FieldTheory.Separable`: `Algebra.IsSeparable`, whose docstring and
  `Algebra.IsSeparable.isAlgebraic` instance explicitly include algebraicity
  (`def-weil-pbc-separable-algebraic-extension`).
- `Mathlib.RingTheory.AlgebraicIndependent.Basic`: `Algebra.trdeg`
  (`def-kun-transcendence-degree`).

The available proof dependencies are imported privately:
`Sheaf.RingTheory.GeometricReducednessSeparableScalarRestriction` supplies
`Algebra.forall_isReduced_tensorProduct_iff_of_isSeparable`;
`Mathlib.RingTheory.Flat.Basic` supplies `Module.Flat.of_free` and
`Module.Flat.lTensor_preserves_injective_linearMap` (with
`Module.Free.of_divisionRing` from `Mathlib.LinearAlgebra.Basis.VectorSpace`);
`Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis` supplies
`lift_trdeg_add_eq`/`trdeg_add_eq`, and
`Mathlib.RingTheory.AlgebraicIndependent.Transcendental` supplies `trdeg_eq_zero_iff`.
The theorem docstring gives all three proof steps, including tensor-factor swaps.

Sources read: local Stacks `algebra.tex`,
`lemma-geometrically-reduced-over-separable-algebraic` (Tag 0C2Y),
`lemma-subalgebra-separable` clause (1) and the tensor-injectivity observation after
`lemma-geometrically-reduced-permanence`; `fields.tex`,
`lemma-transcendence-degree-tower` (Tag 030H). These support the existing node exactly.

Edge cases checked before writing: identity extensions; transcendence degree zero;
infinite algebraic `k/k₀` and `E/F`; infinite transcendence degree (the tower proof adds
zero, never cancels an infinite cardinal); positive characteristic; and incomparable
middle fields, for example `k₀ = ℚ`, `k = ℚ(√2)`, `F = ℚ(t)`,
`E = ℚ(√2,t)`. The field assumptions exclude a zero ring exactly as the node does.
There is no finite type or finite degree requirement that would exclude any of these.
The two tower instances are essential compatibility data, not additional mathematical
restrictions on inclusions into one field. No STATEMENT-DISPUTED or node fault was found.

Searches for existing declarations (all performed before writing):

- `msearch.py leanfinder`: "Geometric reducedness descends to subfields after restriction
  along a separable algebraic field extension and transcendence degrees agree in an
  algebraic field diamond". Eight hits included `Algebra.IsGeometricallyReduced`,
  `.of_injective`, `.of_forall_fg`, and field inseparable-degree lemmas; no full match.
- `msearch.py loogle`: `"GeometricallyReduced", "IsAlgebraic"`. One hit,
  `Algebra.instIsReducedTensorProductOfIsAlgebraicOfIsGeometricallyReduced`, concerns
  a tensor base change along an algebraic extension, not this field diamond.
- `msearch.py grep` in `RingTheory`:
  `GeometricallyReduced|trdeg_eq_of_isAlgebraic|lift_trdeg_add_eq`. Seven hits give
  the geometric-reducedness notion and transcendence-degree tower lemmas, not the item.
- `msearch.py leansearch`: "Geometric reducedness under separable algebraic restriction
  of scalars and subfield descent with equal transcendence degrees". Eight hits give
  geometric-reducedness definitions and separate facts; no full matching declaration.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for geometric scalar/subfield terms,
  `GeometricallyReduced`, and algebraic transcendence-degree comparisons found the
  scalar-restriction proof dependency and `InvariantSeparatingParameters`, plus
  unrelated geometric scheme/coefficient material. The invariant-parameter theorem
  imposes finite generation, finite action, and geometric integrality and asserts
  parameter existence; it is not this lemma. A narrower search in their FieldTheory
  and RingTheory directories and `dag/lean_names_upstream.json` found no conflict
  with `Algebra.geometric_subfield_scalar_restriction`.
- `grep -rn 'lem-sfb-geometric-subfield-scalar-restriction' lean/WeilConjectures`
  found no upstream declaration for this node.

## Second reading by Q13

A separate in-thread rereading of the node, the Lean file, and the source was performed;
no second agent was started, as required by the dispatcher brief. This is a self-review,
not an independent-worker review; the maintainer's independent delivery review remains.
The rereading checked each of the four field structures, all five algebra structures,
and the two compatibility towers against the diamond. It checked that separability
already includes algebraicity, that only `E/F` is assumed algebraic, and that neither
middle-field inclusion is present. It checked both reducedness clauses under the same
arbitrary extension-field quantifier and both transcendence-degree equalities. The first
equality's lifts land in the same universe; the second equality needs no lift because
both top fields are `E`. The test-field universe includes all four fields and an arbitrary
extra universe. The concrete incomparable-middle-field example above is included, and
no finite-generation or domain assumption slipped in. No mismatch was found and no
statement or dependency change was needed. The module has one named theorem with
`sorry`, a complete three-step proof docstring, and no definitions or hidden proof data.
