## Worker report

The module `Sheaf.AlgebraicGeometry.GenericFibreFinitenessCriterion` states
`AlgebraicGeometry.generic_fibre_finiteness_criterion` with proof `sorry`.
It uses Mathlib's `IsNoetherian` scheme predicate, the two finite-type classes,
`irreducibleComponents`, `IsGenericPoint`, residue-field maps and `Module.Finite`,
open restrictions of scheme morphisms, `IsFinite`, and scheme-theoretic fibres.
No new definition node or dependency module is needed.

The hypotheses and clauses render the node as follows.

* `{X S : Scheme.{u}}` and `f : X ⟶ S` are the schemes and their morphism.
  `[IsNoetherian S]` is the Noetherian-scheme hypothesis; Mathlib documents it
  equivalently by a finite affine open cover with Noetherian section rings.
  `[LocallyOfFiniteType f]` and `[QuasiCompact f]` are exactly the two clauses
  of “of finite type”.
* `hdom` quantifies `C : Set X`, its component membership
  `C ∈ irreducibleComponents X`, and `x : X` with
  `IsGenericPoint x C`; its conclusion supplies a component `D : Set S` with
  `D ∈ irreducibleComponents S` and `IsGenericPoint (f x) D`.  This is precisely
  maximal dominance on every component generic point.
* The first side of the equivalence quantifies exactly the same `C` and `x`.
  The `letI := (f.residueFieldMap x).hom.toAlgebra` is the canonical field
  extension `κ(f(x)) → κ(x)`, and
  `Module.Finite (S.residueField (f x)) (X.residueField x)` says that extension
  is finite.  No separability, reducedness, or nonemptiness hypothesis is added.
* The second side chooses `V : S.Opens`; `Dense (V : Set S)` says that it is
  dense, and `IsFinite (f ∣_ V)` is the finite restriction
  `f⁻¹(V) → V`.
* The outer conjunction records the equivalence and the “under either condition”
  clause.  Its disjunction is either finite residue extension or a finite dense
  restriction.  The final universal quantifier ranges over every generic point
  `s` of every `D ∈ irreducibleComponents S`;
  `IsFinite (f.fiberToSpecResidueField s)` says that the fibre
  `X ×_S Spec κ(s)` is finite over `κ(s)`.

The dependency declarations used are:

* `def-pc-scheme`: `AlgebraicGeometry.Scheme` and `AlgebraicGeometry.Scheme.Hom`
  from `Mathlib.AlgebraicGeometry.Scheme`.
* `def-weil-pbc-noetherian-ring`: `IsNoetherianRing` from
  `Mathlib.RingTheory.Noetherian.Defs`, used through Mathlib's `IsNoetherian`
  scheme characterization.
* `def-weil-finite-type-morphism`: `AlgebraicGeometry.LocallyOfFiniteType` and
  `AlgebraicGeometry.QuasiCompact` from
  `Mathlib.AlgebraicGeometry.Morphisms.FiniteType` and `...QuasiCompact`.
* `def-weil-irreducible-components`: `irreducibleComponents` from
  `Mathlib.Topology.Irreducible`.
* `def-weil-residue-field`: `AlgebraicGeometry.Scheme.residueField` and
  `AlgebraicGeometry.Scheme.Hom.residueFieldMap` from
  `Mathlib.AlgebraicGeometry.ResidueField`.
* `def-pc-field-extension`: Mathlib's `Algebra` interface, instantiated here by
  the canonical residue-field map and tested by `Module.Finite`.
* `def-weil-finite-integral-morphism`: `AlgebraicGeometry.IsFinite` from
  `Mathlib.AlgebraicGeometry.Morphisms.Finite`.
* `def-pc-fibre-product`: `CategoryTheory.Limits.pullback` from
  `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`, used by the fibre.
* `def-weil-affine-spectrum`: `AlgebraicGeometry.Spec` from
  `Mathlib.AlgebraicGeometry.Scheme`, used by `fiberToSpecResidueField`.
* `def-sc-generic-point`: `IsGenericPoint` from `Mathlib.Topology.Sober`.
* `def-pc-scheme-fibre`: `AlgebraicGeometry.Scheme.Hom.fiber` and
  `fiberToSpecResidueField` from `Mathlib.AlgebraicGeometry.Fiber`.

Edge cases checked against the statement are empty `X` (the component
quantifiers are vacuous), empty `S` (the only dense open is empty), reducible
and disconnected schemes (all components are quantified separately), nilpotent
nonreduced schemes, inseparable finite residue extensions, open immersions, and
nonseparated morphisms.  The signature imposes no separatedness or reducedness.

Searches for an existing declaration were made as follows.

* `msearch.py ... leanfinder "finite generic residue field extensions equivalent to finite over a dense open for finite type morphisms of Noetherian schemes"`: hits `AlgebraicGeometry.IsFinite`, `Algebra.QuasiFinite` and residue-field finiteness lemmas, but no criterion with these hypotheses.
* `msearch.py ... loogle "AlgebraicGeometry.IsFinite, Module.Finite, IsNoetherian, irreducibleComponents"`: zero hits for the combined criterion.
* `msearch.py ... grep "generic.*finiteness|finite.*generic|residueField.*Module.Finite" Mathlib/AlgebraicGeometry`: no matching declaration.
* `rg` over `WeilConjectures` and `lean/Sheaf` found only the separate generic-finiteness neighbourhood theorem and unrelated generic-fibre results; no declaration states this equivalence.

There is no `STATEMENT-DISPUTED` marker and no node fault.  The module compiles
cleanly with `scompile.py`; the only proof placeholder is the required `sorry`.

## Second reading by NV

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
