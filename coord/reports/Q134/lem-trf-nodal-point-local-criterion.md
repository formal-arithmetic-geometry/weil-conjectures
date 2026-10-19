## Worker report

The module `Sheaf.AlgebraicGeometry.NodalPointLocalCriterion` states
`AlgebraicGeometry.nodalPoint_iff_separable_lci_firstFitting` with one postponed proof.
There are no new definitions, dependency repairs, or statement corrections.

Source read: `literature/stacks-project/curves.tex`, lemma-nodal (0C4D),
lemma-nodal-lci (0C4E), and lemma-fitting-ideal (0C4C). The statement is the
pointwise combination of the depth-one Fitting criterion with the LCI comparison.
The nine-step proof of the node is included in the theorem docstring. Its four
currently unstated formal-local proof dependencies have no modules to import;
all recorded proof dependencies are available through the explicit imports.

Hypothesis and clause correspondence:

- The field is `{k : Type u} [Field k]`; the scheme is `{C : Scheme.{u}}`.
  The given structure morphism `f : C ⟶ Spec (.of k)` is the one used by the
  recorded Fitting and base-change interfaces. `[LocallyOfFiniteType f]` is
  exactly locally finite type, with no quasi-compactness or separatedness added.
- Equidimensional dimension one is `hpure : C.IsPureDimension 1`.
- The point and its closedness are `(x : C) (hx : x ∈ closedPoints C)`.
- The algebraic closure is an arbitrary fixed `(Ω : Type u) [Field Ω]
  [Algebra k Ω] [IsAlgClosure k Ω]`. Fixing any algebraic closure expresses
  the node's chosen algebraic closure; no assumption of separability of Ω/k
  is imposed, so imperfect fields and positive characteristic remain included.
- The left side quantifies over a point `y` of the actual scheme pullback
  `C ×_Spec k Spec Ω`. The equality involving `pullback.fst` says it lies over x.
- The completion is `AdicCompletion (IsLocalRing.maximalIdeal ...) ...` of
  precisely the geometric local stalk. `Nonempty (... ≃+* ...)` says there
  exists a ring isomorphism, as in the node; it imposes no coefficient-linearity
  or chosen presentation. The target is `MvPowerSeries (Fin 2) Ω` modulo
  `Ideal.span {MvPowerSeries.X 0 * MvPowerSeries.X 1}`.
- The right side's first conjunct `(f.residueFieldAlgebraMap x).Finite` says
  κ(x) is finite-dimensional over k via the canonical embedding; the second
  conjunct is `Algebra.IsSeparable k (C.residueField x)` explicitly given that
  same map's algebra structure. This includes algebraicity by the recorded
  definition of separability and imposes exactly the finite separable condition.
- `∃ (U : C.affineOpens) (hxU : x ∈ U.1)` is the affine open neighbourhood.
  Its coordinate algebra S is `Γ(C, U.1)`; the affine-open property supplies
  U = Spec S canonically. The algebra structure is written explicitly using
  `(f.appLE ⊤ U.1 le_top).hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom`, so it
  is the structure induced by f rather than an arbitrary algebra structure.
- The witness `hfg : Algebra.FiniteType k Γ(C, U.1)` is the node's finite
  generation, not an extra global finite-type condition on C.
  `Algebra.IsLocalCompleteIntersection k Γ(C, U.1)` uses precisely the
  existing definition, with that same algebra structure and hfg.
- The last clause maps `(Scheme.firstFittingIdealSheaf f).ideal U` along
  `C.presheaf.germ U.1 x hxU` and equates it to the maximal ideal of the stalk.
  This is exactly the explicit equivalent version in the node. In particular
  it forces x to belong to the singular subscheme: a maximal ideal is proper.
  It expresses equality via the residue map, rather than an abstract ring
  isomorphism that could accidentally identify a different quotient with κ(x).

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`.
- `Sheaf.AlgebraicGeometry.FirstFittingSingularSubscheme`:
  `Scheme.firstFittingIdealSheaf` (and the defining affine characterization),
  the ideal cutting out `Scheme.firstFittingSingularSubscheme`.
- `Sheaf.RingTheory.CompleteIntersectionOverField`:
  `Algebra.IsLocalCompleteIntersection` and its global-CI definition.
- `Mathlib.AlgebraicGeometry.ResidueField`: `Scheme.residueField` and
  `Scheme.Hom.residueFieldMap`; the canonical base-field embedding is the
  existing `Scheme.Hom.residueFieldAlgebraMap` in `WeilConjectures.ZetaSeries`.
- `Sheaf.AlgebraicGeometry.NodalGeometricFibres`: `HasNodalGeometricFibres`.
  The pointwise completion subcondition is expanded, since applying the whole
  predicate would add nonempty connected fibre and morphism hypotheses absent
  here. The exact ring model, completion, and ring-isomorphism encoding are used.
- `WeilConjectures.AlgebraicGeometry.Modules.Differentials`:
  `Scheme.Hom.relativeDifferentials`, used by the Fitting ideal construction.
- `Sheaf.AlgebraicGeometry.PureDimension`: `Scheme.IsPureDimension`.
- `Mathlib.Topology.JacobsonSpace`: `closedPoints`.
- `Mathlib.FieldTheory.IsAlgClosed.Basic`: `IsAlgClosure`.
- `WeilConjectures.AlgebraicGeometry.BaseChangeConventions`: the recorded
  scheme-base-change convention is `Limits.pullback`, with `pullback.fst` as
  the map to C. Its current published source was read using `scompile.py --source`.
- `Mathlib.RingTheory.AdicCompletion.Basic` / `.Algebra`: `AdicCompletion`.
- `Mathlib.RingTheory.MvPowerSeries.Basic`: `MvPowerSeries`, `MvPowerSeries.X`.
- `Mathlib.FieldTheory.Separable`: `Algebra.IsSeparable`.

Edge cases checked mathematically before writing:

- The empty scheme has pure dimension one vacuously but has no x, so there is
  no unintended nonemptiness assumption.
- A smooth point of the affine line has first Fitting ideal equal to the unit
  ideal, not the maximal ideal; both sides are false.
- The ordinary node uv has Fitting ideal (u,v), is an LCI, and satisfies both
  sides. Its discriminant is one even in characteristic two.
- Cusps and doubled lines do not have the required maximal Fitting stalk ideal;
  LCI alone is not enough. No reducedness is assumed separately.
- A finite purely inseparable residue field is excluded by the explicit
  separability conjunct; the formal geometric condition detects its thickening.
- The scheme need only be locally finite type; arbitrary disjoint unions of
  curves are admitted. The universe u is shared by schemes, k, and geometric
  test fields, as in the recorded nodal-geometric-fibres interface.

Searches for an existing statement:

- `msearch.py ... leanfinder` with “Nodal closed point of a curve characterized
  by separable residue field local complete intersection and first Fitting
  ideal equal to the maximal ideal”: eight hits, including
  `Algebra.isUnramifiedAt_iff_map_eq`, `Algebra.FormallyUnramified.iff_map_maximalIdeal_eq`,
  `Algebra.IsSmoothAt`, and `WeierstrassCurve.IsGoodReduction`; no nodal criterion.
- `msearch.py ... loogle 'AdicCompletion, RingEquiv'`: zero hits.
- `msearch.py ... leansearch` with “node on a curve if and only if separable
  residue field local complete intersection Fitting ideal”: eight hits about
  unramifiedness, separability and residue fields; no equivalent statement.
- `msearch.py ... grep 'nodal|Nodal|firstFitting' AlgebraicGeometry`: zero hits.
- `rg` over upstream `WeilConjectures` and shared `lean/Sheaf` for
  `nodal|Nodal|firstFitting|lem-trf-nodal-point-local-criterion` finds the
  definitions and family geometry users, but no pointwise equivalence.
- `rg` of `dag/lean_names_upstream.json`, upstream and side sources for
  `nodalPoint_iff|nodal_point_iff` finds no collision.

Validation: every variable and universe is explicitly bound. The initial compiler
failure was category inference at the geometric point binder; adding
`(C := Scheme.{u})` fixes that without changing the statement. No node fault or
STATEMENT-DISPUTED issue was found.

## Second reading by Q134

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
