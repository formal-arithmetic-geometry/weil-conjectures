## Worker report

The module `Sheaf.AlgebraicGeometry.ProjectiveStablePointedLevelParameter` states
`AlgebraicGeometry.exists_projective_stable_pointed_level_parameter`. Its only theorem
has proof `sorry`; there are no new definitions or auxiliary postponed theorems.
The natural-language statement and proof plan are unchanged. The only additional
statement dependency is the already landed `def-sfb-stable-pointed-curve`, whose
canonical predicate renders the stable-family conditions already written inline
in the item. The previous worker's observation about an already reviewed split
concerned stage 1: the live item has no Lean binding and does need its stage-2 statement.

Clause-by-clause correspondence:

* `k : Type u` with `[Field k]` is the arbitrary field. `g n : ℕ` gives the
  nonnegative integer genus and marking number, and `hg : 2 ≤ g` is the only
  genus restriction. There is no restriction on characteristic or on the field
  having rational level structures.
* `∃ M, ∃ a : M ⟶ Spec (.of k)` is a scheme with its specified k-structure.
  `LocallyOfFiniteType a ∧ QuasiCompact a` is finite type, and `IsHProjective a`
  is the node's finite-projective-space embedding convention for M.
* `∃ U, ∃ f : U ⟶ M, ∃ t : Fin n → (M ⟶ U), ∃ ht` is an actual family with
  ordered sections; `ht` states each section equation. These are actual schemes
  and maps, with no arbitrary existence choice substituted for a construction.
* In (a), `B`, `b : B ⟶ Spec (.of k)`, `m : B ⟶ M`, and `m ≫ a = b`
  range over every k-scheme and k-morphism. `pullback.snd f m` is the pulled-back
  family and `f.baseChangeSection (t i) (ht i) m` its ith section. The named
  `baseChangeSection_snd` supplies its section equation. `IsStablePointedCurve`
  is precisely the landed predicate, not a duplicate: projective-bundle
  projectivity, flatness, finite presentation (projective morphisms supply
  quasi-compactness and quasi-separatedness), connected nonempty nodal geometric
  fibres, reduced pure dimension one, disjoint sections in the smooth locus,
  and the genus-zero/genus-one inequalities on component normalizations.
  Its component maps and genera use the existing reduced normalization and
  arithmetic genus. Its nodality uses the completed geometric-local-ring model
  in the existing `HasNodalGeometricFibres` definition. All of these conditions
  are imposed by the predicate, rather than assumed as extra input hypotheses.
* In (b), `F : Type u`, `[Field F]`, `[Algebra k F]` give every field extension.
  `C` and `[C.Over (Spec (.of F))]` give its specified structural map.
  `Smooth`, `IsHProjective`, `GeometricallyIntegral`,
  `topologicalKrullDim C = 1`, and `C.arithmeticGenus F = g` give exactly the
  smooth projective geometrically integral curve of the specified genus.
  `p : Fin n → (Spec (.of F) ⟶ C)`, `hp`, and `Function.Injective p`
  say the markings are distinct F-rational sections with their given order.
* `P`, `r : P ⟶ Spec (.of F)`, `Nonempty P ∧ IsFinite r ∧ Etale r`
  are the required nonempty finite etale F-scheme. Nonempty concerns the
  underlying space, not the existence of an F-rational point.
* Functorial representability is expressed in its equivalent universal-element
  form. `mP` is a k-map by its equation with `a`, `r`, and `Spec.map (algebraMap k F)`.
  `eP` is an isomorphism between the two pulled-back families over P. Its equation
  with `pullback.snd` says it is over P; the indexed section equations preserve
  every label. This is the universal element of the pair functor.
* For every F-scheme `(B,b)`, every k-map `m`, and every isomorphism `e` over B
  satisfying the identical label equations, `∃! q : B ⟶ P` gives its unique
  classifying map. The equation `q ≫ r = b` says it is an F-morphism and
  `q ≫ mP = m` identifies the parameter component of the pair. The two
  equations for `v` specify the unique canonical map
  `U ×_M B → U ×_M P` associated to q. The final equation identifies e with
  pullback of eP after projection to C. Their B-projections already agree by
  the over-B conditions. Since the two projections of `C ×_F B` are jointly
  monic, this is exactly equality of the full isomorphisms.

Why the last clause is natural representability, not just pointwise existence:
for each F-morphism q, pull back the universal pair to obtain a pair over B.
The pullback map v exists uniquely by the fibre-product universal property.
The stated uniqueness and existence of q make this operation bijective.
For any F-map B' → B, pulling the universal pair back along its composite
with q is the pullback of the pair classified by q. Uniqueness therefore
makes the bijections commute with every change of test scheme. Conversely,
a natural representing bijection supplies `(mP,eP)` from the identity of P
and supplies exactly these unique q and projection equations. No additional
condition on the pair functor is imposed, and no quotient by Aut(C) or by
permutations is taken.

Dependency declarations read and used:

* `Sheaf.AlgebraicGeometry.StablePointedCurve`:
  `AlgebraicGeometry.IsStablePointedCurve`, together with its
  `Scheme.normalizedComponentMap` and `Scheme.normalizedComponentGenus`.
* `Sheaf.AlgebraicGeometry.ProjectiveBundleMorphism`:
  `AlgebraicGeometry.IsProjectiveBundle`, through the stable predicate.
* `WeilConjectures.AlgebraicGeometry.Morphisms.Projective`:
  `AlgebraicGeometry.IsHProjective` (the canonical upstream declaration).
* `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`;
  `Mathlib.Algebra.Field.Defs`: `Field`; `Mathlib.Algebra.Algebra.Defs`: `Algebra`.
* `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`;
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`: `QuasiCompact`;
  `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `Smooth`;
  `Mathlib.AlgebraicGeometry.Geometrically.Integral`: `GeometricallyIntegral`;
  `Mathlib.AlgebraicGeometry.Morphisms.Finite`: `IsFinite`;
  `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `Etale`.
* `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`:
  `pullback`, `pullback.fst`, `pullback.snd`, and their universal property;
  `WeilConjectures.AlgebraicGeometry.DeformationSpace.BaseChangeSection`:
  `Scheme.Hom.baseChangeSection`, `Scheme.Hom.baseChangeSection_snd`.
* `WeilConjectures.AlgebraicGeometry.Cohomology.EulerChar`:
  `Scheme.arithmeticGenus`; `Mathlib.Topology.KrullDimension`: `topologicalKrullDim`.
* Within the stable predicate, `Flat` and `LocallyOfFinitePresentation` are the
  dependency classes in Mathlib's morphism modules;
  `Sheaf.AlgebraicGeometry.ReducedNormalization` supplies the canonical component
  construction. Completion and the two-variable power-series ring are reused
  through the stable predicate's nodal-fibre dependency, with Mathlib's
  `AdicCompletion` and `MvPowerSeries`.

Every currently stated proof-dependency module is imported plainly. The five
moduli/level/universal-curve proof prerequisites have no recorded Lean modules;
none is needed to type the present statement. They remain its proof dependencies,
with the complete six-step proof plan in the theorem docstring. They are not
replaced by assumptions. No dependency module repair is needed.

Edge cases checked before writing: n = 0 gives Fin 0 and vacuous marking
conditions throughout, while g ≥ 2 remains. n = 1 and n = 2 are unrestricted.
The empty B is included in both clauses, as are disconnected or nonreduced test
schemes. M is not required to be smooth. C is nonempty from geometric
integrality and dimension one. P is required to be nonempty, but never to have
an F-point. All characteristics and non-algebraically-closed fields are allowed.
No component of the level cover is selected. The single arbitrary universe u
is the project's scheme/field size convention, including field extensions and
all test schemes of that size. All variables are explicitly bound and
`autoImplicit` is false.

Searches made with msearch.py, all for this item:

* LeanFinder: "A projective scheme carrying a stable pointed curve whose isomorphism
  functor over a fixed smooth pointed curve is represented by a finite etale scheme".
  Eight results concerning schemes, etale morphisms and over categories; no match.
* Loogle: "AlgebraicGeometry.IsStablePointedCurve, AlgebraicGeometry.IsHProjective".
  No results; Mathlib's index does not contain the project's stable-curve predicate.
* Mathlib grep: "stable.*pointed|StablePointed|levelStructure|level_structure" in
  AlgebraicGeometry. No results.
* LeanSearch: "There exists a projective parameter scheme of stable pointed curves
  and finite etale schemes representing isomorphisms with fixed smooth marked curves".
  Eight results about schemes, etale maps and smoothness; no level-parameter theorem.
* rg over `lean/WeilConjectures` and `lean/Sheaf` for stable-curve names found the
  existing StablePointedCurve and StablePointedGenericExtension modules. The former
  is reused; the latter consumes this result in its proof plan. Neither states it.
  A search for the item id in upstream WeilConjectures had no result. A further
  search for projective stable pointed level parameters and the proposed declaration
  name found only the generic-extension proof-plan reference.

Read the primary publisher PDF of de Jong (1996), §2.24 and §4.17,
https://www.numdam.org/item/PMIHES_1996__83__51_0.pdf, confirming the level cover,
projective normalization, universal family and finite etale smooth-locus assertion.
The already reviewed DAG proof explicitly supplies the extension from the printed
n ≥ 3 version to g ≥ 2 with every n ≥ 0; the Lean statement retains that full scope.

Validation: scompile.py compiled this file both as a sandbox module and at its
library module path against the live published build (2.3 s and 2.9 s), with no
errors or unexpected warnings. No statement dispute or correction is needed.

## Second reading by NF

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
