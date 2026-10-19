## Worker report

The module `Sheaf.AlgebraicGeometry.Curve.SeparablyClosedAlgebraicClosure` states
`AlgebraicGeometry.Etale.cohomology_invariance_of_isSepClosed_algebraicClosure`.
It uses the existing Mathlib/source notions for fields, separably and algebraically
closed fields, algebraic extensions, schemes, pullbacks, universal homeomorphisms,
small étale sheaves, inverse image, and étale cohomology.  The two real helper
constructions are the canonical pullback maps
`AlgebraicGeometry.algebraicClosurePullbackToClosure` and
`AlgebraicGeometry.algebraicClosurePullbackToExtension`; they are included in the
node's `lean.declarations` and have source/blueprint docstrings.

The binders `{k k' kbar kbar'}` and their `[Field]`, `[IsSepClosed]`,
`[IsAlgClosed]`, `[Algebra.IsAlgebraic]`, `[Algebra]`, and `[IsScalarTower]`
instances render the two separably closed fields and chosen algebraic closures.
`e : kbar →ₐ[k] kbar'`, `h_e`, and `h_tower` render the compatible inclusion of
closures and its compatibility with the maps from `k` and `k'`.  The scheme map
`f : C ⟶ Spec (.of k)` renders the `k`-scheme structure, and `F` is exactly an
abelian sheaf `Sheaf C.smallEtaleTopology AddCommGrpCat.{u + 1}`.

The first conclusion is
`IsUniversalHomeomorphism (pullback.fst f (Spec.map (CommRingCat.ofHom
(algebraMap k kbar))))`, rendering that the projection
`u : C_kbar ⟶ C` is a universal homeomorphism.  The second conclusion quantifies
`q : ℕ` and states `Function.Bijective (cohomologyMap u F q)`, rendering the
isomorphism on every étale cohomology group.  The final conclusion quantifies
`q` and `x : Sheaf.H F q` and equates the two pullback composites.  Each path is
written with `cohomologyMap`, and the canonical `upperStarComp` comparison is
applied before comparing the two maps.  The compatibility equation `h_comp` is
the explicit equality of the two scheme composites to `C`; `cast` transports the
right path along this equality so the displayed equation has one common target.
Thus the square is stated for the actual maps
`C_kbar' → C_kbar`, `C_kbar' → C_k'`, `C_kbar → C`, and `C_k' → C`.

Dependency declarations used:

* `def-pc-separably-closed`: Mathlib `IsSepClosed` from
  `Mathlib.FieldTheory.IsSepClosed`.
* `def-weil-algebraic-closure`: Mathlib `IsAlgClosed` and
  `Algebra.IsAlgebraic` from `Mathlib.FieldTheory.IsAlgClosed.Basic`.
* `def-weil-scheme-over-base`: Mathlib `AlgebraicGeometry.Scheme.Over` and
  the `Scheme`/`Spec` declarations.
* `def-pc-base-change`: `CategoryTheory.Limits.pullback` and its projections,
  imported through `WeilConjectures.AlgebraicGeometry.BaseChangeConventions`.
* `def-weil-universal-homeomorphism`: source
  `AlgebraicGeometry.IsUniversalHomeomorphism` in
  `WeilConjectures.AlgebraicGeometry.Morphisms.UniversalHomeomorphism`.
* `def-weil-pbc-etale-site` and `def-weil-pbc-abelian-etale-sheaves`: Mathlib
  `Scheme.smallEtaleTopology` and `CategoryTheory.Sheaf`.
* `def-weil-pbc-inverse-image`: source `AlgebraicGeometry.Etale.upperStar` in
  `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`.
* `def-weil-pbc-etale-cohomology`: source `AlgebraicGeometry.Etale.cohomology`
  and `CategoryTheory.Sheaf.H` in the étale derived/global-sections modules.
* `def-weil-pbc-cohomology-pullback`: source
  `AlgebraicGeometry.Etale.cohomologyMap` in
  `WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance`.

Edge cases checked: `q = 0` is included because `q : ℕ` is unrestricted; the
zero sheaf and the empty scheme are allowed by the unrestricted `F` and `C`
binders; an already algebraically closed separably closed field is covered by
choosing its algebraic closure and identity-compatible `e`; characteristic zero
is included because no characteristic hypothesis is imposed; and no finiteness,
properness, curve, torsion, or nonemptiness hypothesis was added.

Searches made:

* `msearch.py Q14 det-curve-invariance-inseparable-closure grep
  "universal homeomorphism|IsUniversalHomeomorphism|purely inseparable"`:
  no match in Mathlib/AlgebraicGeometry.
* `msearch.py ... leansfinder` for an algebraic-closure universal-homeomorphism
  and étale-cohomology statement: only unrelated field/étale declarations.
* `msearch.py ... loogle "IsUniversalHomeomorphism, cohomologyMap,
  IsPurelyInseparable"`: unknown `IsUniversalHomeomorphism`; no match.
* `msearch.py ... leansfinder` for functorial étale pullback: only unrelated
  scheme pullback declarations.
* `rg` over `WeilConjectures/` found the existing generic declarations
  `IsUniversalHomeomorphism`, `Etale.cohomologyMap_bijective`, and
  `Etale.cohomologyMap`; no declaration of this node's algebraic-closure passage.
* `grep -R det-curve-invariance-inseparable-closure WeilConjectures`: no match.

No new DAG nodes or dependency modules were needed; every statement dependency
has a usable Mathlib or source declaration.  The theorem proof is intentionally
`sorry` as required for stage 2.

## New nodes

None.

## Dependency modules

None.

## Second reading by Q14

I reread the node statement, the blueprint node and proof, and every recorded
statement dependency.  The field, closure, scheme, sheaf, universal-homeomorphism,
cohomology, and pullback-map hypotheses are all present in the signature.  The
first conclusion is the universal-homeomorphism clause, the second is bijectivity
for every degree, and the third is the compatible-closures square with the
`upperStarComp` identifications and the explicit equality of the two composites.
The module compiled cleanly with `scompile.py`; no statement or dependency field
was changed in the node copy.
