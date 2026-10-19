## Worker report

The module `lean/Sheaf/AlgebraicGeometry/OpenComparisonTensorNormalization.lean` defines the
canonical tensor comparisons for the comparison inverse image and for restriction to an open,
defines the two projection formula maps by the specified adjunction transposes, and states
`AlgebraicGeometry.ProEtale.openComparison_tensor_normalization` with proof `sorry`.
The module uses the fixed ordinary constant coefficient category
`Sheaf (T.smallEtaleTopology) (ModuleCat A)` and
`Sheaf (Scheme.ProEt.topology T) (ModuleCat A)` with
`A : Type (u + 1)`, `[CommRing A]`, and `[Finite A]`.

The helper `comparisonTensorIso` is `asIso (Functor.OplaxMonoidal.δ C V W)` for
`C = comparisonUpperStar (ModuleCat A) T`, so it is the inverse-image tensor map
`t^T_{V,W}` with the source and target in the item.  The helpers
`etaleRestrictionTensorIso` and `proEtaleRestrictionTensorIso` transport the canonical
oplax tensor map for `j^*` along the recorded localization isomorphisms; these are the
restriction tensor maps used to define the two transposes.

For the item statement, `j : U ⟶ X` and `[IsOpenImmersion j]` are the open immersion, and
`F` and `B` are respectively the arbitrary etale `A`-module sheaves on `U` and `X`.
The etale map `openComparisonEtaleKappa A j F B` is the inverse of the
`Etale.openImmersionLowerShriekAdjunction` Hom equivalence applied to
`(eta_F ⊗ 1) ≫ rho^e.inv`, exactly the defining transpose of `κ^e_{F,B}`.
The pro-etale map `openComparisonProEtaleKappa A j G H` is defined by the analogous
`openImmersionLowerShriekAdjunction` Hom equivalence and `rho^d.inv`, exactly `κ^d`.

The first conjunct of the theorem is the displayed equality.  Its left side is rendered by
`openComparisonTensorLeft`: `C_X.map κ^e`, followed by the canonical `t^X` and then
`c_F ⊗ 1`.  Its right side is rendered by `openComparisonTensorRight`: `c_{F⊗rB}`,
then `d` applied to `(1 ⊗ a_B) ∘ t^U`, and finally `κ^d`.  Thus both maps have source
`C_X e(F ⊗ rB)` and target `d C_U F ⊗ C_X B`.
The second conjunct states naturality in both variables: for `f : F ⟶ F'` and
`b : B ⟶ B'`, the source map is `C_X.map (e.map (f ⊗ r.map b))` and the target map is
`d.map (C_U.map f) ⊗ C_X.map b`, with the usual commuting-square equality for the left
composite.  The first conjunct identifies that natural family with the right composite as
well.

Dependency declarations used are:

* `AlgebraicGeometry.IsOpenImmersion` (Mathlib, `AlgebraicGeometry.OpenImmersion`).
* `CategoryTheory.ringedSiteModules` from
  `Sheaf.CategoryTheory.RingedSiteModules` for the general module-sheaf category.
* `AlgebraicGeometry.Scheme.proEtaleSiteComparison` and its module specialization from
  `Sheaf.AlgebraicGeometry.ProEtaleSiteComparison`.
* `AlgebraicGeometry.Etale.openImmersionLowerShriek` and
  `AlgebraicGeometry.Etale.openImmersionLowerShriekAdjunction` from the recorded etale
  extension-by-zero module, and
  `AlgebraicGeometry.Scheme.sfIntrinsicExtensionByZero` from
  `Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZero`.
* `AlgebraicGeometry.ProEtale.supportSiteComparisonCoefficientPullbackIso` and
  `openComparisonRestrictionIso` from
  `Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence` and
  `Sheaf.AlgebraicGeometry.OpenComparisonUnitNormalization`.
* `AlgebraicGeometry.ProEtale.openImmersionLowerShriekComparisonUpperStarIso` from
  `Sheaf.AlgebraicGeometry.ProEtaleExtensionZeroComparison`.
* `SheafOfModules.siteSheafTensorRight` and its functoriality from
  `Sheaf.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctoriality`, and the recorded
  `SheafOfModules.module_pullback_tensor_iso` interface from
  `Sheaf.CategoryTheory.ModulePullbackTensorIso`.

I checked the edge cases `j = 𝟙 X`, an empty open scheme `U`, zero sheaves `F = 0` or
`B = 0`, and the zero coefficient ring.  The definitions use only categorical units,
zero objects, and canonical isomorphisms, so no nonzero or conservativity assumption is
introduced.  Identity and empty opens are covered by the existing open comparison and
localization isomorphisms.

Searches for an existing exact declaration were made with:

* `msearch.py Q115 lem-sf-open-comparison-tensor-normalization leanfinder "tensor compatibility of the etale pro-etale open-extension comparison"`: eight hits, all generic etale algebra or Kähler differential declarations; no site-comparison theorem.
* `msearch.py ... loogle "Functor.OplaxMonoidal.δ, openImmersionLowerShriekComparisonUpperStarIso"`: zero hits (Loogle reports the names as unavailable in its index).
* `msearch.py ... grep "openComparison|extension.*tensor|tensor.*extension" Mathlib/AlgebraicGeometry`: zero exact hits.
* `rg` over `/home/ubuntu/weil-src-slopmaster2/WeilConjectures`: only generic tensor and extension declarations; no `openComparison_tensor_normalization`.
* `rg` over `lean/Sheaf`: no prior declaration with this item name; the relevant hits are the generic monoidal comparison and tensor interfaces used above.
* `grep -rl '"lem-sf-open-comparison-tensor-normalization"' dag/nodes`: the item itself and
  `lem-weil-finite-compact-projection-formula`; the latter cites this item as a proof dependency
  and remains valid because the delivered statement is unchanged.

No `STATEMENT-DISPUTED` issue or node fault was found.

## Second reading by Q115

I reread the node, its complete proof text, and the complete module.  The open immersion,
finite commutative coefficient ring, both module variables, the two canonical comparison
isomorphisms, the two adjunction transposes, the tensor comparisons, the displayed equality,
and simultaneous naturality are all present.  The composition directions agree with the
node: the left composite is `C_X(κ^e)` then `t^X` then `c_F ⊗ 1`, while the right composite
is `c_{F⊗rB}` then `d((1⊗a_B) ∘ t^U)` then `κ^d`.  No hypotheses were added or dropped,
and the helper tensor maps are canonical transports of the monoidal inverse-image maps.
The file compiles cleanly with `scompile.py`; the only postponed proof is the named theorem.


## Maintainer independent review and mechanical fixes

Reviewed immutable delivery 1b3ac72bc70232fa2d390b1aa6a0adfef9fcdc71 against the
item node, all nine statement dependencies, their recorded declarations, Stacks
proetale.tex Tag 09AF and sites-modules.tex Tags 03DI/03EL. The two composites and
simultaneous naturality state exactly the node. The fixed-scalar sheaf presentation
uses the same ordinary constant-ring modules and extension functors as the recorded
unit-normalization dependency, through the canonical realization equivalences;
no condensed coefficients or geometric-stalk substitute is used.

Mechanical repairs: H8, add literal source/blueprint docstrings to both composite
helpers and the required blueprint syntax to the other helpers and module;
expand the theorem docstring into all six proof steps with dependency ids.
H9, remove the local monoidal/braided instance attributes and use the already
available canonical instances. Add ordinary proof imports for the recorded
localization, restriction adjunction, constant-ring comparison, algebraic tensor
comparison, and pure-tensor calculus. No definition body, theorem signature,
node statement, or dependency record is changed.

Independent searches: LeanSearch for preservation of the open tensor adjunction
mate under etale/pro-etale comparison returned generic module adjunctions and
scheme-module restriction, not this statement; Loogle for
CategoryTheory.Adjunction.homEquiv returned the general Hom equivalence and its
construction lemmas. rg searches for openComparison, comparison tensor iso,
projectionFormula and projection_formula in Mathlib, WeilConjectures and lean/Sheaf
found the imported canonical constructions but no existing exact theorem.
The nearby derived open-projection transport and pro-etale-only base-change tensor
normalization have different inputs and conclusions.

The immutable original and final replacement each passed the prescribed scompile.py
per-file check with exit status 0 and no errors or warnings. The final replacement
compiled as sandbox Sheaf/Stage2/Sandbox0.lean in 3.3 s and as library
Sheaf/AlgebraicGeometry/OpenComparisonTensorNormalization.lean in 3.3 s, with a
60-second per-file limit. The installed wrapper on 2026-10-17 uses the server side
overlay (nt_srv_compile.py --wire-confirm), rather than the earlier local wrapper;
no direct SSH command, global build, or live Lean edit was performed.
The node lean.statement remains verbatim equal to the final theorem signature.
All eight declarations remain recorded; the only theorem proof remains sorry.
Identity and empty opens, empty X, zero sheaves, the zero ring and arbitrary
characteristic remain covered; no extra universe equality or nontriviality is assumed.
