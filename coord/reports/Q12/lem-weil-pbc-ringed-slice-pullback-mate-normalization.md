## Worker report

Item: lem-weil-pbc-ringed-slice-pullback-mate-normalization. Group: Q12.

The module `Sheaf.Paper.RingedSlicePullbackMateNormalization` states
`SheafOfModules.ringedSlicePullbackMateNormalization`, with proof `sorry`.
It also supplies the actual chain map `ringedSlicePullbackComplexMap`: its degree-n
component is the already defined `sliceModulePullbackMap` at `P.X n`. Its differential
compatibility is the symmetry of that natural transformation's naturality equation.
There is no new mathematical notion, chosen map, hollow definition, or auxiliary
postponed theorem. The node changes only in `lean`.

Hypothesis and clause correspondence:

- The small sites are `{D C : Type u} [SmallCategory D] [SmallCategory C]` and
  `{K : GrothendieckTopology D} {J : GrothendieckTopology C}`. This is the existing
  small-site/coefficient convention of the recorded slice-localization theorem.
- The continuous functor is `(u : D ⥤ C) [u.IsContinuous K J]`; its inverse image
  preserves finite limits by `[PreservesFiniteLimits (u.sheafPullback (Type u) K J)]`.
- The commutative coefficient sheaves are `R : Sheaf K CommRingCat.{u}` and
  `S : Sheaf J CommRingCat.{u}`. The structural map is represented by its adjunct
  `a : R ⟶ (u.sheafPushforwardContinuous CommRingCat.{u} K J).obj S`.
  This is precisely the presentation used by the recorded localization dependency;
  its sheaf adjunction identifies it with the node's `c : f⁻¹R ⟶ S`.
- The object is `V : D`, its image is `u.obj V`, and the local morphism is
  `Over.post (X := V) u` with `localizedRingedSiteMap u a V`. Local continuity is
  named as an instance, as in the dependency package; it is supplied by
  `localize_ringed_site_morphism_general`, so it excludes no global morphism.
  `K.over V`, `J.over (u.obj V)`, `R.over V`, and `S.over (u.obj V)` are the existing
  localized sites and rings; there is no private replacement.
- The global and local unbounded derived categories carry explicit
  `HasDerivedCategory.{w}` instances, and q is `DerivedCategory.Q.{w}`.
  `e` and `l : RingedSliceDerivedImage` name the recorded normalized global and
  local derived adjunction presentations. Their `left`, `right`, `epsilon`, `eta`,
  and `adjunction` fields are the actual derived functors, universal comparisons,
  and normalized adjunctions, including normalization on every chain map.
- The canonical comparisons are named by `d : RingedSliceAdjunctionSquare`.
  `d.beta` has orientation j_V* Rf_* → R(f_V)_* j_U*, and `d.lambda` has orientation
  L(f_V)* j_V* → j_U* Lf*, namely theta in this node. `hnormal` is verbatim the
  canonical right-derived normalization supplied by
  `ringedDerivedSliceLocalization`, retaining its termwise restriction factors.
  Naming that package and its defining normalization does not assume the desired
  representative equality or add a flatness hypothesis on f. It permits any
  normalized presentations and the specified canonical comparison between them.
- The complex `P` is arbitrary and unbounded. The two assumptions are exactly
  `P.IsKFlatIndependentCoefficients` and `∀ n : ℤ, (P.X n).IsFlat`.
  The first two conclusions assert K-flatness and flat terms for its actual
  `ringedSliceComplexRestriction K R V` restriction, as the parenthetical clause
  of the node requires. The independent K-flat predicate specializes to the live
  acyclic-total-tensor predicate by the existing
  `isKFlatIndependentCoefficients_iff_isKFlat`.
- `IsIso (e.epsilon.app P)` and `IsIso (l.epsilon.app (…restriction….obj P))`
  assert the two K-flat model identifications in the node. No arbitrary model
  isomorphisms are substituted for these universal comparisons.
- The equality is
  `theta(qP); j_U*(epsilon_P); restrictionFactor_(f*P) =
   L(f_V)*(restrictionFactor_P); epsilon_local_(j_V*P); q(sigma_P)`.
  Here `sigma_P` is `ringedSlicePullbackComplexMap u a V P`, whose degreewise
  components are exactly the canonical ordinary comparison of 04J0. This is
  precisely theta = q(sigma) under the four specified identifications, without
  treating the canonical factorization isomorphisms as definitional equalities.
- The consequent is recorded as the equality of natural transformations
  `(mateEquiv e.adjunction l.adjunction (TwoSquare.mk … d.lambda.hom)).natTrans =
  d.beta.hom`, followed by the formula for every derived object M saying that
  `d.beta.hom.app M` is the local transpose of
  `theta_(Rf_*M); j_U*(global counit_M)`.
  This last formula is the definition of the base change map in Stacks 07A7.
  Equality on the specified K-flat representatives, together with the recorded
  K-flat resolutions and naturality, identifies theta as the square's induced
  derived pullback comparison on every object; it is not just an invertibility claim.

Dependency declarations read and used (including the full signatures and docstrings):

- `Sheaf.CategoryTheory.SiteCoveringAxioms`: `Precoverage.IsSiteForCoverings`;
  its documented Grothendieck-topology/sheaf convention is inherited here.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous`:
  `SheafOfModules.overFunctor`, `over`, and the slice constructions;
  `Sheaf.Paper.LocalizeRingedSiteMorphismGeneral`:
  `localizedRingedSiteMap`, `ringedSiteModuleMap`,
  `localize_ringed_site_morphism_general`.
- `Sheaf.CategoryTheory.RingedSiteModules`: `ringedSiteModules` is transparently
  Mathlib `SheafOfModules`, the category used throughout the signature.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, `DerivedCategory.Q`.
- `Sheaf.CategoryTheory.RingedDerivedRestrictionGeneral`:
  `ringedDerivedRestrictionGeneral`, reused by the dependency's
  `ringedSliceRestriction` and `ringedSliceRestrictionFactors`.
- `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`:
  `CochainComplex.IsKFlatIndependentCoefficients` and its comparison with the live
  K-flat predicate; `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`:
  `exists_isKFlatResolutionIndependentCoefficients` (proof import).
- `Sheaf.Paper.RingedTopoiDerivedPullback`: `ringedTopoiDerivedPullback`
  (proof import); `Sheaf.Paper.RingedDerivedSliceLocalization`:
  `ringedDerivedSliceLocalization`, and its publicly imported
  `Sheaf.Paper.RingedDerivedSliceData` package, in particular
  `RingedSliceDerivedImage`, `RingedSliceAdjunctionSquare`,
  `ringedSliceRestriction`, `ringedSliceRestrictionFactors`, and
  `ringedSlicePushforwardComplexIso`.
- `Mathlib.CategoryTheory.Adjunction.Mates`: `mateEquiv` (the mathlib_match of
  def-weil-pbc-adjunction-mate); `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat`:
  `SheafOfModules.IsFlat` is exactness of tensoring with the sheafified tensor product.
- Additional recorded proof imports are
  `Sheaf.CategoryTheory.Sites.LocalizedModulePullbackComparison`,
  `Sheaf.Paper.RingedSliceDerivedAdjunction`,
  `Sheaf.Paper.RingedSliceDerivedComparisons`, and
  `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`.

Sources opened: sites-modules.tex, lemma-localize-morphism-ringed-sites (04J0);
sites-cohomology.tex, lemma-adjoint (07A6), remark-base-change (07A7), and
lemma-restrict-K-injective-to-open (08FI). The theorem docstring gives all seven
steps of the node's supplied proof, including the normalization at f*P without a
K-injectivity assumption and descent along inverted K-flat resolutions.

Edge cases checked before writing: an empty D has no V, so the localization
assertion is vacuous; an empty C cannot be the target of the stipulated u from a
nonempty D. Zero coefficient rings and the zero complex are allowed, with no
nonzero, boundedness, injectivity or flatness assumption on the structural map.
Restriction to any V, including terminal or identity cases, uses exactly the
same canonical maps. The complexes are indexed by all integers. Characteristic
is unrestricted. No independent site universe is forced equal to another by a
new interface: this is the recorded small-site convention, with an explicit
localization morphism universe w.

Searches performed with the prescribed msearch.py wrapper:

- LeanFinder: "Derived slice pullback comparison equals the localization of the
  ordinary module comparison on flat term K-flat complexes". Eight hits concern
  general derived comparisons/factorizations; none is this module-sheaf normalization.
- Loogle: "CategoryTheory.mateEquiv, NatTrans.mapHomologicalComplex". No hits;
  the search index reported the second name unknown. Direct Mathlib source reading
  found `NatTrans.mapHomologicalComplex` in Algebra/Homology/Additive.lean; it is
  a termwise construction, not the desired derived comparison theorem.
- Mathlib grep: "slice.*[Nn]ormal|mateOnRepresentative|sliceModulePullbackMap".
  No hits.
- LeanSearch: "For sheaves of modules on ringed sites the derived pullback slice
  comparison is the ordinary comparison on K-flat complexes and derived direct
  image comparison is its mate". Eight ordinary pullback/adjunction hits, no match.
- Project/upstream rg searches for the node id, slice/pullback combinations,
  mateOnRepresentative, and slice normalization: no public theorem matching the
  item. The existing `RingedSliceDerivedMate.lean` contains a **private** generic
  `mateOnRepresentative` and uses its specialized equality internally to prove
  invertibility. It does not export the node's representative normalization or
  base change identification; its public theorem states only invertibility.
  The canonical ordinary comparison itself is already public and is reused here.
- The exact node-id search in `dag/lean_names_upstream.json` found no attachment.

No statement correction, new node, dependency repair, or STATEMENT-DISPUTED issue.

## Second reading by Q12

Worker rereading, with the node and final module reopened; the maintainer supplies
the independent review requested by this dispatch (no additional agent was started).
I checked the direction of lambda against the node's theta, the two restriction
factorizations, and the exact ordinary inverse-mate components. The chain-map
constructor requires the symmetry of naturality and a complex-shape relation
argument; the initial compile exposed that constructor mismatch and it was fixed.
The theorem includes both model isomorphisms, preservation of flat-term K-flatness,
the equality of specified maps, and both the natural mate identity and its 07A7
counit-transpose formula. The canonical-normalization hypothesis is the existing
package's output, not the conclusion being assumed. No mathematical clause or
hypothesis changed on rereading.

Validation: prescribed scompile.py completed successfully for both the sandbox
module (39.5 s) and final library module name (48.0 s), without errors or warnings.
