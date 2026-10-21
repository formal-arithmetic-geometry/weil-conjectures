## Worker report

The module `Sheaf.AlgebraicGeometry.ComparisonEtaleSliceAbelianPullback` states
`AlgebraicGeometry.ProEtale.comparison_etaleSlice_abelian_pullback`, with one
postponed proof and no new definitions. The node's mathematical statement is
unchanged. The statement dependencies now cite the definition owners requested in return L
at aee04b74d8e3; there is no statement correction, disputed statement, or
dependency module. One new definition node records existing comparison data.

Source read: `literature/stacks-project/sites.tex`, definition-localize (00Y0),
its ensuing sectionwise restriction formula, and lemma-localize-given-products
(03CE), including its proof. Also read `proetale.tex`, section-morphism (09A5),
including the comparison inverse-image equality before lemma-morphism-comparison.
The quasi-compact and quasi-separated assumptions of that following lemma concern
direct images, and are not assumptions of the inverse-image square used here.

Hypothesis and clause correspondence:

- A scheme X is `(X : Scheme.{u})`; an arbitrary etale object v:W→X is
  `(W : X.Etale)`, with scheme `W.left`, morphism `W.hom`, and etaleness `W.prop`.
  No monomorphism, quasi-compactness, separation or coefficient finiteness is added.
- The common larger universe is `u + 1`: both sites retain schemes in universe u,
  objects in u+1 and morphisms in u; coefficients are `AddCommGrpCat.{u + 1}`.
  There is no equation identifying the object and morphism universes.
- The first conjunct gives `e : Over W ≌ W.left.Etale`. Its inverse composed
  with `Over.forget W` equals `MorphismProperty.Over.map ⊤ W.prop`, so it sends
  each scheme and arrow to its original composite over X. The additional HEq
  specifies its arrow to W as the object's structure morphism, ruling out a
  different slice realization. `e.inverse.IsDenseSubsite` says a sieve covers
  precisely when its image covers. With an equivalence of categories this is
  exactly an equivalence of sites, not an extra topological hypothesis.
- The second conjunct uses the already constructed
  `Scheme.ProEt.sliceEquiv X ((Scheme.toProEt X).obj W)`. Its inverse composes
  weakly etale objects with W.hom, retaining the structure arrow and all maps.
  `IsDenseSubsite` states the same preservation and reflection of coverings for
  the pro-etale slice. The existing functors have the concrete scheme-and-arrow
  formulas, as read in `ProEtaleWeaklyEtaleLocalization.lean`.
- An arbitrary abelian F is the universally quantified
  `F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}` in the component equation;
  both F and every pro-etale abelian G are also arguments of the canonical
  natural isomorphisms of functors: the explicit
  `Etale.upperStarIsoLocalizationRestriction` and `C.sheafIso`. The latter is
  part of `C : Scheme.ProEtaleObjectRestrictionComparison
  ((Scheme.toProEt X).obj W) AddCommGrpCat.{u + 1}`. Thus the restriction
  identifications are natural in sheaves and normalized, rather than arbitrary
  objectwise isomorphisms.
- The restrictions F|W and G|W are the existing
  `Etale.localizationRestriction AddCommGrpCat W.hom W.prop` and
  `ProEtale.localizationRestriction AddCommGrpCat W.hom ...`. Their definitions
  are sheaf pushforward by `MorphismProperty.Over.map`, i.e. precomposition on
  underlying presheaves with the opposite composition functor. Consequently
  their values at T→W are exactly F(T→W→X) and G(T→W→X), and their maps are the
  original restriction homomorphisms. This is definitional, including on sheaf
  morphisms; no substitute restriction construction was made.
- The explicitly written `Etale.upperStarIsoLocalizationRestriction
  AddCommGrpCat.{u + 1} W.hom W.prop` has source the recorded `Etale.upperStar`
  and target F|W. It is defined by uniqueness of left adjoints to the same
  direct image, using the localization adjunction. `C.sheafIso` has source the
  recorded `Scheme.proEtaleSheafInverseImage` and target G|W. The fields
  `C.coprojection` and `C.sheafIso_inv` pin it to the distinguished Kan
  coprojections followed by the sheafification unit. They therefore concern
  the geometric inverse images induced by v, with their canonical
  normalizations. No separate existential `rhoE` or `rhoP` remains.
- `comparisonUpperStar AddCommGrpCat X` and its W counterpart are the existing
  abelian comparison inverse images, given by the same sheafified left Kan
  construction as `Scheme.proEtaleSiteComparison` on sets.
- `tau` is a natural isomorphism from comparison inverse image followed by
  pro-etale restriction to etale restriction followed by comparison inverse
  image on W. Its component equation specifies exactly the three-factor
  composite of node proof step 4: `(C.sheafIso.app ...).symm`, the inverse of
  `supportSiteComparisonCoefficientPullbackIso ... W.hom`, then `mapIso` of the component
  of the explicit `Etale.upperStarIsoLocalizationRestriction`. All factors
  are actual abelian-sheaf isomorphisms. The existential C carries the Kan
  coprojection and sheafification-unit equations; it does not permit twisting
  the restriction identification by an arbitrary natural automorphism.
  This expresses the canonical comparison square under the two restriction
  identifications.

Recorded dependency interfaces used and read:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and its morphisms.
- `Mathlib.AlgebraicGeometry.Sites.Etale`: `Scheme.Etale`,
  `Scheme.smallEtaleTopology`, and its jointly surjective covering formula.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt`, `ProEt.topology`.
- `Sheaf.AlgebraicGeometry.ProEtaleSiteComparison`:
  `Scheme.proEtaleSiteComparison`, implemented using the existing
  `WeilConjectures.SixFunctors.ProEtale.Comparison.Defs` constructions;
  this module's `comparisonUpperStar` is their abelian specialization.
- `Mathlib.CategoryTheory.Sites.Over`: `GrothendieckTopology.over` and
  `overPullback` (the localization declarations also listed by
  def-pur-localized-ringed-site). The node's module-only module-sheaf material
  is unnecessary here; the actual abelian localization uses these declarations.
- `Sheaf.CategoryTheory.SiteCoveringAxioms`: imported as the recorded
  def-weil-pbc-sites-and-cohomology module; abelian sheaves use its retained
  Mathlib `Sheaf` convention, not a new site or sheaf definition.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`: `Etale.upperStar`;
  `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`:
  `Scheme.proEtaleSheafInverseImage`.
- Proof interfaces: Mathlib etale composition and `Etale.of_comp`;
  `Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization`:
  `Scheme.ProEt.sliceEquiv`, `sliceDense`, `weaklyEtale_localization`;
  `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`:
  `Etale.upperStarIsoLocalizationRestriction`;
  `Sheaf.AlgebraicGeometry.ProEtaleObjectInverseImageRestriction`:
  `Scheme.ProEtaleObjectRestrictionComparison` and
  `Scheme.proEtaleObjectInverseImageRestriction` (abelian clause);
  `Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence`:
  `supportSiteComparison_pullback_coherent`, and its canonical
  `supportSiteComparisonCoefficientPullbackIso`, owned by the existing definition
  node `def-per-site-comparison-pullback-data`.
  The pro-etale localizationRestriction comes from
  `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs`;
  despite that module path, this declaration has arbitrary Grothendieck abelian
  coefficients, not a finite coefficient restriction.

Edge cases checked mathematically: the identity etale object gives the usual
identity localization; the empty object and empty base are included without a
nonemptiness hypothesis; zero abelian sheaves are included. A non-monomorphic
etale morphism (e.g. two disjoint copies of X mapping to X) is allowed: the
inverse-image/restriction adjunctions do not need the monomorphism assumptions
used only by lower shriek elsewhere in the imported modules. No auxiliary ring
is introduced in the statement; proof step 2 may instantiate the localization
node's irrelevant ring with the integers. The comparison source of 09A5 imposes
no quasi-compactness on this inverse-image square.

Searches made before writing:

- `msearch.py ... leanfinder "Abelian etale proetale comparison inverse image
  commutes with restriction to an etale slice"`: eight hits, including
  `Scheme.restrictFunctorΓ_inv_app` and scheme open restriction isomorphisms;
  none states the two site identifications and abelian comparison on a slice.
- `msearch.py ... loogle "CategoryTheory.GrothendieckTopology.overPullback,
  CategoryTheory.Sheaf"`: seven hits, including generic `overPullback`, open
  subspace restriction equivalences and sheaf local isomorphism tests; no match.
- `msearch.py ... grep "comparisonUpperStar|upperStarIsoLocalizationRestriction|
  overPullback" CategoryTheory/Sites`: nine hits in Over, SheafHom and
  LocalProperties; generic restriction infrastructure, no scheme comparison.
- `rg` of `lean/WeilConjectures` for comparisonUpperStar, comparisonPullback,
  localizationRestriction and slice comparison: found the generic comparison
  square and restriction primitives reused above. Searching for this node id
  returned no declaration. `rg` of `lean/Sheaf` found the recorded comparison,
  localization and inverse-image modules but no statement of this aggregate.
- A final name search across Mathlib, WeilConjectures and Sheaf found no existing
  `comparison_etaleSlice_abelian_pullback` or abelian etale-slice equivalent.

Validation: `scompile.py NF lem-pe-comparison-etale-slice-abelian-pullback` compiled
both its sandbox check and actual module successfully (3.6s and 3.0s), with no
warnings or errors. The initial check identified private imports of constants
used in the public signature; those imports were made public before the clean
check. The only new theorem has `sorry` as its entire proof; the docstring gives
all four DAG proof steps and the declarations they use.

## Repair of return L (immutable head aee04b74d8e3)

1. H2 / comparison definition: replaced the statement dependency
`lem-weil-pbc-comparison-pullback` by the landed definition node
`def-per-site-comparison-pullback-data`. The statement now uses exactly
`supportSiteComparisonCoefficientPullbackIso AddCommGrpCat.{u + 1} W.hom`.
I read its complete signature and adjunction-mate construction at
SupportComparisonPullbackCoherence.lean:214–228. It gives the same canonical
comparison on abelian coefficients, with the same direction and normalization.
The theorem node remains in proof_deps and proof step 4.

2. H2 / restriction data: replaced the statement dependency
`lem-sfb-proetale-object-inverse-image-restriction` by the new definition node
`def-pe-proetale-object-restriction-comparison-data`. It records existing:true
on Sheaf.AlgebraicGeometry.ProEtaleObjectInverseImageRestriction, owning both
Scheme.ProEtaleObjectRestrictionComparison and
Scheme.proEtaleObjectInverseImageIndexPoint. I read both definitions in full
(lines 38–86), including all five structure fields. The theorem node remains
in proof_deps and proof step 3, where existence of these data is used.

The two genuinely theorem-dependent statement dependencies remain:
lem-weil-pbc-etale-inverse-image-restriction supplies the canonical etale
identification, and lem-weil-proetale-weakly-etale-localization supplies
weaklyEtale_slice used by sliceEquiv. The theorem proof remains exactly sorry.
The saved packet passed the initial dry run, but its old stmt_deps still
contained the two plain-definition faults, so those were repaired explicitly.
Comparison against the current shared node confirms that all non-lean changes
to the item are these authorized statement-dependency additions. Its statement,
proof and proof_deps are unchanged. No source-based correction is needed.

## New nodes

`def-pe-proetale-object-restriction-comparison-data` defines the distinguished
index point and the type of canonical restriction comparison data, using the
existing project declarations without copying them. Stacks 00Y0 and 03CE give
restriction and its base-change description. The Kan coprojection and actual
sheafification-unit formulas come from the existing inverse-image interface
and the comparison structure, as used in proof steps 3–4. The definition does
not assert existence. Its parameters are exactly X, W and a value category D
with the structure's stated universe, colimit and sheafification assumptions.
The distinguished point is the composition/base-change adjunction unit; its
underlying chosen pullback orders the variable factor first. The five fields
are presheafIso, coprojection, sheafification_isIso, sheafIso and sheafIso_inv,
respectively. Thus no arbitrary automorphism can replace the canonical factor.

New-node searches: LeanSearch for canonical proetale restriction comparison
data returned eight generic sheafification/equivalence hits; LeanFinder for
the inverse-image restriction comparison with Kan coprojections returned eight
generic presheaf/sheafification hits; msearch grep of AlgebraicGeometry/Sites
for the structure, index point and localizationRestriction returned zero hits.
The full queries and returned names are preserved in mathlib_searches. Direct
rg over WeilConjectures found neither declaration; Sheaf found the existing
definitions reused here. DAG grep found them owned only as helpers of theorem
lem-sfb-proetale-object-inverse-image-restriction, and mentioned by theorem
lem-coef-infinity-small-colimit-generation, with no definition-node owner.
blueprint_refs.py search ProEtaleObjectRestrictionComparison found zero nodes;
ancestor gives sk-prop-sf-comparison. Identity, empty and non-monomorphic site
objects are allowed by these data definitions; no finite ring is introduced.

## Repair self-check

Reread the final node, Lean signature and both definition-owner interfaces.
The arbitrary scheme and etale object, concrete slice equivalence clauses,
sectionwise restrictions, common u+1 coefficients and canonical rhoE/rhoP
normalizations remain as in the accepted H3 repair. The only signature change
is the specified supportSite comparison name. Its component still lies between
the inverse of C.sheafIso and comparisonUpperStar.mapIso of the etale factor.
The new node is a type definition with no existence assertion; the consumer's
existential C remains the theorem's conclusion, with its original normalization.
Both theorem nodes removed from stmt_deps remain in proof_deps unchanged.

Final repair validation: scompile.py compiled the sandbox check in 4.8 s and
the delivered module in 4.2 s, with no diagnostics. The saved initial packet's
dry run also passed before repair. The final signature matches lean.statement
verbatim, every Lean line is at most 100 characters, every universe and variable
is explicit, and the theorem proof remains exactly sorry. The current shared
node differs only in lean and the four authorized additions to stmt_deps;
statement, proof, proof_deps and all other fields are preserved.

## Second reading by NF

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
