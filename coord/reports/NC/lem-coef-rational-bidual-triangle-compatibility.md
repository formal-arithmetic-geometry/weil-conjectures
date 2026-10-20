## Worker report

The delivery states `lem-coef-rational-bidual-triangle-compatibility` in
`Sheaf.CategoryTheory.CoefficientBidualTriangleCompatibility`, namespace
`CategoryTheory.CoefficientBidual`. The node's mathematical statement is unchanged.
The earlier `CoefficientBidualTriangles` module is withdrawn and empty; it is not
an existing match. There is no maintenance repair note for this item.

The declarations `compatibility`, `slice_compatibility`, `subcategory_linearity`,
and `scalar_compatibility` state the four parts of the node, with `sorry` proofs.
Their docstrings give the corresponding steps of the node's 13-step proof.
The other declarations are transparent constructions or predicates for these same
compatibilities. They introduce no alternative Hom, derived tensor, duality map,
localization, or distinguished-triangle convention.

Hypothesis and conclusion correspondence:

* A site small in the module universe is represented by `{C : Type c}`,
  `[Category.{v} C]`, `J : GrothendieckTopology C`, and coefficient/module universe
  `max c v r`. Object and arrow universes remain independent, including for a slice.
  The sheafification and locally-bijective instances supply the recorded abelian
  module category; `HasDerivedCategory.{w}` makes the chosen morphism universe
  explicit. These are construction/size parameters, not finiteness or geometric
  hypotheses. `R : Sheaf J CommRingCat.{max c v r}` is the node's sheaf O.
* `Modules` and `D` are the dependency's abbreviations for `SheafOfModules` and its
  unbounded `DerivedCategory`. There is no boundedness, perfection, or reflexivity
  hypothesis. `dual` fixes the second argument of the recorded
  `derivedInternalHomOfUniverses` at `ringedSiteDualityUnit`, exactly O[0]. `bidual`
  composes this contravariant functor twice using `Functor.rightOp`.
* `M : RingedSiteDualityModel J R` is the existing normalized representative model
  supplied without conditions on objects by `ringedSiteDualityMaps_exists`.
  `evaluation.app X` is literally `ringedSiteBidual M.closed M.symmetric O X`,
  the transpose of evaluation after Koszul symmetry. Its naturality field is the
  dependency's `ringedSiteBidual_naturality`, not a newly assumed naturality square.
* `signedShift` is minus the composite of Hom applied contravariantly to
  `(sourceShift X 1).hom` and `(sourceShift (dual X) (-1)).inv`. The dependency's
  `sourceShift` is normalized by its full ordinary Hom-product formula and fixed
  augmentation. Thus this is exactly chi = -s_{T(X),-1} T(s_{X,1})^{-1}; the leading
  minus is present. `compatibility` supplies a coherent `CommShift` structure whose
  degree-one component is this specific morphism. Coherence over Z then specifies
  the other integer shifts by iteration, inverse, and the zero-shift identity.
* `TriangleCompatibility F d` states `F.IsTriangulated`, `NatTrans.CommShift d Z`,
  and, for every distinguished triangle T, a morphism `T -> F.mapTriangle.obj T`
  with components exactly `d.app T.obj1`, `d.app T.obj2`, `d.app T.obj3` (with Lean's
  subscripted field names). A Mathlib triangle morphism includes all three squares;
  its third square is precisely `d_Z >> F(w) >> psi_V = w >> d_V[1]`.
* The same predicate includes, for every object and every integer n, the iff between
  invertibility of the component at X and at X[n]. It explicitly states all three
  two-out-of-three implications in distinguished triangles. These are conditional
  invertibility statements; arbitrary bidual maps are not claimed invertible.
* For every object `U : C`, the slice is `J.over U` with coefficient `R.over U`.
  `restriction` is the existing `localizedSystemRestriction R U`, followed by its
  exact `mapDerivedCategory`, with independent derived universe `w'`. Its shift
  comparison is inherited from this exact functor. No new restriction functor or
  sheaf category is chosen.
* `slice_compatibility` takes the normalized source and slice shift structures
  (the ones supplied by `compatibility`) and states that tensor/Hom restriction
  comparisons `t`, `h`, and coefficient comparison `o` exist and respect actual
  evaluation. `restrictionBidualIso` composes h twice, using the contravariance
  and coefficient transports explicitly, exactly as in
  `ringedSiteDualityMaps_restriction`. The natural isomorphism `beta` has these
  precise components, commutes with shifts, and satisfies
  `restriction.map d_X >> beta_X = d_slice(restriction X)`. The final equation
  writes the transported connecting square explicitly, including the shift
  comparison of restriction and the shift of beta. The first two squares follow
  from the component equality and naturality; thus the entire triangle morphism
  is transported. Exactness of restriction is inherited from `mapDerivedCategory`.
* The scalar ring in the node is `A : Type k` with `[CommRing A]`, to distinguish
  it from the coefficient sheaf R. A central coefficient action is encoded by
  `rho : A ->+* End O[0]`, `[Linear A D]`, and `hcentral`, which equates `a • id_X`
  to the tensor-unit action of `rho a` on every X. Endomorphisms of O[0] identify
  with endomorphisms of the ordinary coefficient sheaf, hence global coefficient
  sections. `coefficientScalar` writes this action with the normalized unit
  identification and right unitor. It is not an arbitrary action on bidual.
  This encoding includes any central action on O and requires its induced scalar
  action on D, exactly as in the node.
* `P : ObjectProperty D` and `[P.IsTriangulated]` give the full triangulated
  subcategory. Its linear structure is inherited from D. `hdual` says precisely
  that coefficient duality preserves P. `subcategoryBidual` uses `P.lift` and
  applies `hdual` twice; `subcategoryEvaluation` is the same actual map in that
  full subcategory. `subcategory_linearity` derives additivity and A-linearity
  from the central action, rather than assuming bidual is linear in place of
  proving that clause. The proof witnesses are Prop-valued and do not choose data.
* The scalar element `s : A` is unrestricted. The shifted full subcategory's
  A-linearity is the node's R-linear-shift hypothesis. The raw localized category
  is exactly `ScalarLocalization A P.FullSubcategory s`. The structure parameters
  in `scalar_compatibility`, together with `hshift`, `hQ`, and `htriangles`, are
  precisely the output of `exists_triangulated_scalarLocalization`: induced
  shift, identity-normalized localization comparison, exact Q, and distinguished
  triangles exactly the isomorphic images of distinguished triangles. Thus they
  specify the structures the statement says to equip this category with; none is
  an extra mathematical assumption. No idempotent completion is used.
* `scalar_compatibility` supplies the original restricted signed shift, normalized
  by its equation with the full-subcategory inclusion, and its triangle
  compatibilities. `ScalarCompatibility` uses the actual
  `ScalarLocalization.map A _ s F`; this base-changes `F.mapLinearMap`, so it sends
  `a tensor f` to `a tensor F(f)`. It supplies a natural transformation whose
  component at every localized object is exactly `Q.map d`. Its comparison equation
  with Q specifies the scalar extension of the original shift comparison for
  every integer n. `TriangleCompatibility` in the localized category includes all
  three squares on every distinguished triangle, not only on literal Q-images,
  and both shift closure and all three two-out-of-three implications.

Dependency declarations read and used:

* `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, `DerivedCategory.Q`, and their existing shift and
  triangulated structures (`def-weil-abstract-derived-category`).
* `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`,
  the abbreviation of `SheafOfModules`; `RingedHomUniverses.Modules` uses this
  same Mathlib category (`def-weil-sheaf-of-modules-category`).
* `Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses`:
  `CategoryTheory.derivedInternalHomOfUniverses`, with its complete signature,
  localization construction and representative-comparison docstrings read
  (`def-pur-derived-internal-hom`).
* `Mathlib.CategoryTheory.Triangulated.Pretriangulated`, `.Triangulated`, and
  `.Functor`: `Pretriangulated`, `IsTriangulated`, `Functor.IsTriangulated`,
  `Triangle`, and `TriangleMorphism` (`def-weil-triangulated-category`).
* `Sheaf.CategoryTheory.RingedSiteDualityMaps`: `RingedSiteDualityModel`,
  `ringedSiteDualityUnit`, `ringedSiteBidual`, `ringedSiteBidual_naturality`, and
  the full `ringedSiteDualityMaps_restriction` signature and normalization
  (`lem-sfb-ringed-site-duality-maps`).
* `Sheaf.Algebra.Homology.RingedInternalHomShiftOfUniverses`:
  `RingedHomUniverses.Modules`, `.D`, `.sourceShift`, `.LeftNormalization`,
  `.LeftFormula`, and `.leftShift_existsUnique`, with the full projection and
  augmentation normalizations (`lem-weil-pbc-ringed-internal-hom-exact-restriction`).
* `WeilConjectures.Mathlib.CategoryTheory.Triangulated.Functor`:
  `NatTrans.mapTriangle` and the three `NatTrans.isIso_app_obj...` lemmas, including
  their section variables and CommShift hypotheses
  (`lem-weil-pbc-commshift-nattrans-triangle-morphism`,
  `lem-sf-triangle-two-out-of-three`).
* `Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous`:
  `SheafOfModules.overFunctor`, `.over`, `.Hom.over`, `.overMap`, and
  `.overFunctorMap`; `Mathlib.CategoryTheory.Sites.Over`: `J.over` and `Sheaf.over`
  (`def-pur-localized-ringed-site`).
* `Sheaf.CategoryTheory.ScalarLocalization`: `ScalarLocalization`,
  `.localization`, `.map`, `.mapHom`, and their inherited linear structures;
  `.mapHom` is literal base change of the map on Hom modules
  (`def-weil-linear-scalar-localization`).
* `Sheaf.CategoryTheory.ScalarLocalizationTriangulated`:
  `ScalarLocalization.exists_triangulated_scalarLocalization`, including all
  nested structural witnesses, hshift, the HEq normalization, and the iff defining
  distinguished triangles (`lem-weil-linear-scalar-localization-triangulated`).
* `Sheaf.Algebra.Homology.SignedDoubleHomCone`:
  `SignedDoubleHomCone.comparison`, read with the explicit chi formula, cone-map
  naturality, inclusion identity and connecting-arrow identity
  (`lem-sf-double-hom-cone-comparison`). Its proof import is retained.
* `Sheaf.CategoryTheory.LocalizedModuleExactForSystems`:
  `SheafOfModules.localizedSystemRestriction` and its three existing exactness
  instance declarations (`lem-pur-site-restriction-module-adjunction-exact`). This
  already recorded proof dependency provides the exactness proofs used to apply
  mapDerivedCategory to the overFunctor recorded by def-pur-localized-ringed-site.
  Other recorded proof dependencies are imported without public for the proof plan.

Sources opened: `literature/stacks-project/sites-cohomology.tex`, the full text
and proofs of restriction of RHom, triangulated RHom, and internal-Hom evaluation
(Tags 08JB, 08JC, 0A97); the current blueprint's
`main-20261015/blueprint/sec-smooth-purity/sk-lem-sp-tower/lem-coef-rational-retract-evaluation`
statement and proof, especially the paragraph about site-perfect complexes;
the node's expanded 13-step signed-model proof. No source-based correction is needed.

Edge cases checked before and after writing:

* Zero complex and zero coefficient sheaf: all displayed maps and implications
  remain typed, with no nonzero or faithful-action assumption.
* Empty site and empty slice: chosen universes and exact restriction remain valid.
* O[0] and an unbounded complex: both use the recorded derived Hom, never ordinary
  Hom into O without the comparison hypotheses from the dependency.
* Characteristic two: the leading minus and Koszul signs collapse normally.
* Shifts 0, 1, -1 and arbitrary negative n: all are covered by coherent Z shifts.
* A nonreflexive infinite-dimensional vector space: nothing asserts its bidual
  map is invertible; only closure statements are made.
* s=0, s nilpotent, s=1, and the zero scalar ring: raw localization and all
  compatibilities are defined, without a nonzero or non-zero-divisor hypothesis.
* Triangles with fractional arrows: htriangles and the predicate quantify over
  every localized distinguished triangle, not a restricted family.
* Independent site object, morphism, coefficient, derived, slice-derived and
  scalar universes are explicitly bound; none is silently identified.

Searches made using the prescribed msearch wrapper and repository reads:

* LeanFinder: “The canonical evaluation double dual natural transformation on
  derived sheaves commutes with shifts and distinguished triangles” — eight
  results about generic CommShift/derived exact-functor comparisons, no exact match.
* Loogle: `CategoryTheory.NatTrans.CommShift, Functor.IsTriangulated` — no hits;
  unknown identifier for the latter query token.
* LeanSearch: “bidual natural transformation compatible with shifts derived
  category” — eight generic CommShift results, no coefficient-bidual theorem.
* msearch grep: `bidual|doubleDual`, `CategoryTheory/Triangulated` — no hits.
* rg in `lean/WeilConjectures` and `lean/Sheaf`: bidual/Bidual/doubleDual/DoubleDual
  and the item's id — the existing evaluation map and generic two-out-of-three
  lemmas supply ingredients, but no declaration states this node. The old
  CoefficientBidualTriangles module is empty. Perfect point biduality and
  invertible-dualizing-object transport have different hypotheses/conclusions.

No STATEMENT-DISPUTED flag. No new DAG nodes or dependency-module repairs.

## Second reading by NC

I reread the node, all direct dependency signatures, and the final module against
the correspondence above. This is the dispatcher's single-worker rereading;
the maintainer performs the independent delivery review. The substantive checks
were the direction of the contravariant source comparison, the leading minus in
chi, the connecting square's categorical composition order, the two contravariant
Hom transports in beta, actual exact slice restriction, and scalar balancing.
The original version nested all scalar triangulation witnesses in one concrete
derived-category signature; this was replaced by the same dependency-supplied
structural parameters and a general compatibility predicate to reduce elaboration.
The predicate still fixes all localized components, all integer-shift comparisons,
all triangle squares and every two-out-of-three case. The ring and category
hypotheses are accounted for above; none is a reflexivity assumption. No
mathematical statement correction was made.

Validation: the final module passed the prescribed scompile.py check in both
sandbox and library modes, without errors or warnings (12.7 s and 16.2 s,
respectively, under the unchanged 60-second per-file limit). All four theorem
proofs remain `sorry`; definitions contain actual data. The final code contains
no diagnostic commands, auto-implicit variables, local notation, private
helpers, or file-local instances. Every line is at most 100 characters.

Delivery gate diagnostic: the required direct dependency module
`Sheaf.CategoryTheory.RingedSiteDualityMaps` is rejected by
`tools/stage2_delivery.py:route_pivot_fails` because the unrelated dropped node
`def-per-ringed-site-bidual-transpose` has an `existing: true` alias into that same
module. The gate adds every module mentioned by any dropped node to its forbidden
module map; it does not distinguish such aliases from owning modules or account
for the retained dependency `lem-sfb-ringed-site-duality-maps`. Neither this item
nor that required dependency is on route-pivot-dropped.txt, and the module itself
is absent from route-pivot-dropped-modules.txt. Removing or hiding the import
would work around this ownership refusal while still using the same declarations;
copying the definitions would violate the one-definition rule. The launcher's
explicit instruction forbids patching or working around a wrong gate. No push
has occurred. The sandbox contains the compiling module, node record and report.
