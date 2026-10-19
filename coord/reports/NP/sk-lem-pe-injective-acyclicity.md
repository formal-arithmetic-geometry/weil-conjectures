## Worker report

The delivery states `sk-lem-pe-injective-acyclicity` in
`Sheaf.AlgebraicGeometry.ProEtaleRingedComparisonInjectiveAcyclicity` as
`AlgebraicGeometry.Scheme.isZero_homology_comparisonRingedModuleDirectImage_of_injective`.
The item's JSON differs only in `lean`. Its statement, statement dependencies,
proof, proof dependencies, status and Q11 stage-1 review are preserved.
The earlier “item's node file is unchanged” failure concerned another stage-1
split; this delivery supplies the previously absent stage-2 binding.

The coefficient ring and module categories are intrinsic ringed-site modules.
In particular, the delivery does not specialize to finite rings and does not
assume the underlying abelian sheaf of an injective module is injective.
There is exactly one postponed theorem, the main declaration, with proof `sorry`.
All helper definitions have real data. The two instances are constructed data
for continuity and sectionwise additivity; neither contains `sorry`.

### Hypothesis and clause audit

| Node hypothesis or clause | Exact Lean rendering |
| --- | --- |
| An arbitrary scheme X | `(X : Scheme.{u})`, with explicit `universe u` |
| An arbitrary discrete commutative ring Lambda | `(Λ : Type (u + 1)) [CommRing Λ]`; discreteness means constant coefficients, realized by `constantSheaf`, rather than a continuous-function coefficient system. There is no finiteness, nontriviality, characteristic or torsion assumption. |
| Small etale site | `X.Etale` and `X.smallEtaleTopology`, the recorded Mathlib site |
| Small pro-etale site | `X.ProEt` and `Scheme.ProEt.topology X`, the recorded Mathlib site |
| The comparison geometric morphism | The recorded `Scheme.toProEt X`; ring inverse image and its unit use `Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (toProEt X) RingCat.{u + 1} X.smallEtaleTopology (ProEt.topology X)` |
| Constant etale ring sheaf | `comparisonEtaleRing X Λ` is transparently `(constantSheaf X.smallEtaleTopology RingCat.{u + 1}).obj (RingCat.of Λ)` |
| Pro-etale ring is the inverse image of that ring | `comparisonProEtaleRing X Λ` applies the actual ring-valued `sheafPullback` to `comparisonEtaleRing X Λ`; it is not independently chosen and is not replaced by another coefficient sheaf |
| Modules mean modules over these ring sheaves | Both categories use the recorded `CategoryTheory.ringedSiteModules.{u + 1}`, transparently Mathlib's `SheafOfModules` of the indicated ring |
| Module inverse image applies inverse image to the module and its action | `comparisonRingedModuleInverseImage X Λ` is the constructed module pullback along the actual ring-adjunction unit. Its `SheafOfModules.pullback` is the module-presheaf pullback followed by module sheafification, as characterized by Mathlib's `pullbackIso`. For the ring `ν⁻¹Λ`, this is the usual inverse image of the module and its scalar action. |
| Corresponding module direct image | `comparisonRingedModuleDirectImage X Λ` is `SheafOfModules.pushforward` along `toProEt X` with the actual ring-adjunction unit. It evaluates G at the same etale object and restricts scalars through that unit. |
| I is an etale module sheaf | `(I : ringedSiteModules.{u + 1} (comparisonEtaleRing X Λ))` |
| I is injective in that module category | `[Injective I]`, Mathlib's categorical extension-along-monomorphisms definition, in the displayed module category |
| Right derived functors computed by injective module resolutions | `(J : InjectiveResolution ((comparisonRingedModuleInverseImage X Λ).obj I))`; `J.cocomplex` is an N-indexed complex of injective objects with a quasi-isomorphic degree-zero augmentation, by the recorded `InjectiveResolution` definition |
| Every positive degree q | `(q : ℕ) (hq : 0 < q)`, allowing all positive integers and excluding exactly degree zero |
| R^q nu_* nu^* I is zero | `IsZero (((comparisonRingedModuleDirectImage X Λ).mapHomologicalComplex (ComplexShape.up ℕ)).obj J.cocomplex |>.homology q)` |

The resolution parameter is universally quantified: the theorem applies to
**every** injective module resolution of the specified inverse image. No
acyclicity property is assumed about J beyond being an injective resolution.
This is exactly the node's stipulated resolution definition of `R^q`, not an
extra mathematical hypothesis or a restriction to a specially chosen resolution.
Mathlib `InjectiveResolution.isoRightDerivedObj` identifies this homology with
`(F.rightDerived q).obj (ν^* I)` for every J. Enough injectives on these small
ringed sites is supplied by the recorded Grothendieck-module/enough-injectives
proof inputs, so the quantification over resolutions is nonvacuous. The
statement does not add an enough-injectives hypothesis to the original theorem.

### Canonical construction and universes

The module pullback construction in Mathlib requires a common object/morphism
universe for its presheaf-module adjoint-existence instance. The original sites
have object universe `u+1` and morphism universe `u`; neither site is replaced
by a smaller collection of schemes and no equality of those universes is imposed.

`comparisonEtaleModel` is `AsSmall.{u+1} X.Etale`, with induced topology;
the pro-etale model, topology and return transport reuse the existing
`Scheme.proEtaleSiteModel`, `Scheme.proEtaleModelTopology` and
`Scheme.proEtaleModuleFromModel`. The model inclusion is precisely
`AsSmall.down ⋙ toProEt X ⋙ AsSmall.up`. The model ring map is obtained by
whiskering the actual ring-adjunction unit with `AsSmall.down.op`.
Pullback transports the input module to the model by `SheafOfModules.pushforward`
along `AsSmall.down` with identity ring map, applies Mathlib's constructed
`SheafOfModules.pullback`, and transports back. The theorem itself is on the
original sites and their intrinsic module categories.

These helpers are specializations/transport of the canonical constructions
already present in Mathlib; they introduce no independent mathematical notion.
They belong to this owning node's interface, carry its source/blueprint docstrings,
and are all listed in `lean.declarations`. `comparisonEtaleRing` is a transparent
specialization of the recorded `constantSheaf`, not a second constant-sheaf
construction. The main declaration and module docstrings include the complete
five-step proof plan from the DAG.

### Recorded dependency declarations read and used

* `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`, declarations
  `AlgebraicGeometry.Scheme` and `Scheme.Hom`; read the locally ringed space
  structure, local-affine condition and morphism structure.
* `def-weil-pbc-etale-site`: `Mathlib.AlgebraicGeometry.Sites.Etale`,
  `Scheme.smallEtaleTopology`, with `Scheme.Etale` and jointly-surjective
  covering families. No new etale site is constructed.
* `def-weil-pbc-proetale-site`: recorded
  `Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory`,
  `Scheme.proEtaleDerivedCategory`; read its intrinsic constant-ring
  `SheafOfModules` category, site and `u+1` size convention. This theorem
  concerns the underlying abelian module category, not the derived-category
  localization, and uses the same actual `ProEt.topology` site.
* `def-weil-pbc-site-comparison-morphism`:
  `Sheaf.AlgebraicGeometry.ProEtaleSiteComparison`,
  `Scheme.proEtaleSiteComparison`, its finite-limit assertion, and
  `Scheme.proEtaleSiteComparisonModules`. Read their complete definitions
  and docstrings. The last named wrapper has a finite-ring hypothesis;
  it is not applied to arbitrary Lambda here. The geometric morphism's
  actual `toProEt` inclusion and the recorded canonical adjunction
  construction are specialized to ring sheaves instead.
* `def-weil-pbc-sites-and-cohomology`:
  `Sheaf.CategoryTheory.SiteCoveringAxioms`,
  `CategoryTheory.Precoverage.IsSiteForCoverings`; its record retains
  Mathlib's sheaf/cohomology conventions for the remaining components.
  The existing scheme topologies supply the sites used here.
* `def-weil-pbc-constant-sheaf`:
  `Mathlib.CategoryTheory.Sites.ConstantSheaf`,
  `CategoryTheory.constantSheaf`, sheafification of the constant presheaf.
* `def-weil-sheaf-of-modules-category`:
  `Sheaf.CategoryTheory.RingedSiteModules`,
  `CategoryTheory.ringedSiteModules`; its transparent body is exactly
  `SheafOfModules.{v} R` on an arbitrary ringed site.
* `def-sp-injective-resolutions`:
  `Mathlib.CategoryTheory.Preadditive.Injective.Basic` and `.Resolution`,
  `CategoryTheory.Injective` and `CategoryTheory.InjectiveResolution`.
* `def-sp-left-exact-additive`: the `mathlib_match` is
  `Mathlib.CategoryTheory.Abelian.RightDerived`,
  `CategoryTheory.Functor.rightDerived`, with
  `InjectiveResolution.isoRightDerivedObj`. Read both signatures and
  docstrings; the latter is the exact resolution-form interpretation used here.

The statement dependencies are imported directly or through their recorded
public dependency modules. The already stated proof inputs have ordinary
non-public imports: `SheafOfModules.isGrothendieckAbelian`,
`IsGrothendieckAbelian.enoughInjectives`,
`CategoryTheory.module_abelian_evaluation_comparison`, and
`ProEtale.comparisonCohomologyMap_bijective`. The vanishing Mathlib leaf
`Functor.isZero_rightDerived_obj_injective_succ` is in the already public
right-derived module. The size node is a convention with no module.
`det-pe-injective-acyclicity-reduction` has no Lean record yet; it is a
**proof** dependency, not a statement dependency, so no import exists and
no other DAG node is stated in this delivery.

### Edge cases checked before stating

* Empty scheme: the empty covering forces the usual zero module sections;
  all native sites, constant sheaves and model equivalences remain defined.
* Zero ring and zero injective module: no `Nontrivial` hypothesis is present;
  the canonical ring/unit/module constructions and zero homology apply.
* Infinite rings, for example Z and arbitrary polynomial rings: no `Finite`
  or torsion hypothesis occurs anywhere in the new declarations.
* Degree zero: deliberately excluded by `hq`; the underived comparison
  image need not be zero. Degree one and every higher degree are included.
* Disconnected and non-quasi-compact/non-quasi-separated schemes: neither
  connectedness nor any finiteness/geometric property occurs in the signature.
* Coefficient/module sizes: Lambda and module values are in the common
  larger site universe `u+1`, while the original site morphism universe
  remains `u`. AsSmall changes no objects, covers or coefficient data.
* Arbitrary resolutions: J has exactly Mathlib's injective-resolution
  structure; no termwise direct-image acyclicity premise is added.

### Searches actually run

* `msearch.py leanfinder`: “The inverse image of an injective etale sheaf
  of modules over an arbitrary discrete commutative ring is acyclic for
  the direct image from the proetale site”. Eight hits, including
  `LightCondensed.instIsGrothendieckAbelianLightCondMod`, local-injectivity
  predicates and etale-site definitions. No exact intrinsic ringed
  comparison-acyclicity declaration.
* `msearch.py leansearch`: “An injective etale sheaf of modules pulled
  back to the proetale site has vanishing positive higher direct images
  under comparison”. Eight hits, notably `SheafOfModules.pullback` and
  `SheafOfModules.PullbackConstruction.adjunction`; read their actual
  Mathlib source, including the same-universe existence instance in
  `PresheafOfModules/Pullback.lean`. These supply the canonical construction,
  not the acyclicity theorem.
* `msearch.py loogle`: `Functor.rightDerived, Injective` gave zero hits
  with “unknown identifier Functor.rightDerived”; this rejected query
  is not evidence of absence. A corrected query `CategoryTheory.Injective`
  gave twelve hits for the injective definition and its elementary
  operations; none is the requested comparison statement.
* `msearch.py grep`: `comparisonUpperStar|comparisonLowerStar|rightAcyclic`
  in Mathlib `AlgebraicGeometry/Sites`: zero hits.
* `rg` in upstream `WeilConjectures`, the published framework and side
  `lean/Sheaf`: found
  `ProEtale.rightAcyclic_comparisonUpperStar_obj_of_injective` in
  `WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStarAcyclic`.
  Read its entire signature, docstring, generic coefficient assumptions,
  the `rightAcyclic` definition, and comparison definitions. Its direct
  objects are `Sheaf J A`; specializing A to ModuleCat gives the fixed
  scalar presentation, not the node's explicit intrinsic module category
  over the specified inverse-image ring. No exact existing binding in
  this representation was found, so the delivery states that representation
  instead of silently changing objects or demanding finite coefficients.
* `scompile.py --source
  WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStarAcyclic`
  read the current server declaration as well as the local source, so
  the non-match is not based on an outdated checkout.
* `rg` for ringed-module inverse images and AsSmall etale/pro-etale models
  found `Scheme.proEtaleModuleInverseImage` and the existing pro-etale
  model transports in `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`.
  Read their full definitions; these concern maps between schemes'
  pro-etale sites. The existing model and return transport are reused;
  the missing comparison inclusion/unit specialization is supplied here.
* `rg` for all twelve new declaration names across Mathlib, upstream,
  `lean/Sheaf` and the published framework gave zero hits.

Sources read include the current blueprint `_section.md`, the DAG's full
statement/proof, and local Stacks `proetale.tex` labels
`lemma-affine-vanishing` (099U) and `lemma-relative-comparison` (099V).
The proof docstring preserves the node's arbitrary-ring module/abelian
bridge, rather than incorrectly taking injectivity after forgetting.

There is no statement correction, disputed statement, new node, or dependency
node repair. All writes are confined to this sandbox. Earlier in this worker
session some read-only Git inspection was mistakenly run in the shared clone;
no Git mutation or direct repository edit was performed, and subsequent work
uses only file reads and the prescribed compilation/delivery wrappers.

### Validation

The module passed `scompile.py NP sk-lem-pe-injective-acyclicity` cleanly,
including the actual library-path compile, under the default 60-second
per-file limit. The module has explicit universes and `autoImplicit false`,
no temporary `#check` declarations, no lines over 100 characters and only
the main theorem's expected `sorry`.

The worker's final check is `deliver2.py NP sk-lem-pe-injective-acyclicity
--no-push`. The independent reader supplies the second-reading section
and performs delivery; the worker does not write that section or push.


## Second reading by NP

I independently read the item's complete node and the delivered module together,
the blueprint `_section.md`, Stacks `proetale.tex` Tags 099U, 099V and 099W,
and `sites-cohomology.tex` Tag 03FD. Tag 099U itself assumes an affine scheme
and an injective **abelian** sheaf; Tag 099V's affine-local argument applies
over an arbitrary scheme. The node's five-step proof correctly extends this
to injective modules by 03FD and the arbitrary-abelian-sheaf comparison 099W.
It does not silently use an injective module as an injective abelian sheaf.
There is no extra global affine, quasi-compact, quasi-separated, torsion,
finite-coefficient or characteristic hypothesis in the source route.

My list of objects, hypotheses and conclusion clauses, with the file open:

| Node item | Lean rendering and second-reader verdict |
| --- | --- |
| Scheme X, arbitrary | `(X : Scheme.{u})`; matches the recorded `Scheme` and `Scheme.Hom` definitions. No geometric property is imposed. PASS. |
| Discrete commutative coefficient ring Lambda | `(Λ : Type (u + 1)) [CommRing Λ]`; the constant-sheaf construction realizes discrete coefficients. There is no `Finite`, `Nontrivial`, torsion, invertibility or field instance. PASS. |
| Small etale and pro-etale sites of this same X | `X.Etale`, `X.smallEtaleTopology`, `X.ProEt`, `ProEt.topology X`; these are the recorded Mathlib sites, with etale and weakly etale objects respectively, and their actual covering topologies. PASS. |
| Comparison geometric morphism nu_X | `toProEt X` inside `comparisonRingAdjunction X`; this is the inclusion underlying the recorded `proEtaleSiteComparison`, with the same constructed Kan-extension/sheafification adjunction, now specialized to `RingCat`. The finite-ring module wrapper is not applied. PASS. |
| Constant etale sheaf of rings Lambda_X,Et | `comparisonEtaleRing X Λ` unfolds to `(constantSheaf X.smallEtaleTopology RingCat.{u + 1}).obj (RingCat.of Λ)`; uses the recorded constant-sheaf functor. PASS. |
| Pro-etale coefficient ring is nu_X inverse image of that ring | `comparisonProEtaleRing X Λ` applies the actual ring-valued comparison sheaf pullback to `comparisonEtaleRing X Λ`. It does not pick an unrelated ring sheaf. Using `RingCat` forgets only the recorded commutativity property, not the ring data or module notion. PASS. |
| Both Mod categories are intrinsic modules over these ring sheaves | `ringedSiteModules.{u + 1}` is the dependency's transparent `SheafOfModules` abbreviation. Domain and codomain use exactly the two rings just listed, not fixed-scalar `Sheaf J (ModuleCat Λ)`. PASS. |
| Module inverse image carries the module and scalar action along nu_X | `comparisonRingedModuleInverseImage X Λ`: transport to `AsSmall`, `SheafOfModules.pullback (comparisonModelRingUnit X Λ)`, and the already recorded `proEtaleModuleFromModel`. The ring map is the whiskered actual unit of `comparisonRingAdjunction`. Mathlib `pullbackIso` identifies its construction with module-presheaf pullback followed by sheafification; for the inverse-image ring this is inverse image of the original action. PASS. |
| Corresponding module direct image | `comparisonRingedModuleDirectImage X Λ` is `SheafOfModules.pushforward` along the original inclusion using the original ring-adjunction unit. Its sections are restriction to etale objects with restriction of scalars through that unit. PASS. |
| I is an injective etale module sheaf | `(I : ringedSiteModules.{u + 1} (comparisonEtaleRing X Λ)) [Injective I]`; injectivity is in that module category, by the dependency's extension-along-monomorphisms definition. PASS. |
| Right derived functors are computed by injective module resolutions | `J : InjectiveResolution ((comparisonRingedModuleInverseImage X Λ).obj I)`; the dependency structure has an N-indexed termwise injective complex and quasi-isomorphic degree-zero augmentation. This universally quantifies over resolutions, imposing no acyclicity assumption. `InjectiveResolution.isoRightDerivedObj` identifies the resulting homology with the usual right-derived value for every J. Enough injectives on the small-model module categories, and transport back along the site equivalences, ensure this is nonvacuous. PASS. |
| Every positive degree, and precisely those degrees | `(q : ℕ) (hq : 0 < q)`; the resolution binder preceding q still quantifies over every pair (J,q), as the resolution interpretation requires. PASS. |
| R^q nu_X,* nu_X^* I vanishes as a module sheaf | `IsZero (((comparisonRingedModuleDirectImage X Λ).mapHomologicalComplex (ComplexShape.up ℕ)).obj J.cocomplex |>.homology q)`; this is the homology object in the etale module category, not merely zero global sections or a single evaluation. PASS. |

I opened the recorded statement-dependency signatures: Mathlib `Scheme`,
`Scheme.Hom`, `smallEtaleTopology`, `constantSheaf`, `Injective`,
`InjectiveResolution`, `Functor.rightDerived` and
`InjectiveResolution.isoRightDerivedObj`; project `proEtaleDerivedCategory`,
`proEtaleSiteComparison`, `preservesFiniteLimits_proEtaleSiteComparison`,
`proEtaleSiteComparisonModules`, `Precoverage.IsSiteForCoverings` and
`ringedSiteModules`. The site's underlying topology is used directly where
its recorded node also packages a derived category. I also read the actual
`proEtaleSiteModel`, `proEtaleModelTopology`, `proEtaleModuleFromModel`, and
Mathlib `SheafOfModules.pullback`, `PullbackConstruction.adjunction` and
`pullbackIso`, rather than inferring their contents from their names.
The Grothendieck, enough-injectives, module/abelian evaluation comparison and
abelian etale/pro-etale comparison proof imports agree with their recorded
signatures. The unstated reduction node is a proof dependency only.

Edge-case audit: the empty scheme is allowed by the native sites and their
empty covers; the zero ring and zero module are allowed; arbitrary infinite
rings and every characteristic are allowed. Degree zero is excluded exactly
as required, while degree one and every higher degree are included. There
is no nonempty index set or chosen cover in the signature. All universes are
bound by `universe u` and `autoImplicit false`. Sites retain object universe
u+1 and morphism universe u. The `AsSmall.{u+1}` models only enlarge Hom
universes, without restricting objects, covers or rings. Coefficients and
module values live in the common larger universe required by the node's
size convention; no extra equality between original site universes occurs.

Independent H4 searches actually performed:

* `msearch.py ... leanfinder "Higher direct image of the pro-etale inverse image of an injective module over a constant ring sheaf vanishes in nonzero degrees"`: eight hits, including `Functor.isZero_rightDerived_obj_injective_succ`, condensed-module Grothendieck results and local injectivity of sheafification; none states this comparison-ringed-module result. The elementary vanishing lemma requires its input itself to be injective, unlike the inverse image here.
* `msearch.py ... leansearch "Pulling back an injective sheaf of modules from the etale site makes an acyclic sheaf for comparison direct image"`: eight hits for module pullback, its adjunction and construction; these supply constructions, not this theorem.
* `msearch.py ... loogle "CategoryTheory.InjectiveResolution"`: twelve hits, including the resolution structure, self-resolution and comparison maps; no comparison-site acyclicity statement.
* `msearch.py ... grep "comparisonRingedModule|comparisonUpperStar.*injective|rightAcyclic_comparison"`: zero Mathlib hits. Independent `rg` searches over Mathlib's scheme sites, all upstream `WeilConjectures`, the exact shared 51-module framework and project `lean/Sheaf` found the existing `ProEtale.rightAcyclic_comparisonUpperStar_obj_of_injective` and the pro-etale model transports, but no exact intrinsic ringed-module statement. I read that theorem in the shared framework together with its surrounding binders, `comparisonUpperStar`, `comparisonLowerStar`, and the definition of `Functor.rightAcyclic`: it concerns `Sheaf J A` for a fixed abelian value category A. Specializing to `ModuleCat Λ` changes the literal coefficient presentation and does not supply this intrinsic `SheafOfModules` interface. Its presence therefore does not justify an `existing: true` binding of this node. I read `coord/pefw-upstream-framework.md` as required. Exact searches for the delivered ringed-comparison names found no pre-existing declarations, and the upstream node-name inventory has no binding for this item.

H5/H6/H8/H9 audit: every new helper has actual constructed data; the only
postponed theorem is the named main statement with proof `sorry`. The two
instances provide continuity and additivity through existing constructions,
not additional postponed theorems. Every declaration names its source and
this blueprint node. The theorem docstring preserves all five proof steps,
including the module/abelian bridge and the limitation on the reduction
node's use. There are no file-local definitions/notations, private objects,
unbound universes, or hidden additional statement premises. Every helper
is listed in `lean.declarations`. No new node, dependency repair or
statement correction is present, so no H12/H13 or citer-correction audit
is required. Comparing the sandbox node to the shared node shows `lean`
as its only differing field. Its `lean.statement` is verbatim the theorem
signature in the module.

Mismatches found: none. I retained the Lean and node record unchanged and
added this independent second-reading section. The required `scompile.py NP
sk-lem-pe-injective-acyclicity` compile passed both the sandbox check (4.2 s)
and actual module-path check (4.0 s), with no errors or warnings. Delivery
preflight and push are performed after this report is written.
