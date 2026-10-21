## Worker report

The module `Sheaf.AlgebraicGeometry.CondensedLocalizationExactCohomology` states both clauses of `lem-sfb-condensed-localization-exact-cohomology`. The item JSON changes only `lean`. No mathematical statement correction, new node, dependency repair, build, or direct Git mutation was needed. All seven theorem proofs are `sorry`. All five helper definitions have real data obtained from the recorded constructions.

### Hypotheses and objects

- A scheme S is the explicit section variable `{S : Scheme.{u}}`.
- An arbitrary object u:V→S of the small pro-etale site is `(V : S.ProEt)`; the morphism is `V.hom`. Its weak etaleness is the site's existing instance `V.prop`. There is no monomorphism or open-immersion assumption.
- A commutative condensed ring is `(Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]`. This is exactly the unbundled form of the recorded `Profinite.CondensedRing = Mon (Sheaf ... Ab)` with a commutativity instance; it does not assume a topological presentation of Λ.
- Γ_T=p_T^*Γ is `condensedRingObj Λ T`; its section-ring sheaf is the recorded `InternalModuleOperations.ring Λ T`. That declaration reconstructs the ring operations from this very internal ring object, rather than choosing another coefficient sheaf.
- Sectionwise module sheaves are `SheafOfModules.{u + 1} (ring Λ T)`, the transparent Mathlib implementation of the recorded `CategoryTheory.ringedSiteModules`.
- The functor `pullback Λ V` is a definition with explicit source and target whose entire body is the existing `InternalModuleOperations.upperStar Λ V.hom`. The latter is the presheaf tensor pullback followed by module sheafification along the section-ring map reconstructed from the canonical eta. Its recorded internal/sectionwise comparison identifies it with `CondensedRing.upperStar`, the specified internal ringed-topos pullback, not a replacement abelian inverse image or an arbitrary map.
- For the derived clauses only, `[HasDerivedCategory.{wS} (SheafOfModules.{u + 1} (ring Λ S))]` and the independent target binder at `wV` specify the node's chosen localization universes. They do not identify site object and morphism universes, which remain u+1 and u, and do not identify the two derived morphism universes. All variables and universes are explicitly bound, with `autoImplicit false`.

### Clause (1)

`Scheme.ProEt.sliceEquiv S V` is the already constructed concrete category equivalence, whose inverse sends W→V to its composite over S and its map to V. `localization_comparison` asserts the covering-sieve iff for this exact inverse and `(ProEt.topology S).over V`. The category equivalence is supplied by that existing equivalence object, not an unspecified existential equivalence. This renders the site identification including coverings.

The next conjunct is `Nonempty (ProEtale.upperStar Ab V.hom ≅ localizationRestriction Ab V.hom V.prop)`. The existing `upperStarIsoLocalizationRestriction`, used in the following normalization, is the canonical comparison of the two left adjoints of the same direct image. Its target is sectionwise composition of test objects. The coefficient-independent inverse-image theorem is imported as a proof dependency.

`restrictedRing Λ V` is precisely `(localizationRestriction RingCat V.hom V.prop).obj (ring Λ S)`. The existential `e : restrictedRing Λ V ≅ ring Λ V.left` identifies the coefficients. For every test object W and every coefficient section a, the equation in `localization_comparison` identifies `e.hom` with the actual `condensedPullbackHom` after the inverse of the canonical abelian inverse-image/restriction comparison. Thus e is the section-ring version of alpha_u, not an arbitrary isomorphism. As a morphism of sheaves of rings, e already commutes with every restriction and preserves addition, multiplication and the unit; those properties are not extra assumptions.

`actionTransport Λ V e` is exactly `SheafOfModules.restrictScalars e.inv`. On every W this defines b acting on m by e_W inverse of b acting on m. `localization_comparison` asserts that this actual functor `IsEquivalence`. The inverse transport uses e.hom. The underlying additive sections, restriction maps, and morphisms are retained by Mathlib's scalar restriction.

`restriction Λ V` is Mathlib `SheafOfModules.pushforward` along the composition functor `MorphismProperty.Over.map ... V.prop`, with the identity coefficient map. Hence its value on W is F(W→S), with precisely the original module structure and restriction maps. `localizedPullback Λ V e` is this restriction followed by `actionTransport`. There is no copied module or sheaf construction.

The isomorphism `rho : pullback Λ V ≅ localizedPullback Λ V e` is natural in F and is an isomorphism of module sheaves. Its inverse is normalized on every section m over every W: evaluate the existing ringed-module adjunction unit at the composite W→S and restrict along the unit of `mapPullbackAdj` at W. This unit is the graph W→W×_S V. The normalization is exactly m↦1⊗m followed by sheafification. Therefore rho is the canonical tensor-inverse comparison; its forward formula is b⊗m↦alpha inverse(b)m. As rho is a module morphism, its components give the required canonical additive section isomorphism compatible with multiplication by sections. Its sheaf naturality gives compatibility with every section restriction.

`pullback_additive`, `pullback_preservesFiniteLimits`, and `pullback_preservesFiniteColimits` state exactly the final additive/exact assertion. `localizedPullback_additive` supplies additivity of the termwise comparison target needed for the derived representative statement. These are clauses of this node, not new independent mathematical lemmas. Their docstrings give Steps 1–5 and name the generic exactness, equivalence-preservation, and natural-isomorphism invariance nodes used by the proof.

### Clause (2)

The unbounded derived functor is the existing `(pullback Λ V).mapDerivedCategory.{wS,wV}`, which applies the exact functor termwise and localizes at quasi-isomorphisms. No left-derived resolution, bounded subcategory, K-flatness assumption, or auxiliary chosen derived functor is substituted.

`localized_complex_represents` quantifies over every coefficient isomorphism e and every module comparison rho (the preceding theorem supplies the canonical ones), every `K : CochainComplex ... ℤ`, every `Q : DerivedCategory ...`, and every representation `a : DerivedCategory.Q.obj K ≅ Q`. It asserts the isomorphism between the derived image of Q and `Q` of `((localizedPullback ...).mapHomologicalComplex (.up ℤ)).obj K`. This is exactly the termwise sectionwise restriction with its coefficient action transported. Naturality of rho for the differentials gives the complex isomorphism. The hypotheses e, rho and a are the named comparison and representation data whose existence was already stated, not extra restrictions on u or Γ.

`cohomology_comparison (q : ℤ)` asserts a natural isomorphism of the functors `DerivedCategory.homologyFunctor source q ⋙ pullback` and `pullback.mapDerivedCategory ⋙ DerivedCategory.homologyFunctor target q`. Its components are u^*H^q(Q)≅H^q(D(u^*)Q), and its functor isomorphism supplies naturality for all derived morphisms.

The equation for every complex K fixes that natural isomorphism: compose its component at QK with target cohomology of `mapDerivedCategoryFactors` and then `homologyFunctorFactors`; this equals source `homologyFunctorFactors` mapped through pullback, followed by the inverse of `(K.sc q).mapHomologyIso (pullback Λ V)`. `ShortComplex.mapHomologyIso` is the canonical comparison induced by the preserved kernel and image and their quotient, with its cycle inclusion and cohomology projection compatibility. This normalization is stronger than a bare existence of an isomorphism only in the sense that it specifies the canonical map already requested by the node. It does not assert an additional mathematical conclusion.

There is no boundedness, flatness, finite presentation, quasi-compactness, quasi-separatedness, admissibility, or nonemptiness assumption anywhere in these declarations.

### Dependencies read and reused

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt`, `ProEt.mk`, `ProEt.topology`; objects and their weak-etale instances retain the site's object/morphism universe distinction.
- `Sheaf.Topology.ProfiniteCondensedRing`: `Profinite.CondensedRing`, read together with its recorded underlying Mon encoding; the statement uses that encoding unbundled.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`: `condensedRingObj`, `coefficientRing`, `condensedPullbackHom`, `coefficientPullbackIso`, `condensedPushforwardHom` and their ring-morphism instances.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs`: `CondensedRing.upperStar`, its mapMod/extension-of-scalars formula and specified adjunction.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`, transparently `SheafOfModules` for a general ringed site.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous`: `SheafOfModules.pushforward`, `overFunctor`; the localized ringed-site record points to this exact sectionwise restriction API.
- `Sheaf.AlgebraicGeometry.InternalModuleOperationsTransport`: `InternalModuleOperations.ring`, `equivalence`, `coefficientMap`, `upperStar`, `adjunction`, `upperComparison`, and `internal_module_operations_transport`. These recorded definitions give the actual section-ring reconstruction and tensor-formula sectionwise adjunction.
- `Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization`: the concrete `Scheme.ProEt.sliceEquiv` and its covering assertion.
- `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs`: `ProEtale.localizationRestriction`, `localizationRestrictionLowerStarAdjunction`, `upperStarIsoLocalizationRestriction`, including the coefficient-independent abelian-sheaf comparison.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`, `ExactFunctor`, `HomologySequence`: `HasDerivedCategory`, `DerivedCategory`, `DerivedCategory.Q`, `Functor.mapDerivedCategory`, `mapDerivedCategoryFactors`, `homologyFunctor`, `homologyFunctorFactors`.
- `Mathlib.Algebra.Homology.ShortComplex.PreservesHomology`: `ShortComplex.mapHomologyIso` and its construction using left homology data, including `mapCyclesIso_hom_iCycles`.

All already stated proof modules are imported, including `ProEtaleObjectInverseImageRestriction`, `LocalizedModuleExactForSystems`, the recorded module-sheaf tensor module, and Mathlib's adjoint-limit and localization interfaces. No declaration from a proof is used unless it is already a public declaration of the imported module. There is no import cycle added by this delivery.

### Searches actually run

The mandated `msearch.py Q126 <item>` calls were:

1. LeanFinder: "For a condensed coefficient ring pullback to an object of the pro-etale site is exact sectionwise restriction and commutes with unbounded derived cohomology". Eight hits, including `LightCondensed.instIsGrothendieckAbelianLightCondMod`, condensed exact-limit APIs and `SheafOfModules.pullbackIso`; none states the combined specific canonical condensed localization and derived normalization.
2. Loogle: `SheafOfModules.overFunctor`. Three hits: `overFunctor`, `overFunctorMap`, `Scheme.Modules.overFunctorEquiv`. The general localization restriction is reused; scheme open restriction alone is not the full theorem.
3. Mathlib grep: `overFunctor|homologyFunctorIso` in `Algebra/Category/ModuleCat/Sheaf`. Five hits in `PushforwardContinuous`, giving the exact existing restriction construction, not a full statement match.
4. LeanSearch: "Exact pullback of sheaves of modules along localization of a ringed site commutes with cohomology in the unbounded derived category". Eight hits on `SheafOfModules.pullback`, `pullbackPushforwardAdjunction`, `PullbackConstruction.adjunction`, scheme pullback and free-module comparisons; none matches the whole node.

Direct `rg` searches in both `lean/WeilConjectures` and `lean/Sheaf` covered the item id, condensed/localization/cohomology combinations, sectionwise transport, `localizationRestriction`, `sectionRing`, `ringSheaf`, and the new declaration names. The item id has no existing upstream match. The pertinent partial results were `CoefficientSectionsLocalization` (only coefficient sections), `ProEtaleObjectInverseImageRestriction` (only its abelian/ring clause applies to arbitrary condensed coefficients), and `InternalModuleOperationsTransport` (the sectionwise/internal operation comparison, reused). Generic Mathlib exact-derived and short-complex comparisons were read in full at their declaration sites. No exact existing declaration of this aggregate item was found, and no existing notion was redefined.

### Source checks and edge cases

Read Stacks `sites.tex`, `lemma-localize-given-products` (03CE), the localized ringed-site definition in `sites-modules.tex` (04IX) and its section formula; `homology.tex`, `lemma-exact-functor` (010N); `derived.tex`, `lemma-right-derived-exact-functor` (015F), especially every unbounded complex computing the derived functor. Read the blueprint's coefficient-morphism definition: alpha is the canonical comparison of pullback from the point and is invertible without admissibility. The retained stage-1 source report supplies the explicit transport and tensor inverse calculations, which the theorem docstrings retain in summarized form.

Checked V empty, V=S with identity structural map, a disconnected V, non-monomorphic weak-etale V, the zero ring and zero module, q=0, negative q, and complexes unbounded in both directions. All are admitted. For a nontrivial coefficient-ring automorphism the action must use e.inv, and does; using e.hom here would have been wrong. A sheaf epimorphism need not be sectionwise surjective; exactness is asserted as finite limit/colimit preservation, not sectionwise surjectivity. Graph restriction in rho's normalization exists without any monomorphism assumption. No statement dispute or node fault was found.

### Validation

`python3 /home/ubuntu/weil-launcher-all/batch2/scompile.py Q126 lem-sfb-condensed-localization-exact-cohomology <module>` passed cleanly both as sandbox and final module, in 14.1 s and 17.1 s. An initial elaboration exposed the reduced comma-object endpoints of the existing pullback, preventing derived-category and additive-instance inference. The delivered `pullback` specialization retains explicit source/target types and resolves that inference issue without any universe restriction or new mathematical hypothesis. Scratch `#check` probes were confined to `scratch/Check.lean`, outside the delivery's Lean tree.

The prescribed `deliver2.py Q126 lem-sfb-condensed-localization-exact-cohomology --no-push` completed successfully: `OK (dry run): commit 91ff9f13c13 passes the preflight and compiles; nothing pushed`. The packet contains exactly the module, the item node copy and this report.

## Second reading by Q126

This is a fresh self-reading with the node and final source open; no second agent was started, as the dispatch explicitly forbids it. The maintainer's independent review remains the independent reading.

I checked all hypotheses and both numbered clauses against the exact declarations listed above. In particular, I checked the orientation of e, the e.inv scalar transport, all-section naturality of the coefficient map, and the adjunction-unit/graph normalization of rho.inv. The graph lands in W×_S V with the project site's chosen variable factor first, exactly the target of the adjunction unit; the formula compiles without a cast or an assumption that V→S is mono. `IsEquivalence` is attached to the actual scalar-restriction functor, whose underlying sections remain unchanged.

For the derived statement I checked that K has integer degrees and no bound and that every representation QK≅Q is admitted. I checked each endpoint of the cohomology normalization: it starts in u^*H^q(QK), goes through H^q(D(u^*)QK), and ends in H^q(C(u^*)K). The right path goes through u^*H^q(K) and then the inverse kernel/image comparison, with the same endpoints. The natural isomorphism is between functors on the derived category, so naturality is not restricted to complex maps.

The only implementation repair from the first draft was exposing the existing pullback's source and target, after reading its full universes with sandbox `#check` probes; no statement or dependency was weakened. There are no hollow definitions, implicit variables, extra finiteness or flatness assumptions, private constructions, file-local instances or notation, or lines above 100 characters. Seven postponed theorems all carry this node's blueprint id and a proof docstring. The five helpers specialize existing functors and introduce no independent notion needing a new node.
