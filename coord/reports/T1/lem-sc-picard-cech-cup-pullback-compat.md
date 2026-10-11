## Worker report

Repair of return X-20c63 (head 20c63957a), 2026-10-12.

H10: inserted `import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf` immediately after `import Sheaf.AlgebraicGeometry.ModuleCohomologyFMap` in `CechRefinementCochainMap.lean`. The imported declaration `AlgebraicGeometry.Scheme.Modules.presheafModuleCat` gives the underlying presheaf of global-section modules; it is required directly by this module's signatures and component formulas.

H3: added `AlgebraicGeometry.Scheme.Modules.cechRefinement_composition_naturality` in `CechCupPullbackCompat.lean`, and listed it in the item's `lean.declarations`. It explicitly quantifies `f₁ : X'' ⟶ X'` as well as `f : X' ⟶ X`. The coefficient identification is the existing `tensorSectionsComp f₁ f` from `Sheaf.AlgebraicGeometry.EtaleTensorSections`, not an arbitrarily chosen isomorphism from a Nonempty theorem. Its definition is the conjugate of sectionwise pushforward composition under the canonical, section-normalized tensor-pullback adjunctions.

Current hypothesis and clause mapping:

- The main theorem's `X X' : Scheme`, `f : X' ⟶ X`, `U`, `hU`, `U'`, `hU'`, `refine` and `hrefine` give exactly the schemes, morphism, arbitrary covers and specified refinement. Index types are arbitrary `Type v`; there are no finiteness, affine, field or characteristic restrictions.
- `F G : X.Modules` and the two `IsQuasicoherent` instances give the coefficient hypotheses; `(tensorPullback f).obj` gives the recorded module pullbacks. `p q : ℕ` includes degree zero.
- `cF`, `cF'`, `cG`, `cFG` with their `IsModuleCechComparison` hypotheses are the canonical comparisons, without invertibility assumptions. `gamma` with `IsCechRefinementMap` is fixed by the Tag 01FD tuple rule. The first conjunct is clause (a), the equality of refinement followed by comparison and comparison followed by `moduleCohomologyPullback`.
- `cup` with `IsCechCupProduct` is the bilinear map induced by the signed cochain cup construction. `sheafCup` with `IsModuleCupProduct` is the usual sheaf cup product. The second conjunct is clause (b). The third conjunct, quantifying `IsIso` only there, gives the in-particular identification through inverse comparisons.
- `moduleCup_coefficient_naturality`, `cechCup_coefficient_naturality`, and `cechRefinement_coefficient_naturality` give coefficient naturality. `moduleCup_pullback_naturality` gives the cup-product pullback equality through the section-normalized `module_pullback_tensor` identification.
- In the new composition theorem, `X X' X''`, `f`, `f₁`, the three cover families and three covering equations specify successive pullbacks of covers. `refine`, `hrefine`, `refine₁`, `hrefine₁` specify the two refinements. `hrefineComp` is a proof of their composite containment with index function `refine ∘ refine₁`; it follows pointwise from the two containment hypotheses and functoriality of inverse images, so imposes no extra geometric condition.
- `F` and `IsQuasicoherent` give the coefficient hypothesis; `p : ℕ` is unrestricted. `gamma`, `gamma₁`, and `gammaComp` with their three `IsCechRefinementMap` hypotheses fix the first, second, and composite cochain maps. `c` and `cComp` with `IsModuleCechComparison` fix the source and final canonical comparison.
- The new theorem's first conjunct is an equality of cochain morphisms: `gamma ≫ gamma₁` followed by the Cech map of `(tensorSectionsComp f₁ f).hom.app F` equals `gammaComp`, whose refinement is explicitly `refine ∘ refine₁` and whose scheme morphism is `f₁ ≫ f`.
- Its second conjunct states the corresponding equality after taking homology, forgetting scalars with the canonical homology comparisons, applying the coefficient identification, and applying `cComp`: this equals `c` followed by the usual pullback along `f₁ ≫ f`.
- Its third conjunct identifies the composite of the two usual cohomology pullbacks, followed by cohomology of the same coefficient identification, with the usual cohomology pullback along `f₁ ≫ f`. Together these explicitly give the comparison square for successive pullbacks.

Dependencies used: `IsModuleCechComparison` from `Sheaf.AlgebraicGeometry.ModuleCechComparison`; `cechComparisonMapNaturality` from `Sheaf.Paper.CechComparisonMapNaturality`; `RingedSpace.moduleCohomology` from `Sheaf.Topology.RingedSpaceModuleCohomology`; `tensorPullback` from `Sheaf.AlgebraicGeometry.TensorPullback`; `exists_tensorPullbackAdjunction` from `Sheaf.AlgebraicGeometry.TensorPullbackAdjunction`; `moduleCohomologyPullback` from `Sheaf.AlgebraicGeometry.ModuleCohomologyFMap`; `module_pullback_tensor` from `Sheaf.AlgebraicGeometry.ModulePullbackTensor`; the three new definition modules below; and the existing normalized `tensorSectionsComp` described above. The source of the repair was read at Stacks Tag 01FD (https://stacks.math.columbia.edu/tag/01FD), including the tuple rule and the resolution comparison diagram; composition uses the node's proof Step 4.

Edge cases checked: identity morphisms and identity refinements, repeated/noninjective refinement indices, empty covers on the empty scheme, empty opens, zero coefficient modules, degree zero, and distinct global-section rings at all three schemes. All maps across schemes live in additive groups; no equality of the rings is imposed. The canonical coefficient isomorphism, rather than literal equality of successive tensor pullbacks, handles the identity/composition cases.

Repair searches: `msearch.py leanfinder` with "Cech refinement cochain maps compose under successive scheme pullbacks" returned scheme pullback cocycle/gluing hits, none this statement; `msearch.py loogle` with "tensorSectionsComp" returned unknown identifier and zero hits. `rg` with `cechRefinement.*comp|refinement.*comp|tensorSectionsComp` over Mathlib algebraic geometry, upstream WeilConjectures, and Sheaf found the existing normalized `tensorSectionsComp`, which is reused, and no existing refinement composition theorem. Earlier searches for the three definition nodes are retained below and in their JSON `mathlib_searches`.

The item's natural-language statement and its inherited statement correction are unchanged. All theorem proofs remain `by sorry`; no data definition was changed apart from the explicit import. The earlier independent reading below predates this repair: the next independent reader must verify the added composition declaration, matching the three conjuncts and the two specified refinements above, before delivery.

## New nodes

`def-sc-cech-refinement-cochain-map` characterizes the actual refinement map by its pullback-and-restriction components, states unique existence, and defines its homology map through canonical scalar-forgetting comparisons (Tag 01FD). It does not define comparison compatibility as a hypothesis. The repair adds its missing direct import only.

`def-sc-cech-cup-product` defines the front/back Alexander–Whitney cochain formula using existing `tmulSection`, states signed Leibniz, and characterizes the induced bilinear product on cocycle classes (Tag 07MB, coefficient sheaves in degree zero).

`def-sc-module-cohomology-cup-product` defines computing resolutions and sectionwise resolution pairings, then characterizes the usual module-cohomology cup product by their cocycle classes (section-cup-product and Tag 0FKV). It does not define a replacement tensor product: the existing sheaf tensor product is used. Its existence statement follows the Godement-resolution argument.

The searches in these three nodes' `mathlib_searches` record LeanSearch, LeanFinder/Loogle and grep of Mathlib, upstream and DAG declarations. Existing Cech complexes, sheaf tensor products, `tmulSection` and module cohomology are reused; the existing field-dependent cup API does not cover arbitrary schemes and arbitrary O_X-modules. No new node is added by this repair.

## Earlier second reading (a previous round; superseded)

The theorem has the original scheme, morphism, cover, refinement, quasi-coherence, and degree binders. Every comparison map is universally quantified and constrained by `IsModuleCechComparison`; (a) contains the refinement/pullback equality, (b) contains an elementwise cup compatibility predicate, and the final conjunct is an explicit naturality equality. The landed comparison module is imported directly.

## Earlier second reading (a previous round; superseded)

This reading is retained from the preceding delivery; it does not certify the new composition theorem added in the X-20c63 repair. The next independent reader must update this section.

The original Worker report above described intended mathematics, not the actual delivered signature. I opened the node and all four sandbox modules independently. The original signature compiled as a combined file but did **not** state the node. The repaired delivery keeps the item's natural-language statement unchanged and replaces its incorrect Lean rendering and the three new definition nodes/modules.

Objects, hypotheses, and conclusions matched individually:

- Schemes X and X', and an arbitrary scheme morphism f:X' -> X: `X X' : Scheme.{v}` and `f : X' ⟶ X`. Correct, with no base field, characteristic, separation, Noetherian, quasi-compactness, or finiteness binder.
- An arbitrary open cover U of X: `{ι : Type v}`, `U : ι → X.Opens`, `hU : iSup U = ⊤`. Correct; no finite or ordered-index instance is imposed.
- An arbitrary open cover U' of X': `{ι' : Type v}`, `U' : ι' → X'.Opens`, `hU' : iSup U' = ⊤`. Correct.
- The *specified* refinement function and containment: `refine : ι' → ι`, `hrefine : ∀ i, U' i ≤ f ⁻¹ᵁ U (refine i)`. Correct. These now actually determine gamma through `IsCechRefinementMap`, rather than being unused parameters.
- O_X-modules F and G, both quasi-coherent: `F G : X.Modules`, `[F.IsQuasicoherent] [G.IsQuasicoherent]`. Correct, using the landed Coherent module's Mathlib quasi-coherence notion. No finite-type/coherent or locally-free condition was substituted.
- Pullbacks f-star F and f-star G: `(tensorPullback f).obj F` and `.obj G`. Correct, using the recorded tensor-formula pullback and the normalized `exists_tensorPullbackAdjunction` unit. Mathlib's different `Modules.pullback` is not used.
- Nonnegative cohomological degrees: `p q : ℕ`, with output `p + q`. Correct, including degree zero.
- Cech and sheaf cohomology: `(cechComplexFunctor U).obj F.presheafModuleCat`, its `.homology p`, and `(RingedSpace.moduleCohomology X.toRingedSpace p).obj F`. Correct; cohomology is the shared right-derived global-sections functor on O-modules, not abelian-sheaf Ext or field-linear cohomology.
- Canonical comparison maps on every cover: `cF`, `cF'`, `cG`, `cFG`, each guarded by `IsModuleCechComparison` as a **hypothesis**. Correct. Existence for every cover is already stated by the imported `cechComparisonMapNaturality`; we do not impose invertibility. The original universal `cF'` was incorrectly required to be canonical in the conclusion.
- Clause (a), the *refinement cochain map* and its induced map: `gamma` is a cochain morphism between the underlying additive complexes, guarded by `IsCechRefinementMap f U U' refine hrefine F gamma`. That predicate pins every tuple component to pullback by the adjunction unit, followed by restriction to the specified refined intersection. `exists_unique_cechRefinementMap` states existence and uniqueness without any extra cover assumptions. `cechRefinementHomology gamma p` transports the induced homology map through the canonical forgetful homology comparisons. Correct.
- Clause (a), commutation with the *usual* pullback: the first conjunct is `cechRefinementHomology gamma p ≫ forget.map cF' = forget.map cF ≫ moduleCohomologyPullback f F p`. Correct. Forgetting scalars is needed because the global rings of X and X' differ; it adds no mathematical hypothesis.
- Clause (b), the signed Cech cochain product: `cechCupCochain` uses the front indices 0,...,p and back indices p,...,p+q, restricts both factors to the full intersection, and calls the existing `tmulSection`. The shared vertex occurs in both factors. `cechCupCochain_leibniz` states the differential identity with sign `(-1)^p`. Tag 07MB explicitly says its component sign is +1 when coefficient complexes are sheaves in degree zero; no missing sign was suppressed. Correct specialization of the node's cochain map, with no alternative complex introduced.
- Clause (b), the induced tensor product map: `cup` is a nested `Γ(X, ⊤)`-linear map, guarded by `IsCechCupProduct`. That predicate fixes its value on every pair of cocycle classes to the class of `cechCupCochain`; `exists_unique_cechCupProduct` states that it exists uniquely. A bilinear map is exactly the tensor-product map by the tensor universal property. Correct; two arbitrary unary maps are not substituted for a tensor product.
- Clause (b), the *usual* sheaf cup product: `sheafCup` is a nested global-section-linear map guarded by `IsModuleCupProduct`. The predicate computes its value on every pair of global cocycles in any computing resolution pairing. Those pairings are O-linear on opens, commute with restrictions, obey signed Leibniz, and extend `tmulSection` on the coefficient augmentations. The cohomology classes use a comparison extending the augmentation into an injective resolution and `isoRightDerivedObj`, not an arbitrary isomorphism. The existence/uniqueness statement uses Godement resolutions and the derived-tensor definition from the source. Correct; no compatibility with Cech products is built into this definition.
- Clause (b), comparison compatibility: the second conjunct is `∀ a b, cFG (cup a b) = sheafCup (cF a) (cG b)`. Correct for every open cover, without assuming comparisons are isomorphisms.
- The 'in particular' clause: the third conjunct quantifies `IsIso cF`, `IsIso cG`, `IsIso cFG` only for the inverse-comparison identity `cup (inv cF a) (inv cG b) = inv cFG (sheafCup a b)`. Correct. The finite-affine/affine-diagonal example is the existing affine comparison-iso material, not a restriction on the compatibility theorem.
- Naturality in F and G: `cechRefinement_coefficient_naturality` states the degreewise refinement/coefficient equation; `cechCup_coefficient_naturality` states the Cech product/coefficient equation; `moduleCup_coefficient_naturality` states the sheaf product/coefficient equation. Together with the already-landed comparison-map naturality these make both comparison squares natural. Correct; the old `∀ φ : F ⟶ F, φ = φ` expressed none of this.
- Naturality for pullback f: `moduleCup_pullback_naturality` states the product of pulled-back classes equals pullback of their cup, followed by the **existing**, section-normalized `module_pullback_tensor` coefficient comparison. Together with clause (a) and the tuple formula this renders the node's pullback naturality. Correct; no field hypothesis is added.

Source reading: I read the actual Stacks Cohomology TeX at `lemma-functoriality-cech` (01FD), `equation-needs-signs` (07MB), `section-cup-product`, and `lemma-diagrams-commute` (0FKV), including their proofs. 01FD assumes arbitrary ringed spaces, open coverings, and a specified f-map; the node specializes it to schemes and the tensor-pullback unit. 07MB gives the total signs and explicitly reduces to the unsigned front/back component for sheaves in degree zero. 0FKV assumes bounded-below coefficient complexes and an arbitrary covering, and uses Godement resolutions. The sheaves F[0], G[0] meet bounded-below automatically. The sheaf cup characterization uses exactly the usual map from derived tensor to ordinary tensor: its map to a degree-zero coefficient is fixed by the degree-zero augmentation. Computing resolutions are data used inside the definition's universal characterization, **not** extra hypotheses on X, F, G in the compatibility statement.

Dependency signature audit: I opened `ModuleCechComparison` (the resolution-pinned `IsModuleCechComparison`), `CechComparisonMapNaturality` (existence for arbitrary covers plus guarded coefficient naturality), `ModuleCohomologyFMap` (resolution construction and pullback of the normalized adjunction unit), `TensorPullback` and `TensorPullbackAdjunction`, `RingedSpaceModuleCohomology`, `ModulePullbackTensor` (its naturality and section-normalization clauses), and `Coherent`. I also inspected the source `TensorSection` and `CechComparison`: the existing `tmulSection` and the categorical-product-to-tuple equivalence are reused. The existing `def-pur-sheaf-tensor-product` serves the tensor notion; the old sandbox's `schemeModuleTensorProduct` was an unnecessary duplicate and was removed. The affine-only `moduleCechComparison_natural_affine` was read and is not used to claim an arbitrary-cover result. The total tensor sign agrees with `CochainComplex.mapBifunctor` recorded on `def-pc-tensor-complex-sheaves`.

New-node audit: all three new nodes were rewritten as self-contained mathematical definitions with explicit objects, formulas and dependency citations, instead of the worker's one-sentence placeholders. `def-sc-cech-refinement-cochain-map` now carries the actual tuple-constrained cochain map, not a generic square equation. `def-sc-cech-cup-product` carries the front/back section-tensor formula and its induced bilinear quotient map, not a sum of unary maps. `def-sc-module-cohomology-cup-product` now carries the missing genuine sheaf cup-product characterization, not a duplicate tensor object. Each has the required source, search records, empty proof/proof_deps, provenance, blueprint route, audit states, chapter/unit and Lean record. Auxiliary statements required for the constructions are named theorems with `sorry`, source and complete natural-language proofs; no data definition contains `sorry`. No dependency module was needed: the landed APIs were usable.

Edge cases: empty cover indices are allowed (cover hypotheses force the scheme to be empty); repeated indices are allowed and no ordering is imposed. Zero modules, empty schemes and zero global-section rings are not excluded. The bilinear and refinement formulas still make sense for empty products and zero sections. At p=0 or q=0 the front/back formulas share the correct endpoint, and `(-1)^0=1`. There is no characteristic assumption. All four modules declare their own universe variables and disable auto-implicit binders; no independent low universe is used for test algebras or schemes. Index types are in the existing Cech API's scheme universe, which can be chosen as large as needed. I specifically removed the old tensor module's unbound `u₁` (it declared `u₃` and accidentally compiled only because combining siblings supplied `u₁`).

Independent searches: LeanFinder queries `Alexander Whitney product sheaf cohomology tensor pairing` and `Sheaf cohomology multiplication computed by acyclic resolutions` returned sheaf tensor objects, ordinary abelian-sheaf H, and nonabelian degree-one cochain multiplication, none of the required constructions. Loogle queries `Cech cup product` and `Presheaf tensor sections cup product` returned no hits and unknown-identifier diagnostics. LeanSearch query `Sheaf cohomology cup products for modules on ringed spaces` was unavailable (Internal Server Error), recorded as unavailable rather than as no match. I ran `rg` using cupProduct/cup_product/CupProduct, Alexander/Whitney, Godement/godement, refinement, and tensor-section terms over Mathlib, WeilConjectures, Sheaf and DAG nodes. Existing Cech complexes, tensor objects, `tmulSection`, module cohomology and the canonical comparison API were reused. `FieldLinearModuleCohomologyOperations.scalarCohomologyCup` was opened: it requires a field and a scheme morphism to Spec k and cannot replace this arbitrary-scheme statement. No existing arbitrary-scheme Cech refinement or ordinary module-cohomology cup API was found.

Mismatches repaired: false universal claims about arbitrary gamma and cF'; missing canonical construction of refinement; `True` replacing all of clause (b); `φ = φ` replacing naturality; the unary-additive 'cup compatibility' definition; duplicate scheme tensor object; the tensor module's unbound universe; placeholder new-node statements with missing objects/dependencies; missing module docstrings and incomplete proof documentation. The item Lean record now lists the main comparison theorem and the four explicit naturality statements, and its main signature is extracted verbatim from the file. The item's statement was not weakened or otherwise changed.

The inherited 2026-10-11 statement correction was checked against 0FKV: arbitrary-cover compatibility, rather than an unconditional comparison isomorphism, is exactly the source. There is only **one** direct DAG citer: `lem-sc-picard-kunneth-qcoh`; I read its Steps 1, 3, 7 and 8, and its use still holds (finite affine covers make the comparisons isomorphisms; arbitrary pullback covers need only compatibility). As a second downstream check I read `lem-sc-picard-h1-product-injective`; its slice-pullback argument uses Kunneth naturality and still holds. There is no new statement correction in this delivery, and no citer was edited.

Validation: all four delivery modules were compiled together locally, cleanly, with no errors or warnings. Every theorem body is `by sorry`; every data definition is an explicit construction, and the characterizing predicates do not assume the compatibility theorem they are intended to state. Final server compile and preflight results are recorded after the delivery dry run.

Final validation: `deliver2.py --no-push` printed OK: all four modules compile on the project server and the stage-2 preflight passes. The blueprint via paths were then aligned with the item’s exact ancestor route and checked again before pushing.

Additional search hit checked: upstream `AlgebraicGeometry.Etale.cupProduct` and `cupProductAux` in TraceCup operate on shifts of the tensor unit in the étale derived category, not arbitrary O_X-modules in the recorded Zariski module cohomology. Upstream `TopCat.Presheaf.godement` is the additive Godement presheaf, not the module-cohomology cup pairing. Neither is redeclared here. The final provenance check uses the full ancestor route computed by the current-base preflight, which is longer than the route stored in the item copy.

Dependency-record precision: the general `SiteCechComplex` API also exists, but the module-valued open-cover complexes in this delivery use the existing specialized `cechComplexFunctor U` encoding pinned by `def-sc-module-cech-comparison`; the two new Cech nodes cite that specialized node directly. No copy of the general-site complex was introduced.

## Repair validation

The four compilation units were checked separately on the project server in the dependency order recorded by `scompile.combine`: `CechRefinementCochainMap`, `ModuleCohomologyCupProduct`, `CechCupProduct`, `CechCupPullbackCompat`. For the two modules importing delivery siblings, the scratch compilation unit prepends just the required sibling bodies and removes those sibling imports, as prescribed by brief-stage2 §6; no sibling was landed or installed. The original module files remain separate in the delivery. Each server invocation uses `compile_remote.sh` and its unchanged default 120-second limit.

- `CechRefinementCochainMap`: exit 0, 3.3 seconds, no errors or warnings.
- `ModuleCohomologyCupProduct`: exit 0, 6.2 seconds, no errors or warnings.
- `CechCupProduct` with its required cup-resolution sibling: exit 0, 6.9 seconds, no errors or warnings.
- `CechCupPullbackCompat` with its three required siblings: exit 0, 23.1 seconds, no errors or warnings.


## Second reading by T1

Independent reading of the current X-20c63 repair, 2026-10-12. I opened the item,
all four delivered modules, the three new definition nodes, and the recorded
statement dependencies. This section certifies the current files, including
`cechRefinement_composition_naturality`; the earlier readings above do not.

Source first: the repository has no local cohomology.tex. I fetched the Stacks
project's cohomology.tex into this item's scratchpad and read
`lemma-functoriality-cech`, `equation-needs-signs`, `lemma-diagrams-commute`, and
`section-cup-product`, with their surrounding hypotheses and proofs. 01FD is
for ringed spaces, arbitrary open covers, a specified refinement, and an f-map.
Here the f-map is the tensor-pullback unit. 07MB explicitly says the component
sign is +1 when the first coefficient is a sheaf in degree zero; its Leibniz
sign is still (-1)^p. 0FKV applies to bounded-below complexes and arbitrary
covers; F[0] and G[0] meet boundedness without added assumptions. The inherited
statement correction agrees with 0FKV: compatibility always, identification
only for invertible comparisons. No new correction to the node is needed.

Object, hypothesis and conclusion checklist (each verdict is against the node):

- Schemes and their morphism: `X X' : Scheme.{v}`, `f : X' ⟶ X`. PASS:
  arbitrary schemes, with no base field, separation or Noetherian assumption.
- The cover U of X: `{ι : Type v}`, `U : ι → X.Opens`, `hU : iSup U = ⊤`.
  PASS: no finite-index or affine assumption.
- The cover U' of X': `{ι' : Type v}`, `U' : ι' → X'.Opens`, `hU'` with
  the same covering equation. PASS.
- The specified refinement: `refine : ι' → ι` and
  `hrefine : ∀ i, U' i ≤ f ⁻¹ᵁ U (refine i)`. PASS: the particular function,
  rather than mere existence of some refinement, determines the map.
- Coefficients: `F G : X.Modules`, `[F.IsQuasicoherent] [G.IsQuasicoherent]`.
  PASS: the existing quasi-coherent notion, not coherent or finite type.
- Pullback coefficients: `(tensorPullback f).obj F` and likewise G. PASS:
  recorded tensor-formula pullback, using the normalized adjunction unit.
- Degrees: `p q : ℕ`, target `p + q`. PASS, including either degree zero.
- Cech cochains/cohomology: `(cechComplexFunctor U).obj F.presheafModuleCat`
  and `.homology p`. PASS: the specialized module-valued Cech encoding of
  def-sc-module-cech-comparison, not a privately defined complex.
- Sheaf cohomology: `RingedSpace.moduleCohomology X.toRingedSpace p`. PASS:
  derived global sections of modules, over Γ(X, ⊤).
- Canonical comparisons: cF, cF', cG, cFG with `IsModuleCechComparison`.
  PASS: the predicate fixes them by alpha, beta and the resolution comparison.
  Their existence on arbitrary covers is the imported
  `cechComparisonMapNaturality`, not an extra mathematical assumption.
- The refinement cochain map: gamma with `IsCechRefinementMap`. PASS:
  the predicate fixes every tuple component to pullback by the unit followed
  by restriction; `exists_unique_cechRefinementMap` supplies existence.
- Clause (a): first conjunct
  `cechRefinementHomology gamma p ≫ forget.map cF' =
  forget.map cF ≫ moduleCohomologyPullback f F p`. PASS: the usual pullback,
  and the scalar-forgetting homology identifications are canonical. No
  equality of the two global rings is assumed.
- Clause (b), cochain construction: `cechCupCochain`, front/back restrictions,
  and `cechCupCochain_leibniz`. PASS: shared vertex p, section tensor product,
  and precisely the total-tensor differential sign of 07MB.
- Clause (b), induced product: cup with `IsCechCupProduct`. PASS: bilinearity
  is the tensor-product universal property; the values on cocycle classes
  are fixed by the actual cochain formula. Existence/uniqueness is stated.
- The usual sheaf cup: sheafCup with `IsModuleCupProduct`. PASS: computing
  resolutions, sectionwise bilinear chain pairings and augmentation determine
  it; the classes use injective-resolution comparisons. The characterization
  does not assume the Cech compatibility conclusion.
- Comparison compatibility: second conjunct `∀ a b,
  cFG (cup a b) = sheafCup (cF a) (cG b)`. PASS: arbitrary covers.
- In particular: third conjunct has IsIso cF, IsIso cG, IsIso cFG only inside
  the inverse-comparison identity. PASS: no invertibility assumed for (a)
  or (b); the finite-affine-cover example is not a restriction of the theorem.
- Naturality in coefficients: `cechRefinement_coefficient_naturality`,
  `cechCup_coefficient_naturality`, `moduleCup_coefficient_naturality`, plus
  the existing comparison-map naturality. PASS: actual map equalities.
- Naturality of the sheaf cup under f: `moduleCup_pullback_naturality`.
  PASS: uses the section-normalized `module_pullback_tensor` comparison.
- Naturality of the Cech cup under f: missing as an explicit equality in the
  worker's current file. REPAIRED by `cechCup_refinement_naturality`, fixing
  all three gamma maps by their tuple predicates and identifying gammaFG of
  the cup with the cup of gammaF and gammaG through module_pullback_tensor.
  This states exactly Step 4's cochain square and works for non-cover families
  too, as the tuple formula requires no covering condition. It descends by
  Leibniz, independently of any injectivity of comparison maps.
- Composition naturality: `cechRefinement_composition_naturality` quantifies
  f₁, all three covers, both specified refinements, and their composite index
  function `refine ∘ refine₁`. PASS: hrefineComp follows from hrefine and
  hrefine₁, so adds no geometric restriction. First conjunct composes cochain
  maps through `(tensorSectionsComp f₁ f).hom.app F`; second conjunct gives
  its comparison square; third composes the usual cohomology pullbacks through
  the same coefficient identification. All three arrows have the correct
  direction. I read tensorSectionsComp itself: it is the conjugate of
  pushforwardComp under the normalized adjunctions, not an arbitrary iso.

Dependency and new-node audit: I read ModuleCechComparison, the current
CechComparisonMapNaturality signature, TensorPullback and its adjunction,
ModuleCohomologyFMap, RingedSpaceModuleCohomology, Coherent, ModulePullbackTensor,
and EtaleTensorSections. The affine-only comparison-natural dependency is
not substituted for arbitrary-cover comparison. The underlying tensor is the
existing sheaf tensor product; `tmulSection` and the tuple equivalence come
from upstream TensorSection and CechComparison. All three new nodes are
self-contained and match their modules: refinement is the 01FD component
rule; Cech cup is the degree-zero 07MB formula; module cup is the usual
resolution-computed product. Their dependencies, source fields, creation,
chapter/unit, empty proof fields and ancestor routes are present. No dependency
module is needed. I checked the resolution-pairing characterization against
the derived definition: any such augmented pairing induces the canonical map
F tensor-derived G to F tensor G, since it is determined by H-zero; Godement
pairings supply computing resolutions, so the characterization is nonvacuous.

Edge cases: empty indices are admitted (a covering equation then forces the
empty scheme), repeated indices and noninjective refinements are admitted,
zero modules and empty opens are admitted, and no characteristic is excluded.
At p=0 or q=0 the front/back tuple shares the correct endpoint and the Leibniz
sign at p=0 is +1. The composition comparison handles identity maps and
successive pullbacks without asserting literal equality of coefficient objects.
Every module declares its own universe and disables autoImplicit. Index types
use the existing Cech API's scheme universe; it can be enlarged to accommodate
any given small family. There is no independent low test-object universe.

Independent searches: LeanFinder query `Alexander Whitney pairing Cech
complexes refinement composition sheaf modules` returned eight Dold--Kan
summand-map identities, none the desired statement. Loogle `CechComplex
cupProduct` returned zero hits with an unknown-identifier diagnostic, not a
proof of absence. LeanSearch `Refinement of open coverings induces a cochain
map compatible with cup products` returned service unavailable. I also ran
rg for cupProduct/cup_product/CupProduct, Alexander, Whitney, cechRefinement,
tensorSectionsComp, and refinement over Mathlib, upstream WeilConjectures,
Sheaf and the DAG. I opened the two relevant apparent cup hits:
scalarCohomologyCup requires a field and a structure map to Spec k; upstream
Etale.cupProduct concerns shifts of the unit in the etale derived category.
Neither is this arbitrary-scheme O-module product. Existing tensor sections,
Cech complexes, cohomology and pullback composition are reused, not redeclared.
No other DAG definition supplies the three new notions.

Citers of the inherited correction: the sole direct citer is
lem-sc-picard-kunneth-qcoh, whose affine-cover comparison and pullback/cup
steps still hold. I also opened lem-sc-picard-h1-product-injective: its slice
calculation uses Kunneth pullback naturality and still holds. No citer changed.

Changes of this reading: added the missing Cech cup/refinement equality with
its source and componentwise proof documentation, and listed its declaration
in the item's lean record. No existing mathematical signature, definition,
node statement or inherited correction was rewritten. All theorem proofs
remain sorry; all data definitions have explicit bodies. Docstrings carry
sources and blueprint ids. Main lean.statement was checked byte-for-byte
against the signature before `:= by`; every line is within 100 characters.

Local validation: all four delivered modules compiled together in dependency
order, exit 0 in 23.6 seconds, with no errors or warnings. Server compilation
and preflight are performed by the delivery dry run below.
