## Worker report

Module: `Sheaf.AlgebraicGeometry.SpaceSupportedAdicExistence`.
Main declaration: `AlgebraicGeometry.AlgebraicSpace.supportedAdicRestriction_isEquivalence`.
The natural-language statement is unchanged. The returned-delivery repair adds the two already-landed statement dependency owners listed below. All new declarations belong to the two categories and canonical restriction functor explicitly introduced by this node; there is no additional independent notion or dependency repair.

### Hypothesis and clause correspondence

- The ambient scheme is the explicit section variable `{S : Scheme.{u}}`. Algebraic spaces are the existing `AlgebraicSpace S`, not schemes or arbitrary categories. Site objects remain in universe `u+1`, site morphisms and module sections in `u`, as in the recorded framework. No universe equality or smallness hypothesis is added.
- The coefficient ring is `{A : Type u} [CommRing A]`; Noetherianity is `[IsNoetherianRing A]` on the theorem. The ideal is `(I : Ideal A)`.
- Completeness is `[IsAdicComplete I A]`. Mathlib's `AdicCompletion.of_bijective_iff` identifies this with bijectivity of the canonical map to compatible quotient sequences. This is the ring isomorphism condition in the node; indexing the positive quotients by `n+1` does not change that inverse limit.
- The specified structural map of the affine base is `(a : Spec (.of A) ⟶ S)`. The existing `schemeSpace (Over.mk a)` regards exactly this scheme over S as an algebraic space.
- The space and morphism are `{Y : AlgebraicSpace S}` and `(p : Y ⟶ schemeSpace (Over.mk a))`. The theorem has precisely `(hsep : MapIsSeparated p)` and `(hft : MapIsFiniteType p)`.
- `supportedAdicBase a I n` is `Spec(A/I^(n+1))`, with the composite specified map to S. `supportedAdicThickening a I p n` is the actual existing `properQuotFibre` sheaf pullback `Y ×_A Spec(A/I^(n+1))`. No arbitrary model or extra pullback hypothesis is used.
- `supportedAdicQuotientStep` is `Ideal.Quotient.factor` for `I^(n+2) ≤ I^(n+1)`. Applying contravariant `Spec.map` and the existing `properQuotFibreMap` gives `supportedAdicStep`, the canonical adjacent closed immersion. `supportedAdicProjection` is the existing first projection to Y.
- The module categories are the existing `X.Modules` on the small etale structure sheaves. Quasi-coherence is Mathlib's `SheafOfModules.IsQuasicoherent`, exactly the predicate underlying the recorded `QCoh`. Finite presentation is Mathlib's `SheafOfModules.IsFinitePresentation`: its docstring and local presentation data give precisely the finite free presentation in the node.
- `SupportedAdicProperSupport p M` is the specified closed-carrier condition: `∃ Z i`, representability by closed immersions on scheme tests, `MapIsProper (i ≫ p)`, and `∃ G`, `G.IsQuasicoherent ∧ G.IsFiniteType ∧ Nonempty ((moduleDirectImage i).obj G ≅ M)`. It packages the identical inline condition in the recorded `ProperQuotient.properSupport`; it does not use Quot's separate flatness condition. The existing `CoherentAdicHasProperSupport` only specializes the first term of a diagram over the particular base `Spec A`, so cannot express the module condition with the arbitrary specified map to S and the two different bases needed here.
- `SupportedAdicModules p` is D: the full subcategory of `Y.Modules` for quasi-coherence, finite presentation, and this support condition. Its arrows are all module homomorphisms, without an extra condition on the arrows or the carrier choices.
- `SupportedAdicFamilies a I p` is the dependent product of the actual level module categories. `supportedAdicShift` sends `(F_n)` to `(j_n^* F_(n+1))` using the existing `moduleTensorPullback`, on both objects and arrows. An object of Mathlib's `Endofunctor.Algebra` for this shift is exactly a family with adjacent maps `j_n^* F_(n+1) → F_n`. `IsSupportedAdicSystem` requires every such map to be an isomorphism and every term to be quasi-coherent and finitely presented, and imposes `SupportedAdicProperSupport` on the zeroth component over `properQuotSnd p (supportedAdicTest a I 0)`. This is the first positive level over `Spec(A/I^1)`, canonically `Spec(A/I)`, rather than support over A or support on every level as an additional hypothesis.
- `SupportedAdicSystems` is the full subcategory for that predicate. Mathlib's algebra morphism equation `shift.map f ≫ G.str = F.str ≫ f` is precisely, component by component, the commuting square required for the families of module maps. Its category structure already has componentwise identities and composition. Replacing explicitly stored isomorphisms by their hom maps with `IsIso` loses no information: inverses are unique.
- `supportedAdicRestriction` is the actual tensor restriction functor D → D-hat. On objects it has components `(moduleTensorPullback (supportedAdicProjection ... n)).obj M`; on arrows it applies those same tensor functors to the input homomorphism. Its transition is `supportedAdicRestrictionIso`: the existing tensor-normalized `moduleTensorComposition`, followed by transport along the existing `properQuotFibreMap_fst` triangle. Thus neither the functor nor its transition maps are selected from an unnormalized existence statement. `supportedAdicRestriction_admissible` supplies only the proof that this construction lands in the specified full subcategory.
- The conclusion `(supportedAdicRestriction a I p).IsEquivalence` asserts exactly that the specified functor is an equivalence (fully faithful and essentially surjective), not that the two categories admit some unrelated equivalence.
- No flatness predicate occurs in any input module, system condition or theorem binder. No properness of p, nonemptiness, nonzero-ideal hypothesis, or flatness of a quotient-base transition is imposed.

### Dependencies used

All namespaces below are `AlgebraicGeometry.AlgebraicSpace` unless qualified otherwise.

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `AlgebraicGeometry.Spec`, `AlgebraicGeometry.Spec.map`.
- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`; `Mathlib.RingTheory.AdicCompletion.Basic`: `IsAdicComplete` and its canonical-map interpretation.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`, `IsRepresentableWith`, `Modules`, `structureSheaf`, the existing small etale sites.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule`: the existing slice instances needed for the exact Mathlib quasi-coherence and finite-presentation predicates; `QCoh` is the corresponding full subcategory.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations`: `moduleDirectImage`, `moduleTensorPullback`, with their specified chart-limit/adjunction normalization.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties`: `MapIsSeparated`, `MapIsFiniteType`, `MapIsProper`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers`: `fibreProduct_isAlgebraicSpace`, used through the recorded pullback construction.
- `Sheaf.AlgebraicGeometry.SpaceProperQuotFunctor`: `ProperQuotTest`, `properQuotFibre`, `properQuotFst`, `properQuotSnd`, `properQuotFibreMap`, `properQuotFibreMap_fst`; its inline closed-carrier convention is retained verbatim as a predicate on a module. `schemeSpace` comes from its existing enlarged-site import, and `moduleTensorComposition` from its existing normalized tensor comparison import.
- `Mathlib.CategoryTheory.Pi.Basic`: `Pi.comap`, `Functor.pi`, `Functor.pi'`, and the dependent product category.
- `Mathlib.CategoryTheory.Endofunctor.Algebra`: `Endofunctor.Algebra`, its algebra morphisms and category; `ObjectProperty.FullSubcategory` and `ObjectProperty.lift` provide the two finiteness/support restrictions.

Every presently recorded proof-dependency module is imported without `public`: `SpaceCoherentAdicSystem`, `AlgebraicSpaceAffineChartCalculus`, `FiniteModuleComplete`, `AlgebraicSpaceFlatProperFpLocality`, `ModuleSupportProperOverBase`, `SchemeZariskiEtaleQuasiCoherentEquivalence`, and `ChowAlgebraizationCore`. The module-operations dependency is already a public statement import. Unstated proof prerequisites have no module to import and are not needed to formulate this statement.

### Proof obligations and real data

All definitions have actual data. The named postponed obligations are `supportedAdicBaseStep_w`, `supportedAdicTestStep_w`, `supportedAdicRestrictionMap_w`, `supportedAdicRestrictionLaws`, `supportedAdicRestriction_admissible`, and the main `supportedAdicRestriction_isEquivalence`. Each belongs to this node's specified canonical functor or theorem, has the node's blueprint tag and its own natural-language proof docstring. The main theorem's docstring includes all eight proof steps from the node. No anonymous sorry occurs in a definition, no object is chosen from a bare existence theorem, and no proof is completed in this stage.

### Edge cases

Checked the empty space and zero module/system: no nonemptiness or nonzero requirement enters either category or the functor. The empty closed carrier realizes proper support of zero. Checked `I = 0`: positive thickenings are canonically Y and all adjacent restriction maps are invertible, so the expected constant-system equivalence is included. Checked `I = ⊤`: completeness forces A to be the zero ring (Mathlib `IsAdicComplete.subsingleton`), so the corresponding base and spaces are empty; the statement has no spurious exclusion of that case. Nilpotent ideals and the zero ring are also included. Index zero means level one; no unrequested `Y_0`, `F_0`, or compatibility with it is imposed. A nonflat finite presented module, for example the residue field over a complete DVR, satisfies the finiteness clauses; hence flatness was not silently inserted. The closed-carrier definition and quotient transitions require no flatness.

### Searches

- `msearch.py ... leanfinder "Grothendieck existence equivalence coherent modules proper support algebraic spaces complete Noetherian ring"`: eight hits, mostly condensed module categories and `SheafOfModules.IsFinitePresentation.exists_quasicoherentData`; no algebraic-space existence equivalence.
- `msearch.py ... leansearch "category of systems of finitely presented sheaves on algebraic spaces Grothendieck existence"`: eight hits including `SheafOfModules.isFinitePresentation` and finite presentation data, but no such equivalence or adic-system category on varying spaces.
- `msearch.py ... loogle "IsAdicComplete"`: twelve hits, including `IsAdicComplete`, `AdicCompletion.of_bijective`, and the canonical completeness equivalences. Reused the existing predicate rather than introducing a completion definition.
- `msearch.py ... grep "Grothendieck.*existence|proper.*support" AlgebraicGeometry`: zero Mathlib hits.
- `rg` in `lean/WeilConjectures` for the item id found no declaration. Searches for adic existence and proper-support definitions found the scheme-only coherent-formal-module API and `Scheme.Modules.HasSupportProperOver`; these concern schemes, not the statement's algebraic spaces.
- `rg` in `lean/Sheaf/AlgebraicGeometry` for adic functors, finite presentation and proper support found `SpaceCoherentAdicSystem` and `SpaceProperQuotFunctor`, whose declarations were read. The former is diagrams on the single space over the particular base `Spec A`; the latter provides the actual fibre products and the identical inline carrier condition. Neither states this equivalence or supplies the two categories in Tag 08BF. They were reused as imports and constructors, without replacing their objects or module operations.
- Name searches for `SupportedAdicProperSupport`, `SupportedAdicModules`, `supportedAdicThickening` and `supportedAdicRestriction` across Mathlib, `lean/WeilConjectures`, and `lean/Sheaf` found no existing declarations.
- Read Stacks `spaces-more-morphisms.tex`, `theorem-grothendieck-existence` and `remark-reformulate-existence-theorem` (08BE/08BF), including the proof and the three object conditions in the unwound statement. These agree with the node.

### Validation

`scompile.py` compiled both the sandbox module and its final library path cleanly against the live published library. The final preflight and delivery are run through `deliver2.py`; no direct git mutation or build command is used. No statement dispute or source correction was needed.


## Returned-delivery repair

Repaired H2 from the independent review of immutable head `951f9080f471`:

- Added `def-sfb-space-module-tensor-composition` to `stmt_deps`. Its existing declaration is `AlgebraicGeometry.AlgebraicSpace.moduleTensorComposition`, in `Sheaf.AlgebraicGeometry.SpaceFlatDirectImageBaseChange`; `supportedAdicRestrictionIso` uses exactly this normalized composition isomorphism.
- Added `def-trf-scheme-algebraic-space` to `stmt_deps`. Its existing declaration is `AlgebraicGeometry.AlgebraicSpace.schemeSpace`, in `Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite`; the type of `p` and `supportedAdicTest` use exactly this representable-scheme construction.

Read both current landed node records and their declaration signatures/docstrings. Both have `existing: true` records. These additions use STMT_DEPS MAY GAIN LANDED NODES and do not require a statement correction. Compared the retained sandbox node with the current main node: the mathematical statement, proof and proof dependencies agree. The repaired delivery retains the Lean module and Lean record from the returned head byte for byte; the node repair consists only of adding the two missing dependency IDs. The existing public import of `SpaceProperQuotFunctor` already makes both owning modules public through its public imports, so no Lean import change is necessary. Compilation, dry run and delivery are repeated against the current live base by the authorized wrappers.

## Second reading by N8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
