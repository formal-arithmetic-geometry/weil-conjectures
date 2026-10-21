## Worker report

The module `Sheaf.Paper.PurAdicLineSystemBaseChange` states
`CategoryTheory.purAdicLineSystem_baseChange`, with its proof `sorry`.
Its other declarations are data structures, predicates, or explicit composites of existing
isomorphisms that package this node's diagrams and normalization equations. They introduce
no alternative sheaf, module category, inverse image, localization or tensor product.
There is no definition with postponed data and no auxiliary theorem with `sorry`.
The original unfinished draft and report were retained; the old report is saved in
`.report-before-resume` for resumption history.

Source read: current blueprint
`literature/blueprint/main-20261015/blueprint/sec-smooth-purity/sk-prop-an/sk-prop-sfb-cartesian-coefficients-twists.proof.md`,
Integral twist and Rational and algebraic closure paragraphs, together with the item's
full ten-step expanded proof and the existing free-tower comparison. The module docstring
identifies this blueprint source and Sites 03CF. The theorem docstring records all ten
proof steps, including both the sequential and tensor localization descriptions and the
common-upper-bound scalar construction. No statement correction is needed.

### Hypotheses rendered

| Node hypothesis | Lean rendering |
| --- | --- |
| Sites C,D small relative to a larger sheaf universe | Independent `uC`, `vC`, `uD`, `vD`, `w`; `Category` and `EssentiallySmall.{w}` binders. All rings, modules and set sheaves take values in universe `w`. Sheafification and locally bijective-equivalence instances are the standard small-site infrastructure, not extra mathematical restrictions. |
| Site coverings and finite limits on both sites | `J K : Precoverage`, `_hJ : J.IsSiteForCoverings`, `_hK`, and `HasFiniteLimits C`, `HasFiniteLimits D`. These use the recorded corrected covering-presieve site convention. |
| u preserves finite limits and coverings | `U : C ⥤ D`, `PreservesFiniteLimits U`, `_hUcover`. |
| L is the geometric inverse image of u | `U.IsContinuous`, `_adj : L ⊣ U.sheafPushforwardContinuous ...`, and `PreservesFiniteLimits L`. The adjunction characterizes the Kan-extension/sheafification inverse image up to its unique adjunction-compatible isomorphism. Continuity and left exactness are the stated geometric-inverse-image structure supplied by the dependency, not an arbitrary functor. The adjunction also supplies colimit preservation. |
| Nonempty directed poset I in the sheaf universe | `I : Type w`, `PartialOrder I`, `Nonempty I`, `IsDirected I (· ≤ ·)`. |
| Positive stride e_i | `e : I → ℕ`, `_he : ∀ i, 1 ≤ e i`. Natural-number index n denotes the positive level n+1. `purAdicStride e` sends n to e*(n+1)-1. |
| Full ring towers R_i,m and S_i,m | `A.full`, `B.full : I → ℕᵒᵖ ⥤ Sheaf ... CommRingCat.{w}`. All transition composites are functorial, with no assumed surjectivity. |
| Their full limits R_i,S_i | `A.integral.R`, `A.rπ`, `A.rlimit`, and their B counterparts. `IsLimit` is the existing categorical universal property; it does not assume L preserves a limit. |
| Full compatible ring isomorphisms a_i,m and a_i with specified projections | `a.full`, `a.integral`, `a.full_natural`, `a.projection`. The existing `SheafOfModules.AlgebraicInverseImage.ringUnderlying` is a ring comparison because its graph equations preserve addition, multiplication, zero and one. |
| B_i,n = R_i,e_in and the primed version | `A.levels.R`, `B.levels.R` and `A.subsequence`, `B.subsequence` identify them with `purAdicStride (e i) ⋙ full i`. `a.subsequence` identifies the ring comparison used by c with the corresponding full comparison. |
| Module towers with semilinear transitions | `A.levels.M`, `B.levels.M` are the recorded `ringedSiteModules` over the corresponding rings; `levels.P` is their abelian-sheaf presentation, `identify` its isomorphism, and `semilinear` is the full sectionwise scalar equation for every diagram arrow. |
| Compatible semilinear level isomorphisms c_i,n | `c : PurAdicPairComparison L A.levels B.levels`; its `a`, `c` fields use the graph-normalized `AlgebraicInverseImage` and actual linear module isomorphisms. `ring_natural` and `module_natural` impose every diagram square. `purAdicModuleIso` is their underlying set-sheaf composite. |
| One common cover for each i and compatible bases on slices | `_bases : PurAdicLineLocallyBased J A` quantifies one family `(Q,V,v)` for each i, requires `Presieve.ofArrows V v ∈ J (⊤_ C)`, and gives a basis isomorphism for every n on `SheafOfModules.over` over `J.over (V j)`. The displayed equation on every `W : Over (V j)` is exactly t_n b_(n+1) = b_n rho_n. It does not allow a different cover for each n. |
| M_i,N_i are inverse limits, with the subsequence scalar actions | `A.integral.P`, `A.pπ`, `A.plimit` and B; `projection_smul` identifies the actual module action under every projection with the subsequence ring projection. Thus the integral actions are fixed, rather than arbitrary actions on a chosen underlying limit. |
| Specified directed pair diagrams and their induced limit maps | `levels` is a single diagram on `I × ℕᵒᵖ`, so i-maps commute with tower maps. `integral` is a pair diagram on I; `rπ_natural` and `pπ_natural` fix its ring and module maps. `a.integral_natural` imposes compatibility of the given full coefficient comparisons with these maps. Varying strides are retained. |
| Compatible global sections and s'_i = a_i(Ls_i) | `s`, `s'` are actual presheaf sections, `_hs` is compatibility of s. `_hsection : IsInverseImageSection ...` is the existing generalized-element equation for inverse images of sections. Compatibility of s' follows from that equation and coefficient naturality; it is not added as a separate hypothesis. |

### Conclusions rendered

| Node clause | Lean rendering |
| --- | --- |
| Cofinal restriction identifies the full coefficient limit with its subsequence | `PurAdicCofinalRestriction A ∧ PurAdicCofinalRestriction B`: it explicitly asserts `HasLimit` for the subsequence, and for every chosen limiting cone T on it there exists a ring-sheaf isomorphism q. `q.hom ≫ T.π_n = rπ_(e(n+1)-1)` is restriction. |
| Inverse coordinate m is reduction from any sufficiently high subsequence coordinate | The second conjunct of `PurAdicCofinalRestriction` says, for every m,n and `h : m ≤ e i*(n+1)-1`, `q.inv ≫ rπ_m = T.π_n ≫ full.map (homOfLE h).op`. This is an equality of ring-sheaf morphisms, hence on all sections and restrictions. |
| Integral theta_i exists and is an isomorphism semilinear over the given a_i | `∃ t : PurAdicPairComparison L A.integral B.integral` and `(t.a i).ringUnderlying = (a.integral i).ringUnderlying`. The `t.c` field is a linear isomorphism after the canonical algebraic inverse-image transport. |
| Displayed projection equations | `PurAdicIntegralNormalized L A B c t` states theta_i followed by target projection equals L(source projection) followed by c_i,n. |
| Uniqueness and independence of the bases | Every underlying set-sheaf morphism f with those projection equations equals `purAdicModuleIso ... t`. Its normalization refers only to the original projections and c, so the comparisons from any other valid cover/bases coincide. |
| Naturality in the specified tower maps | `t.ring_natural` and `t.module_natural` give all i-diagram squares. The product diagram c already contains compatibility with every tower transition. |
| M[1/s] is the actual localized module and ring | `∃ Q : PurAdicLocalization A.integral s`, and Q' on D, occur in the conclusion. `ringIso` identifies each coefficient ring with the recorded sheafification of `Localization.Away`, and `ringUnit_eq` fixes its algebra map. `moduleIso` is an isomorphism over the original ring between restriction of the localized module and the existing `scalarLocalization`, i.e. tensor localization. `moduleUnit_eq` fixes m tensor 1. The node explicitly allows this equivalent tensor description; its sequential-colimit identification is step 5–6 of the recorded proof, not an additional hypothesis. |
| Localized comparisons extend theta uniquely and remain natural | `∃ d : PurAdicPairComparison L Q.pairs Q'.pairs` with `PurAdicLocalizationNormalized L t Q Q' d` fixes ring and module comparisons on the localization units. Every other semilinear comparison d' with the same normalization has the same ring and module underlying isomorphisms. `d.module_natural` and `d.ring_natural` are the directed compatibility equations. Uniqueness is among algebraic/semilinear comparisons, not arbitrary nonlinear functions from a localization. |
| Filtered colimits, their ring and module structures, exist | `∃ F : PurAdicFilteredColimit Q.pairs` and G likewise. `rcolimit`, `pcolimit` are actual `IsColimit` cocones in ring and abelian sheaves. `M` is an actual module sheaf over R and `identify` identifies its abelian sheaf with P. These are conclusions, not assumptions. |
| Scalar action [r_i][m_j] = [r_k m_k] | `F.scalar` and `G.scalar` quantify every i,j,k with i≤k,j≤k and every section over every object, and give exactly this equation after the ring/module coprojections. This specifies the sheafified action without asserting every global section has one global stage representative. |
| Inverse image commutes with the module colimit semilinearly over the ring-colimit comparison | `∃ z : PurAdicColimitComparison L d F G`, with `z.a : AlgebraicInverseImage L F.R G.R` and `z.c : z.a.modules.obj F.M ≅ G.M`. `purAdicPresentedModuleIso` gives precisely L(F.P) ≅ G.P on underlying sheaves. |
| All colimit comparisons are normalized and unique | `z.ring_ι`, `z.module_ι` give every coprojection equation. The last quantified clause equates any other normalized z' with z on both the underlying ring and module isomorphisms. |

### Dependency declarations used

Read each statement dependency's node, binding and declaration/docstring. No dependency
interface was replaced and no new node is required.

- `def-weil-size-convention`: its recorded metatheoretic convention is rendered by explicit universes and `EssentiallySmall`, not a new definition.
- `Sheaf.CategoryTheory.SiteCoveringAxioms`, `CategoryTheory.Precoverage.IsSiteForCoverings`: actual covering-family site axioms.
- `Sheaf.CategoryTheory.RingedSiteModules`, `CategoryTheory.ringedSiteModules`: transparent abbreviation of Mathlib `SheafOfModules`, with actual sectionwise module actions and linear morphisms.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`, `SheafOfModules.cochainModulesMonoidal`: the recorded independent-site-universe tensor structure, retained as a proof import for tensor localization.
- `Sheaf.CategoryTheory.SiteInverseImageTensor`, `CategoryTheory.siteInverseImage_tensor` and `_coherence`: the inverse-image adjunction, exactness, colimits and tensor compatibility. L is specified by its adjunction to that same continuous pushforward; no second inverse-image construction is defined.
- `Mathlib.CategoryTheory.Limits.HasLimits`, `CategoryTheory.Limits.limit`, `limit.π`, `colimit`, `IsLimit`, `IsColimit`: the chosen limits/colimits are expressed using their universal cones/cocones, allowing arbitrary presentations of the same canonical objects.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous`, `SheafOfModules.overFunctor`, `over`, and `Mathlib.CategoryTheory.Sites.Over`: the actual localized ringed sites and bases.
- `Sheaf.CategoryTheory.RingedSectionLocalizationOfUniverses`, `CategoryTheory.ringedLocalizationRingOfUniverses`, `ringedLocalizationRingUnitOfUniverses`: the real fraction-ring sheafification and its unit, explicitly universe-instantiated.
- `Mathlib.CategoryTheory.Sites.Sheafification`, `CategoryTheory.presheafToSheaf`, `toSheafify`, `sheafificationAdjunction`: existing sheafification, retained in the statement and proof imports.
- `Sheaf.CategoryTheory.LocalizationInverseImageCoherence`, `scalarLocalization`, `scalarLocalizationUnit`, `IsInverseImageSection`, and the publicly imported `SheafOfModules.AlgebraicInverseImage`: actual tensor localization, its normalized unit, and the graph-normalized algebraic comparisons. All scalar/isomorphism expressions use these existing operations.

The proof imports additionally include every already recorded proof-dependency module,
including the free-tower comparison, sectionwise presheaf module colimits, sheafification
tensor/underlying-set interfaces, module localization colimit, filtered-colimit representative
criteria and finite-limit commutation, and tensor localization. Mathlib leaves are imported
from the module named in their `mathlib_match`.

### Searches and edge cases

Fresh prescribed searches made with `msearch.py` (the sandbox retains `searches.jsonl`):

- LeanSearch, “Inverse image of sheaves preserves inverse limits of compatible locally free rank one module towers when the coefficient ring limit comparison is an isomorphism, with semilinear localization and filtered coefficient colimits”: 8 hits, including `SheafOfModules.hasLimit`, `hasLimitsOfSize`, `hasLimitsOfShape`, sectionwise presheaf limits and `pullbackObjFreeIso_hom_naturality`; these give existence/individual free pullback, not this adic base-change theorem.
- LeanFinder, “inverse image of compatible locally free rank one inverse towers, preserving the coefficient limit, commutes with scalar localization and filtered colimits”: 8 hits, concerning module free loci, localized modules and algebraic Tilde maps; none states this site/adic system comparison.
- Loogle, `"sheafPullback", "limit"`: three hits, all finite-limit-preservation declarations; none asserts the countable coefficient-normalized tower comparison.
- Mathlib grep, `(adic|localization|[Ll]imit).*(pullback|[Ii]nverseImage)|(pullback|[Ii]nverseImage).*(adic|localization|[Ll]imit)`: 25 displayed hits, mainly scheme pullbacks and `Sheaf/PushforwardContinuous`; no exact match.
- Project `rg` for the node id, `AdicLine`, adic/base-change names, and inverse-image compatible free towers in `lean/WeilConjectures` and `lean/Sheaf`: no existing declaration of this node. `PurInverseImageCompatibleFreeTower` supplies the rank-one tower proof ingredient, with one coefficient index and a fixed small-site universe presentation. `PurIntegralTwistLineInverseImage` and `CartesianCoefficientTwists` concern specialized Tate coefficients. The present diagram structures add directed varying-ring maps, arbitrary positive strides and the localization/colimit normalization required here; they are not replacement definitions of any of those constructions.

Edge cases checked by reading the actual formulas: e_i=1 gives the identity stride; arbitrary
positive e_i retains every positive coefficient level cofinally; coordinate m=0 represents
level 1, so no positive level is omitted. The hypotheses explicitly exclude e_i=0 and empty
I, as the node does. Singleton I is permitted, and no injectivity/surjectivity assumption is
made on any tower or directed map. Zero rings/modules, s_i=0 and s_i a unit are allowed by
the actual `Localization.Away`/tensor construction. An empty covering family is allowed
when the site's coverage allows it. Only C requires bases; no target-site bases or choice
of a global basis is assumed. The module and site universes are independent. The scalar
formula is stated after coprojections, so sheafification does not introduce a false
sectionwise representative assertion. No `STATEMENT-DISPUTED` issue was found.

### Validation

The initial required dry run correctly identified the absent node copy in the unfinished
sandbox. The earlier published-artifact failures recurred once, then the prescribed
current-server confirmation progressed to actual elaboration. Repaired all reported
universe, carrier-type and diagram-map inference errors without changing the node's
statement or dependency list. Explicit coefficient universes on localization and section
transport are necessary; unrestricted inference had chosen universe zero.

The complete module compiled cleanly in both the sandbox and actual-library-name checks
(29.2 and 29.9 seconds). The first complete delivery dry run also passed. A final clause
review then removed the redundant target-section compatibility hypothesis (it follows
from the induced-section equation and coefficient naturality), and made subsequence
limit existence explicit alongside its normalized isomorphism. The final dry run
recompiles this precise signature under the required 60-second limit, two threads and
nice 19. All definitions have real data; the only postponed proof is the
node's named theorem. The node JSON changes only `lean`, whose statement is copied
verbatim from the theorem signature. The delivery dry run and push are recorded by the
prescribed wrapper.

Final revised-signature dry run: `deliver2.py Q19 lem-pur-adic-line-system-base-change --no-push` printed `OK (dry run): commit 9f7d926e1c1 passes the preflight and compiles; nothing pushed`.

## Second reading by Q19

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
