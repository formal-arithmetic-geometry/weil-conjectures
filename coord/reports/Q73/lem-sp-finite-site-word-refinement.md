## Worker report

Stage 2, Q73, lem-sp-finite-site-word-refinement. The delivery states
`AlgebraicGeometry.ProEtale.finiteSiteWordRefinement` in
`Sheaf.Paper.FiniteSiteWordRefinement`, with its single proof `sorry`.
Seven helper definitions construct the specified B and the two rho components,
and descend the canonical open compositors and unit identifications termwise.
They contain no postponed data or auxiliary theorem. The node changes only in
`lean`; its natural-language statement, dependencies and eight-step proof are
unchanged. There are no new nodes, dependency repairs or statement corrections.

The previous retry referred to a stage-1 refusal for an already reviewed split.
This item has a reviewed stage-1 proof but no Lean record, so this is its first
stage-2 statement. The prescribed stage-2 wrapper is used throughout.

The statement and its hypotheses match the node as follows.

| Node clause | Lean rendering |
| --- | --- |
| An arbitrary finite commutative coefficient ring | `(R : Type (u + 1)) [CommRing R] [Finite R]`; no field, presentation, nonzero or flatness binder. |
| Every scheme is Noetherian, meaning finite affine Noetherian covers | Each scheme in every theorem clause has `[IsNoetherian ...]`. Mathlib's `IsNoetherian` is locally Noetherian plus compact; `isNoetherian_iff_of_finite_iSup_eq_top` identifies this with the stated finite-affine-cover criterion. |
| Ordinary constant-R module derived categories on the two small sites | `DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R))` and the corresponding `Sheaf (Scheme.ProEt.topology X) ...`. These are the strictly full D+ subcategories of the ordinary, uncompleted derived categories. |
| N is the specified exact site comparison | `(comparisonUpperStar (ModuleCat.{u + 1} R) X).mapDerivedCategoryPlus`, the recorded module comparison applied termwise. |
| P and J are the direct image and extension by zero | `Etale.rightDerivedLowerStarPlus`, pro-etale `lowerStar ... .rightDerivedFunctorPlus`, and `openImmersionLowerShriek ... .mapDerivedCategoryPlus`, with the appropriate namespace. |
| Lower bounds for Je E, N E, and all intermediate etale proper direct images | The input E and every intermediate are objects of the strictly full `DerivedCategory.Plus`, whose `property` is the existence of a cohomological lower bound. Iterated P and J are actual functors on those subcategories, so this is also true for every successive intermediate, including P_a Je E and P_b P_a Je E. The canonical `mapDerivedCategoryPlusCompatibility` and `rightDerivedFunctorPlusCompatibility` identify these with the ambient ordinary derived operations. |
| Je, Jp and N preserve every specified lower bound | The first two conjuncts quantify `(n : ℤ)` and assume `DerivedCategory.IsGE E.obj n`, concluding `IsGE` at the same n for the relevant outputs. Pro-etale J is tested on every bounded-below pro-etale input, not just etale-origin objects. Every object with a specified lower bound belongs to D+, so this formulation loses no bounded input. |
| e and its composition law descend termwise | The existing `properOpenSiteExtensionIso` is literally `mapDerivedCategoryPlusCompIso.symm`, the descended sheaf isomorphism, and `mapDerivedCategoryPlusCompIso`. The helper open compositors similarly descend the recorded canonical sheaf compositors. No replacement isomorphism is chosen. The open equation is asserted in the theorem. |
| Every proper map here is qcqs and its specified d is invertible | The third conjunct concludes `QuasiCompact r ∧ QuasiSeparated r ∧ IsIso (fixedComparisonDirectImageMatePlus R r)` for every such proper r. |
| B is P_r(e_j) after d_r(Je(-)) | `finiteSiteWordComparison` is the whiskered named d followed by the whiskered named e, with all three functor associators inserted. Its component is the displayed composite, up to identity associator components. |
| B is a natural isomorphism | B is constructed as a natural transformation, and the fourth conjunct asserts its `IsIso`, not merely a `Nonempty` isomorphism between endpoints. |
| The specified bounded-below etale-origin witness | The source of B at E is exactly N_V applied to `(Etale.rightDerivedLowerStarPlus ... r).obj (Je.obj E)`. This etale object already carries its lower-bound property. `IsIso B` supplies its actual witness isomorphism via `asIso (B.app E)`. Thus the witness is the specified word itself, not an arbitrary existential substitute. |
| Canonical proper compositors, normalized by inverse-image adjunction conjugation | The fifth conjunct identifies the existing `etaleComparisonDirectImageCompIso` and `proEtaleComparisonDirectImageCompIso` with `conjugateIsoEquiv` of the two derived adjunctions and the specified inverse-image compositor. Mathlib's convention inputs the inverse-image isomorphism from composite pullback to iterated pullback and outputs the right-adjoint isomorphism from iterated pushforward to composite pushforward, exactly the node's orientation. |
| Proper counit mates obey the displayed composition equation | The next conjunct is `N.map kappa_e ≫ d_ab = d_b ≫ P_b.map d_a ≫ kappa_p`, componentwise for every bounded-below E. Lean's `≫` reads left to right; this is the node's right-to-left displayed composition. |
| d_id is the identity under canonical units | The following conjunct is `d_id ≫ id_p = N.map id_e`, using the right-derived identity isomorphisms, with no arbitrary choice. |
| The analogous open-composition equation | The open conjunct is `N.map m_e ≫ e_ab = e_b ≫ J_b.map e_a ≫ m_p`, using the two explicitly descended open compositors. |
| e_id is the identity | The next conjunct is `e_id ≫ open_id_p = N.map open_id_e`, with the canonical adjunction-based open unit identifications. |
| j_i are open, u and r2 proper, and u j1 = j2 | The final conjunct has the two open immersion instances, `(a : W₁ ⟶ W₂) [IsProper a]`, `(r₂ : W₂ ⟶ V) [IsProper r₂]`, and `(h : j₁ ≫ a = j₂)`. The notation r1 is eliminated by writing `(a ≫ r₂)` throughout. |
| rho_t is kappa_t after P_r2(alpha_t) | `finiteSiteEtaleRefinement` and `finiteSiteProEtaleRefinement` are exactly those two composites, using the specified `properOpenComparison` and `properOpenProEtaleIsoPlus.hom`. The latter is the recorded open-adjunct comparison from `lem-sp-refinement-coefficient-mate`, not an unspecified map. |
| Pushed-refinement equality on D+ | The final equation is `N_V.map rho_e ≫ B_r1 = B_r2 ≫ rho_p`, at every E. No Cartesian-square hypothesis is present. All component equations include the canonical associators (their object components are identities); B itself is a natural transformation. |

The D+ formulation uses the already published fixed-coefficient interfaces. It does
not introduce new derived categories, use completion, replace a named mate by an
arbitrary isomorphism, or impose constructibility. In particular, the recorded
`FiniteCoefficientEtaleDerivedCategory` is the same etale fixed-ring derived
category used here. On the pro-etale side `finiteCoefficientRealization` and its
published equivalence theorem identify fixed-ring module sheaves with modules over
the recorded connected-component coefficient ring sheaf. No private second module
category or coefficient sheaf is defined in this delivery.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`; the scheme specialization
  is `AlgebraicGeometry.IsNoetherian` in `Mathlib.AlgebraicGeometry.Noetherian`.
- `WeilConjectures.AlgebraicGeometry.DerivedCategories`: the documented ordinary
  fixed-ring `Etale.DerivedCategoryModule`, `DerivedCategory.Plus`, homology and
  bounded-below subcategory. Its `torsionCohomology` predicate is not needed here.
- `Sheaf.AlgebraicGeometry.ProEtaleFiniteModules`: `FiniteCoefficientModules`,
  `FiniteCoefficientEtaleDerivedCategory`, `finiteCoefficientRealization`,
  `finiteCoefficientRealization_isEquivalence_ring`, and its exactness interface.
- `Sheaf.AlgebraicGeometry.ProEtaleSiteComparison`: `Scheme.proEtaleSiteComparison`
  and `Scheme.proEtaleSiteComparisonModules`; the latter is `comparisonAdjunction`.
- `Sheaf.AlgebraicGeometry.FixedComparisonDirectImageMate`:
  `fixedComparisonPullbackPlus`, `fixedComparisonDirectImageMatePlus`, its
  invertibility and its actual counit normalization.
- `Sheaf.AlgebraicGeometry.ProEtaleExtensionZeroComparison`:
  `openImmersionLowerShriekComparison_coherence`, the underlying
  `openImmersionLowerShriekComparisonUpperStarIso`, and `proEtaleOpenExtensionComp`.
- `Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations`: the intrinsic
  constant-ring operations and their published finite-coefficient specialization.
  The named mate and refinement dependencies expose the equivalent fixed-ring
  sheaf-valued `lowerStar`/`upperStar` operations used in their own signatures.
- `Sheaf.AlgebraicGeometry.Etale.OpenImmersionLowerShriekCoherence`:
  `Etale.openImmersionLowerShriekComp` and its coherence theorem.
- `Sheaf.AlgebraicGeometry.ProperOpenComparison`:
  `Etale.properOpenComparison`, with its actual theta and open adjunction.
- `Sheaf.Paper.RefinementCoefficientMate`: `AlgebraicGeometry.refinementCoefficientMate`
  and its site component. Its public dependency `Sheaf.Paper.ProEtaleProperOpenComparison`
  provides `properOpenSiteExtensionIso` and `properOpenProEtaleIsoPlus`.
- `Sheaf.AlgebraicGeometry.ComparisonDirectImage` (exposed by the preceding module):
  `etaleComparisonDirectImageCompIso` and `proEtaleComparisonDirectImageCompIso`.
  Their precise adjunction normalization is explicitly asserted in the new theorem.

Every recorded statement-dependency module is publicly imported; every available
recorded proof-dependency module (including Mathlib matches) is imported. The
proof docstring includes each of the node's eight steps with its prerequisites.
No additional postponed lemma or unmatched sorry is introduced.

Sources opened: local `proetale.tex`, `lemma-morphism-comparison` (09A6) and
`lemma-jshriek-comparison` (09AF); `more-etale.tex`, `lemma-shriek-well-defined`
(0F7I); and the current main-20261015 blueprint exceptional-reduction proof's
Locality paragraph. These give the canonical site/open maps and the formal pasting
route. The full node and its recorded statement dependencies were read.

Searches for an existing full assertion:

- `msearch.py`, LeanFinder, query `Finite ring etale proetale derived comparison counit mates direct image composition proper open refinement`: eight hits, including condensed-solid counits and unrelated scheme/etale declarations; no full assertion.
- `msearch.py`, Loogle, query `CategoryTheory.mateEquiv_hcomp`: one hit, the generic Mathlib horizontal mate-pasting lemma; no finite-site/refinement assertion.
- `msearch.py`, grep, query `finiteSiteWord|pushedRefinement` in `CategoryTheory`: zero hits.
- Direct `rg` on project `lean/WeilConjectures` and `lean/Sheaf`, query `finiteSiteWord|pushedRefinement|lem-sp-finite-site-word-refinement`: zero hits before writing. Relevant maps were then read by their recorded module paths; none states this entire package.
- `msearch.py`, LeanSearch, query `Etale proetale comparison direct image composition and pushed proper open refinement`: eight hits: ordinary sheaf pushforward composition, formally etale/etale ring composition, scheme module restriction composition, proper-map composition, and presheaf pushforward composition; no full assertion.

Edge cases checked against the types and the eight-step argument: the zero ring
is permitted; no `Nontrivial R` assumption exists. Empty schemes and empty source
opens are permitted; there is no nonemptiness or chosen affine in the statement.
The lower bound is an arbitrary integer including negative values. Identity
proper/open maps use the explicit canonical unit laws. The non-Cartesian example
W1 = Spec(k) disjoint union Spec(k), W2 = X = Spec(k), j1 the first component,
j2 the identity, and a the fold satisfies the final binders and is not excluded.
No algebraic field structure, torsion presentation, Tor-amplitude, bounded-above,
flatness, or coefficient-extension assumption has been added.

There is no STATEMENT-DISPUTED flag and no identified node fault.

Validation: the prescribed `scompile.py Q73 lem-sp-finite-site-word-refinement`
compiled the final module in both sandbox and library modes within the 60-second
per-file limit, without errors or warnings. Delivery preflight follows below.

Delivery validation: `deliver2.py Q73 lem-sp-finite-site-word-refinement --no-push`
printed `OK (dry run): commit f1070b649e8 passes the preflight and compiles; nothing pushed`.
Only the module, the item's lean record, and this worker report were staged.
The delivery command repeats the checks before pushing.

## Second reading by Q73

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
