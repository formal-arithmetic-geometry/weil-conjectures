## Worker report

The unchanged node is stated in
`lean/Sheaf/Paper/RefinementExchangeCoherence.lean`, with primary declaration
`AlgebraicGeometry.ProEtale.StrictTower.refinementExchangeCoherence`.
There are no new nodes, dependency repairs, or statement corrections.
The file has three postponed theorems, each belonging to this item's statement or
its explicit proof step 2, with source and full proof-plan docstrings. The two
helper definitions have actual data.

The canonical operations are reused rather than copied: `compositionF B c` is
`J B c.i ⋙ R B c.g`; `compositionC` is the normalized identity-left gamma followed
by the outer R and canonical compositors; `compositionE` is the proper-square mate
followed by beta and its associators. `refinementComparison` only supplies the
quasi-compactness of the two opens using `Compactification.quasiCompact_openImmersion`.
`refinementCommonComparison` is literally `asIso C_u₁ ≪≫ (asIso C_u₂).symm` at M,
so its hom is the specified `C_u₂⁻¹ C_u₁` in right-to-left notation. It is an actual
isomorphism, not an arbitrary map or a chosen witness of existence.

Hypothesis and clause correspondence:

- `B : Type (u + 1)` and `[CommRing B]` allow arbitrary commutative B, without
  finiteness or a nonzero assumption. `Scheme.{u}`, `Derived B X`, `G`, `R`, `J`,
  and `ev` are the recorded strict constant-coefficient pro-etale tower operations.
  The site and coefficient universes are exactly those of the dependency API.
- `[IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]` express separated
  finite type. They impose no qcqs or Noetherian assumption on Y.
- All `c₁`, `c₂`, `c₃`, `d`, `e`, and the three cocycle refinements are supplied
  `Compactification f` objects. `Refinement` supplies the equations on the open
  immersion and proper projection; its underlying morphism is proper by the
  existing compactification interface. No density or cartesian condition is
  imposed on the original refinement.
- `M : Derived B X` and
  `hM : ∀ n : ℕ, Nonempty (ScalarEtaleOrigin B X ((ev B X n).obj M))` are precisely
  the stipulated domain: at each level a finite commutative Λ, a map B → Λ, a
  bounded-below etale-origin witness and a scalar-restriction isomorphism. Each
  level has its own ring and lower bound; no compatibility of chosen witnesses
  or uniform lower bound is added.
- The first conjunct is `IsIso ((refinementComparison B r).app M)` for every
  refinement r. `refinementComparison_isIso` separately names the same fact
  needed by the real-data common-refinement definition.
- The second conjunct is `C_id = 𝟙 _`. The third is
  `C_(r.comp s) = C_s ≫ C_r`, Lean's left-to-right form of the node's composition
  identity. Both are equalities of natural transformations, before evaluation.
- In the fourth conjunct `sf : IsPullback g' f' f g` binds the whole arbitrary
  base change. `si₁`, `sp₁`, `si₂`, `sp₂` specify its open and proper cartesian
  faces for the supplied primed compactifications. Their `.w` fields give the
  commutativities required by `compositionE`. The equation `hr` says r' is the
  pulled-back refinement. The displayed natural-transformation equality is
  `e₂ ≫ G_g' C_r' = C_r G_g ≫ e₁`, exactly `C'_r e₂ = e₁ G_g C_r`.
  Quasi-compactness of f' is obtained from sf using
  `MorphismProperty.IsStableUnderBaseChange.of_isPullback`; it is not an added
  hypothesis. Neither g nor the compactification projections s_i is assumed proper.
- The fifth conjunct equates `refinementCommonComparison` for arbitrary common
  refinements d and e and arbitrary pairs of arrows. Taking d = e includes
  independence of the arrows, with no extra compatibility assumption.
- The sixth conjunct uses three independently supplied common refinements d₁₂,
  d₂₃ and d₁₃ and asserts `I₁₂ ≪≫ I₂₃ = I₁₃`. Thus the cocycle is not restricted
  to three comparisons computed from one common refinement.
- The final conjunct supplies the cartesian faces for c₁, c₂ and d and compatible
  pulled-back arrows u₁', u₂'. It states
  `G_g.map I₁₂.hom ≫ e₂.app M = e₁.app M ≫ I₁₂'.hom`. The primed input is
  `(G B g').obj M`, and its finite-origin hypothesis is supplied by the named
  `refinementFiniteOrigin_pullback`, which is exactly item proof step 2. There is
  no additional finite-origin assumption after pullback. Independence allows any
  other common-refinement diagram to compute the same primed isomorphism.

Dependencies read and reused (names below are in
`AlgebraicGeometry.ProEtale.StrictTower` unless indicated):

- `Sheaf.AlgebraicGeometry.StrictConstantTowerOperations`: `Derived`, `Towers`,
  `G`, `R`, `adj`, `ev`, `rId`, `rComp`, `gComp`, `evalG`.
- `Sheaf.AlgebraicGeometry.StrictTowerOpenExtension`: `J`, `jAdj`, `jComp`,
  `jCongr`, `evalJ`.
- `Sheaf.AlgebraicGeometry.StrictTowerProperOpenArrows`: `gamma`, `beta`,
  `exchange`; and `StrictTowerProperOpenCalculus`: `gamma_isIso`,
  `gamma_identities`, `normalizedProperOpenCalculus`.
- `Sheaf.AlgebraicGeometry.FiniteConstantCoefficientTransport`:
  `ScalarEtaleOrigin`, `H`, `HD`, `hPullbackInv`, `hPullbackInv_isIso`, `originIso`.
- `Sheaf.AlgebraicGeometry.StrictTowerCompositionPasting`: the already published
  definitions `compositionF`, `compositionC`, `compositionE`, not any theorem
  about composition or common-refinement coherence.
- `WeilConjectures.Compactification.Defs`: `AlgebraicGeometry.Compactification`,
  `Compactification.Refinement`, its identity and composition, and
  `quasiCompact_openImmersion`. The projection-compactification node's recorded
  `Scheme.proEtaleRingCompactSupportImage` was read: it concerns individual ringed
  module categories. Here the item explicitly uses the strict-tower R and J,
  so its supplied compactification datum is reused with those recorded operations.
- Mathlib `LocallyOfFiniteType`, `QuasiCompact`, `IsSeparated`, `IsProper`,
  `Limits.IsPullback`, and `CategoryTheory.mateEquiv` are the recorded geometric
  and mate interfaces; no replacement notions are introduced.
- Proof-only imports: `WeilConjectures.Compactification.CategoryBaseChange`
  (`isCofiltered`, `baseChangeFunctor`, base-change identity/composition),
  `WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact`
  (`AlgebraicGeometry.etaleInverseImageModulesExact`), and
  `Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence`
  (`supportSiteComparison_pullback_coherent`). Mate pasting is in the inherited
  `Mathlib.CategoryTheory.Adjunction.Mates` import.

Import-cycle note for the maintainer: `StrictTowerCompositionPasting` already owns
F, C and E, so this file imports it to avoid duplicate definitions. Its
`compositionCommonCoherence` proof cites this item. Under stages/2-statements §3.7,
the automatic proof import of this module back into `StrictTowerCompositionPasting`
must therefore be omitted; its proof can use an eventual extraction of the shared
canonical definitions. This delivery introduces no DAG edge to the downstream theorem
and uses none of its postponed theorem proofs to construct the maps here.

Sources checked directly: Stacks `more-etale.tex`, labels
`lemma-shriek-proper-and-open` (0F7B), `lemma-shriek-proper-and-open-compose`
(0F7C), `lemma-shriek-proper-and-open-base-change` (0F7F), and the final paragraph
of the cited `thm-cbc-complete-proetale.md` blueprint proof. The item is a
strict-tower refinement consequence of those normalized operations, as its six
proof steps explain; no source correction was needed.

Searches for an existing full statement:

- `msearch.py leanfinder`, “Refinement exchange coherence compactification strict
  tower”: only unrelated topology/refinement hits, no matching theorem.
- `msearch.py loogle`, `gamma, cbcRefinementMap, Compactification`: no match.
  A further `CategoryTheory.mateEquiv` query found the mates equivalence and its
  twelve related normalization/pasting declarations, not this compactification theorem.
- `msearch.py grep`, `RefinementMap|gamma_identities|normalizedProperOpenCalculus`:
  no Mathlib match. A corrected Mathlib `CategoryTheory` search for
  `compactification.*(exchange|refinement)|refinementComparison|compositionC`
  likewise returned zero hits.
- `rg` in both upstream `WeilConjectures` and side `lean/Sheaf`, for this node id,
  `refinementExchangeCoherence`, and `refinementCommonComparison`: only the
  downstream composition module's docstring cited the item. Reading that module
  located the canonical F/C/E definitions reused here, but no full matching theorem.

Edge cases checked against the signatures and constructions: empty schemes and
zero rings are admitted; n = 0 is the first positive tower level; zero derived
objects are admitted; identity and composite refinements have explicit clauses;
common refinements may coincide while their arrows differ; the three cocycle
comparisons may use distinct common refinements; identity and arbitrary base
changes are retained. All equations are in the actual derived strict-tower
categories, with no evaluation-faithfulness premise. No `STATEMENT-DISPUTED` flag.

Validation: scompile.py passed for the delivered file with no errors or unexpected
warnings. All three theorem proofs remain `sorry`, as required by stage 2.

## Second reading by Q80

Final worker reread of the node, definitions, and complete theorem signature;
the dispatcher explicitly forbids starting another worker, so the maintainer's
independent reading remains the independent review of this delivery.

This pass found and repaired an initial weakening: an existential comparison map
was insufficient for the specified canonical isomorphism, independence, and final
intertwining. The file now constructs the canonical isomorphism from the actual
C maps and states all three missing clauses explicitly. It also removed an
unnecessary proposed prose correction: the original base-change notation can be
rendered with supplied cartesian squares without changing the node. It removed
an added quasi-compactness premise on f', deriving that property from sf instead,
and supplies both proper and open cartesian faces. Finally it strengthened the
rendering of the cocycle from one common refinement to three independently chosen
common refinements, matching the choice-independent wording directly.

I checked each of the seven main conjuncts against the correspondence above,
including the directions and domains of C and e, the inverse in I₁₂, all three
refinement-arrow compatibilities, and the finite-origin witness after pullback.
No node statement was changed. The only node-field delta is the `lean` record.
