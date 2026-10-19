# Worker report: lem-kun-geometric-point-derived-constants

## Files written

- `dag/nodes/sec-smooth-purity/lem-kun-geometric-point-derived-constants.json`: statement node; split into seven steps; no new nodes, no Mathlib leaf.
- `citations.json`: one exact statement quotation for every node used by every proof step.
- `searches.jsonl`: actual outputs logged by msearch.py; the item's previous search records remain intact.

## Attachments

None. Searches of the read-only slopmaster2 `WeilConjectures/` by item id, constant/stalk equivalence, constant-sheaf IsEquivalence and derived point category found no declaration stating every clause. The finished sheaf-constancy and local-site instances are only abelian ingredients; the derived point file proves detection and has a sorry in its duality assertion, not this normalized monoidal equivalence.

## WANTED

None.

## What was wrong or corrected

The item had a statement but no proof. Its statement, hypotheses, ordinary integer coefficients, ancestry, and unit binding are unchanged. I supplied the unit/counit equations rather than assuming a chosen abstract equivalence has the required normalization. I also supplied the unbounded K-flat preservation argument rather than inferring a derived tensor comparison from exactness alone. An early draft reversed the written adjunction direction; the delivered proof uses the correct `C_s ⊣ S` and checks both triangle identities explicitly. The parent `lem-kun-0f0f` already documents the error in the blueprint's global-free-sheaf argument; this item realizes the parent's accepted geometric-point reduction and changes no unit route.

## What could not be finished

No mathematical part remains for this stage-1 item. No Lean was written, no compiler/Lake/build command was run, and no live project file was changed.

## Review by Q81

I read the contract, stage-1 brief, delivery-errors B through E, the three levels in SETUP, GOAL, dag-sync, the chapter, the Kunneth unit and its empty steps list, the parent `lem-kun-0f0f` and the current main-20261015 proof. The item's source is Stacks `etale-cohomology.tex`, Tag 04JQ (`lemma-equivalence-abelian-sheaves-point`, lines 9078 ff.), with the constant-germ theorem sourced by Tags 03PT (2) (`lemma-stalk-exact`), 040R (`definition-stalk`) and 03PQ (`lemma-cofinal-etale`), and the geometric-point tensor reduction in Tag 0F0F (`lemma-projection-formula-proper`, lines 19001 ff.). I read these texts: 04JQ gives the stalk equivalence, and 0F0F uses the derived point tensor reduction but does not itself write all coherence details. Accordingly proof_origin is agent, with those sources identified. I also read `homology.tex`, Tag 010N (`lemma-exact-functor`), `sites-modules.tex`, Tag 03EK (`section-tensor-product`, lines 3551 ff.), and `sites-cohomology.tex`, Tags 06YS (`lemma-K-flat-resolution`, lines 3207 ff.) and 0DEN (`lemma-check-K-flat-stalks`, lines 3767 ff.).

Step 1 uses the statement of `lem-exc-abelian-sheaves-gmodules`: it is the actual geometric stalk, with its additive operations, and it is an equivalence for a field and an algebraically closed extension containing its separable closure. Here all three fields are Omega and the Galois group is trivial. Discrete trivial-group modules are precisely abelian groups, as the step writes out; no field-extension theorem is silently added.

Step 2 uses the actual map in `lem-weil-pbc-constant-sheaf-geometric-stalk`, which is the germ of the constant-presheaf sheafification-unit section, and `def-kun-constant-sheaf`. The unit eta is that map, not an arbitrary isomorphism. Full faithfulness of S supplies the unique epsilon with S(epsilon)=eta inverse. The proof computes the triangle identities, checks naturality and additivity, and transports the kernel/cokernel universal properties for exactness. All this is a few-line consequence of Step 1 and the cited constant-germ theorem; it is not another node restating the underived clause of this item.

Step 3 cites `lem-weil-pbc-exact-functor-complex-cohomology` for its natural comparison in every degree and `lem-weil-pbc-localization-universal-property` for descent of functors, natural transformations and equations. I read both statements; they cover unbounded complexes and natural transformations. `def-weil-pbc-derived-categories` identifies the ordinary integer category with D(Ab). No bounded representative, enough-injectives hypothesis, or constructibility condition is used. Vanishing below each integer is preserved by the same cohomology comparison.

Step 4 uses `def-kun-constant-sheaf` and `def-pur-sheaf-tensor-product`, whose statements explicitly give locally constant values and sheafification of sectionwise tensor. The proof constructs both constant tensor maps and checks their composites on locally generating pure tensors; it writes the associativity, symmetry and unit checks. Step 5 uses that tensor definition and `def-weil-pbc-geometric-stalks` for germs. Reduction through the already constructed counit identifies the canonical germ tensor map on arbitrary sheaves with the explicit constant formula. The equation for eta on pure tensors proves its monoidality, and S(epsilon)=eta inverse plus faithfulness proves the counit equations. These are written local generator calculations, not a hidden comparison theorem.

Step 6 uses the total tensor and K-flat definitions in `def-kun-derived-tensor` and the cohomology comparison already cited. It proves coproduct preservation from Hom universal properties, hence compatibility with all direct-sum tensor degrees and the differential sign. For arbitrary acyclic A in the target, G(A) is acyclic, and F(P) tensor A = F(P tensor G(A)) is acyclic. This explicitly proves K-flat preservation in both directions, including unbounded complexes.

Step 7 cites `lem-pc-kflat-resolution`, which states unbounded K-flat resolution existence on any ringed site, with flat terms and a termwise-surjective augmentation. The small etale site with constant Z qualifies, as does the one-point ringed site computing ordinary abelian groups. `def-kun-derived-tensor` supplies precisely this K-flat tensor construction. The localization statement gives descent of the natural comparisons and equations, in each tensor variable. The sign symmetry is the same (-1)^(pq), and the normalization is preserved. Both generic off-unit tools, field-stalk equivalence and K-flat existence, are declared in split_report.tool_uses; neither replaces any Kunneth-unit proof step. The cohomology and localization tools are Mathlib leaves.

For B--E I checked the statement introduces its objects and has all definition dependencies; every cited statement was read and is copied verbatim in citations.json, with no reliance on a cited node's proof; no non-elementary fact is left behind a tag-only citation; no new clause-shaped or elementary node is created. All seven steps are below 1,000 characters, so none triggers the 2,000-character long-step review. Exact functors/localization and the actual K-flat existence theorem are cited rather than inferred from definitions. The local tensor and equivalence transport arguments marked elementary are written out from definitions and preceding steps. The source route uses no SGA citation.

I tested N=0, the unit N=Z, the torsion case M=N=Z/2 (whose derived tensor retains Tor in degree -1), complexes with arbitrarily many nonzero degrees, and the zero complex. The normalized pure-tensor formulas reduce to identities; the K-flat argument uses arbitrary acyclic complexes so does not accidentally discard the Tor or unbounded cases. Algebraic closure is used in Step 1; over a non-separably-closed field the Galois group need not be trivial, so this specialization would fail as expected.

The existing Mathlib search records were retained and their returned declarations read. I additionally ran six logged searches: LeanFinder with two phrasings, Loogle, LeanSearch, and grep globally and in AlgebraicGeometry/Sites. I read the returned signatures and the plausible source definitions: constantSheaf/constantSheafAdj (ConstantSheaf.lean 66/70), sheafCongr (Equivalence.lean 141), condensed functorIsoDiscrete (Condensed/Discrete/Module.lean 122), and etale point lifting (EtalePoint.lean 37). They supply definitions or different categories, not this theorem. No service was down in these searches and no search is claimed without an actual log.

## Not duplicates

No new nodes are created. Whole-DAG and whole-blueprint searches by constant, stalk, geometric point derived, and constant germ found the reused ingredients but no blueprint node stating this full normalized unbounded equivalence. In particular the existing `lem-weil-pbc-geometric-point-pullback-stalk` and `lem-exc-abelian-sheaves-gmodules` state abelian equivalences, `lem-sf-point` has different coefficient/duality scope, and `lem-sfb-etale-derived-tensor-stalk` gives tensor compatibility but not a quasi-inverse normalized equivalence.
