## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-fppf-face-total-qcoh-equivalence.json`: existing statement, split; no Mathlib match.
- `dag/nodes/sec-six-functors-basics/lem-sfb-ringed-unbounded-descent-criterion.json`: statement-only, unsplit; no Mathlib match. General five-hypothesis ringed-topos criterion, Stacks 0D7V with 0D6R written out.
- `dag/nodes/sec-six-functors-basics/lem-sfb-fppf-face-heart-descent.json`: statement-only, unsplit; no Mathlib match. Effective descent of modules in degree zero, face-only version of 0DHD.
- `dag/nodes/sec-six-functors-basics/lem-sfb-fppf-face-heart-derived-unit.json`: statement-only, unsplit; no Mathlib match. The derived unit only for a quasi-coherent module in degree zero, face-only version of 0DHE.
- `citations.json`: every proof-step citation with its verbatim statement, including the hypotheses.

## Attachments

None. Searched the project `lean/WeilConjectures` by the exact blueprint tag and by face/total, hypercover, semisimplicial, quasi-coherence and cohomological-descent terms. No project declaration states the whole item. The Mathlib results concern one-hypercovers, definitions of quasi-coherence, abstract adjunctions and exact derived functors; none supplies these statements. In particular `SheafOfModules.pushforwardPushforwardEquivalence`, Mathlib/Algebra/Category/ModuleCat/Sheaf/PushforwardContinuous.lean:375–400, assumes an equivalence of sites. A hypercover augmentation has no such equivalence. `Functor.mapDerivedCategoryFactors` only descends an exact functor through localization, and `Adjunction.toEquivalence` already assumes invertible units/counits. These cannot establish the new criterion.

## Wanted

None. Sources used are present in `literature/`.

## Problems and corrections

The original item was unsplit. Its statement is retained exactly, including unboundedness and the absence of quasi-compactness/separatedness assumptions. The source explicitly labels the face-only version agent-supplied; Stacks 0DHF must not be treated as literally stating it. I preserve this distinction in proof origin and in the two new geometric nodes' source fields. No claim of flat degeneracies is made.

The historical blueprint chain is broken: `tools/blueprint_refs.py ancestor lem-sfb-fppf-face-total-qcoh-equivalence` prints `None`, because `lem-sfb-admissible-direct-image` was created for `Sheaf.SixFunctors.CtfStabilityDirectImages`, a module rather than a DAG id. I retain the prescribed null ancestor and the full inherited via chain. The exact supporting place is recorded. The latest blueprint `sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md`, paragraph (3), is the historical origin and has no separate face-total assertion. The unit and chapter remain unchanged.

I initially considered a new component-object cohomology comparison. Searching all same-tag nodes found `lem-sfb-semisimplicial-evaluation-free-adjoint`; its exact left adjoint makes that comparison a short injective-resolution argument, now written in step 4. The proposed comparison node was deleted before delivery. Searches for it remain in the genuine search log and result files as historical work, not as a delivered node.

## Unfinished work

No part of this item's one-level split is left unfinished. The three new inputs are intentionally statement-only and join the stage-1 queue. Their future proof work is not represented as already proved:

- For 0D7V the proof is the source's bounded-below equivalence followed by truncation control from the two local-bound assumptions. Those assumptions are essential; an equivalence of hearts alone is insufficient for unbounded derived descent.
- For face-heart descent, use effective fppf descent through the matching maps; invertible face transitions encode the descent isomorphism and its cocycle. The underlying simplicial object remains available, so split identities also recover the degeneracy compatibilities, without requiring degeneracy pullback to be exact. This is only an underived result.
- For the degree-zero derived unit, adapt the big-fppf comparison and hypercover resolution in the proof of 0DHE to injective order maps. Tags 0DGN and 0DGP supply the component quasi-coherent topology comparison. Only the alternating-face resolution is required. This input asserts acyclicity for a single sheaf, not the unbounded equivalence or essential surjectivity.

## Not duplicates

The source-tag scan of all nonmerged live nodes found no same-tag existing nodes for the three delivered new nodes. Whole-blueprint searches for descent, quasi-coherent, unbounded, cartesian, face, 0D7V, 0DHD and 0DH2 found no imported node stating any of these three lemmas. The broad searches include the existing scheme-only fpqc and Picard descent nodes, which do not state descent of algebraic-space face-total systems.

lem-sfb-ringed-unbounded-descent-criterion vs lem-sfb-fppf-face-total-qcoh-equivalence: the criterion is for any ringed-topos morphism, conditional on five explicitly written hypotheses; it proves none of the geometric hypercover hypotheses or local affine bounds.

lem-sfb-fppf-face-heart-descent vs lem-sfb-fppf-face-total-qcoh-equivalence: the former is underived effective module descent, one hypothesis of the general criterion; it states no derived equivalence, derived unit or weak Serre property.

lem-sfb-fppf-face-heart-derived-unit vs lem-sfb-fppf-face-total-qcoh-equivalence: the former proves only the derived unit on degree-zero quasi-coherent modules, with no essential-surjectivity assertion or arbitrary-unbounded-complex assertion. The item's proof checks the other criterion hypotheses before using the general theorem.

lem-sfb-fppf-face-heart-descent vs lem-sc-etale-qcoherent-descent: the existing node only says the associated presheaf on a scheme's small etale site is a sheaf; it does not effectively descend module systems on an algebraic-space fppf hypercover.

## Review by Q82

I read Stacks `spaces-simplicial.tex` 0DHF in full, particularly its separate checks Ad (1)–(5), its cited 0D7M characterization, and the full 0DHD/0DHE proofs. I read the criterion 0D7V and its proof and the exact local condition 0D6R in `sites-cohomology.tex`. I read `spaces-more-cohomology.tex` 0DGN/0DGP, used in the degree-zero input's source. For component quasi-coherence closure I checked `spaces-properties.tex` 03M1. I read 0DH2 and the flat augmentation and cartesian-module passages of `spaces-simplicial.tex` to check the face adaptation. For K-flat representatives I read `sites-cohomology.tex` 06YS, and for the derived adjunction the 07A6 statement. The current blueprint affine etale acyclicity statement agrees with the cited live node.

Step 1 cites the actual existing hypercover-face-property statement, which explicitly supplies flatness of every injective-order-map pullback and every augmentation component. It does not purport to supply flatness of degeneracies. The semisimplicial total-category statement explicitly supplies exact conservative evaluation, the component pullback formula, and the cohomology characterization of cartesianness when transition pullbacks are exact. These are exactly the assertions used. Component exactness detects total exactness, so the extra flatness inference is written out.

Step 2 uses the existing space quasi-coherent kernels/colimits and extension-closed statements on every component and on Z, with their absence of finiteness hypotheses. It cites the same exactness and component-system statements as step 1. Kernels/cokernels preserve invertible transitions by exact pullback; the extension diagram argument is written out, not cited as an unstated theorem. These four citations establish the weak Serre hypothesis without needing a separate weak Serre node.

Step 3 uses precisely the two new degree-zero inputs: the underived heart equivalence with its ordinary direct-image inverse, and the actual derived adjunction unit on a module. Their common setup introduces S, Z, every matching map, the enlarged sites, the face total category and its quasi-coherent systems. The hypotheses coincide with the item; no finite type or flatness condition on a degeneracy has slipped in. They are smaller inputs for the five-hypothesis criterion, not replacements of the entire unbounded argument.

Step 4 uses the enlarged-site-model statement for scheme charts, covering families and module-site identification; the space pullback-quasicoherent statement for restriction to an affine scheme object; the scheme Zariski/etale equivalence for identification with the associated module; and the affine etale acyclicity statement for positive-degree vanishing. I read the latter two statements rather than assuming that any site-presented module is already a Zariski module. The exact evaluation free-adjoint statement explicitly gives an exact left adjoint; I wrote out how this preserves injectives and why sections of the evaluated resolution are identical. Thus the total/component cohomology comparison does not invoke a theorem hidden in the proof of another node. Refining each etale covering by affine domains is allowed componentwise, so the criterion's cofinal covering requirement holds. The bound is zero independently of n, the affine object, the sheaf, or any global dimension. No quasi-compactness or separatedness is used.

Step 5 applies the new general 0D7V criterion with the source and target in the correct direction, and matches each of its five hypotheses to steps 1–4. Its statement includes the canonical unit and counit, so no assertion about an arbitrary chosen equivalence is substituted for the adjunction. The enlarged-site-model statement supplies the module equivalences used to identify the target category with the item's small etale category.

Step 6 uses existing ring-sheaves-Grothendieck and Grothendieck-K-injective statements on small sites in the common module universe. The right-derived definition explicitly computes the functor on K-injective resolutions. The existing general ringed-site K-flat resolution statement gives flat terms without boundedness, and the existing ringed-topoi derived pullback statement explicitly computes the pullback using them. I did not use the special constant-coefficient version of a resolution theorem for structure-sheaf coefficients. Off-unit generic tools are declared in split_report.tool_uses.

I checked B–E against these files: the three new nodes are self-contained statement-only nodes, have exact Stacks tags/labels with their adaptation scope disclosed, have genuine recorded Mathlib queries of all requested kinds and two natural-language phrasings, and carry blueprint source places. I inspected the search hits and the plausible Mathlib site-equivalence/derived-functor sources before giving no-match verdicts. citations.json quotes every cited statement verbatim. No proof step exceeds 2000 characters.

Small-case checks: for the identity hypercover of a point, the face-total heart consists of constant-compatible module systems and the conclusion reduces to ordinary complexes; the criterion specializes to the identity ringed topos. The empty space has only the zero quasi-coherent module, and affine-basis conditions are vacuous. A Cech hypercover of a faithfully flat non-etale map still has flat faces while its diagonal degeneracy need not be flat; the proof only uses the former. Non-quasi-compact spaces are covered by possibly infinite families of affine scheme charts, which the local-bound criterion allows. The degree-zero inputs make no false assertion that arbitrary noncartesian total modules descend. These checks did not reveal a statement dispute or require changing the item.
