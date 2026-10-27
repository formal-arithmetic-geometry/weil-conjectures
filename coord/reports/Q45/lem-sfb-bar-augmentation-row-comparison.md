# Q45: lem-sfb-bar-augmentation-row-comparison

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-bar-augmentation-row-comparison.json`: existing statement, now split into eight proof steps; no exact Mathlib match. Its statement and statement dependencies are unchanged.
- No new DAG nodes and no new Mathlib leaves. The existing DAG supplies the needed spectral-sequence, row-collapse, and bar-total comparison results.
- `citations.json`: one entry per step/cited-node pair, quoting the complete relevant node statement verbatim. `searches.jsonl` contains the Q45 search commands and actual result digests. These are supporting sandbox evidence.

## Attachments

None. I searched `lean/WeilConjectures/` by the exact item id/docstring tag, bar augmentation, positive-row, row-comparison and condensed-bar terminology. No declaration there states every clause of the item. The spectral-sequence and ordinary injective-resolution declarations found are ingredients, not attachments of this item; nothing was compiled.

## Wanted literature

WANTED: none for this split. The formal argument uses the available Stacks source and existing internal-bar interface. The blueprint does not itself assert the positive-row refinement, so `proof_origin.by` is `agent`; this is not attributed to an unstated theorem of the blueprint.

## Corrections and scope

The item was unsplit with no sandbox attempt, report, or search log when I started. There is no released stage-1 repair note for it. I copied its current repository version into the sandbox and preserved its statement, statement dependencies, provenance, blueprint reference, and old searches.

The source's Tag 0133 proves the stronger column-exact special case, not the full item: I did not treat it as the positive-row theorem. Tags 0130 and 0132 give the spectral sequence used for the refinement. The actual augmentation is proved a quasi-isomorphism through functoriality for the concrete single-row double complex, which resolves the actual-morphism issue omitted at the end of the source's proof of Tag 0133. There is no statement dispute or change of hypotheses.

The inherited `blueprint.from.node` is null; `tools/blueprint_refs.py ancestor` confirms that the existing created-item chain has no blueprint ancestor. I retain that metadata instead of inventing an ancestor. I read the current `literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md` and its `sk-thm-sf-ctf-stability-direct-images.proof.md`, especially paragraph (3), and the unit/chapter records. This is only a formal internal-bar input to that open-direct-image route. The blueprint searches for augmentation, row collapse and inhomogeneous terms give no equivalent imported blueprint statement; `same_as` remains empty.

## Unfinished work

None for the stage-1 item. The dependencies retain their existing states; I have not formalized or proved Lean code. The independent maintainer review remains part of the delivery process.

## Not duplicates

There are no new nodes. In particular, I reuse `thm-sp-double-complex-spectral-sequences`, `lem-weil-pbc-first-quadrant-row-collapse`, `lem-sfb-condensed-bar-total-naturality`, `lem-weil-pbc-right-adjoint-preserves-limits`, and `lem-sp-derived-injective-resolution-naturality`. No new node repackages one clause of the item or the whole augmentation theorem.

## Searches and Mathlib verdict

I retained the inherited searches and added only searches actually run with the required msearch command for Q45. The two new LeanFinder phrasings ask for the bottom-cycle-row augmentation under positive-E2-row vanishing. They return generic quasi-isomorphism/truncation lemmas and total-summand inclusion identities, not this criterion with its specified bar augmentation. LeanSearch returns generic homology and quasi-isomorphism declarations. Loogle `CategoryTheory.InjectiveResolution, Homotopy` returns `descHomotopy`, `descHomotopyZero`, `descIdHomotopy`, and `descCompHomotopy`; I read their signatures and Resolution.lean around lines 90–180. These are already represented by existing resolution/bar-total tools and do not state the item. The logged grep for quasi-isomorphism/acyclicity versus total/spectral terms in Algebra/Homology has no hits. Every Q45 record uses the exact query and tool in searches.jsonl; all services returned successfully. No new leaf is claimed.

## Review by Q45

I read `coord/delivery-errors.md` B–E, in both copies in that file, against the completed node, and checked the mathematical content rather than relying on the mechanical pass. For the item I read Stacks `homology.tex`, labels `lemma-ss-double-complex`, `lemma-first-quadrant-ss`, and `lemma-double-complex-gives-resolution` (Tags 0130, 0132, 0133). I also read `derived.tex`, labels `lemma-morphisms-lift` and `lemma-morphisms-equal-up-to-homotopy` (013P, 013S), including their bounded-below/injective hypotheses. The tag-to-label mapping was checked in the local Stacks tags file. There are no new nodes needing a separate source review. The latest blueprint's paragraph (3) motivates the application but supplies neither the positive-row argument nor a replacement for derived internal Hom.

For step 1, `def-sfb-condensed-equivariant-bar-data` really specifies the first action face, the common nonnegative resolution, and the total differential. `def-sp-double-complex-total` really specifies the coprojections and sign convention. Equivariance of the specified augmentation handles the first face; naturality handles the other faces. The identity d_I s=0 kills the only unwanted vertical term. Thus the actual cochain map, including its components, is constructed.

For step 2, I checked the compatible data's exact forgetful-functor clause, and the last sentences of `lem-sfb-condensed-derived-invariant-bar`, which explicitly say that internal module Hom is right adjoint to internal tensor and is derived in its second variable. `lem-weil-pbc-right-adjoint-preserves-limits` applies to the finite kernel diagram; it has no exactness/projectivity assumption. This yields C^p=H^0 of the column by the kernel inclusion, naturally for all bar faces. I initially considered the generic sheaf tensor–Hom statement, then used this existing condensed-internal statement directly so the proof needs no unstated encoding comparison. I did not infer vanishing of higher internal Hom from left exactness.

For step 3, I opened `thm-sp-double-complex-spectral-sequences`: it gives exactly E1=vertical cohomology, E2=horizontal cohomology of that, finite image filtrations, convergence, and functoriality for double-complex maps. I checked `lem-weil-pbc-first-quadrant-row-collapse`: it gives the edge from E2^(n,0) into H^n as an isomorphism under the precise positive-row assumption, not merely an abstract isomorphism of objects. Applying both results to J and D and to alpha makes H^n(a_I) the bottom map in the edge square. No general spectral-sequence-comparison theorem is being assumed without a node. Every index is nonnegative, each total degree has at most n+1 summands, and n<0 is zero. This is internal module cohomology throughout; I never evaluate on a profinite test object and assert exactness of that evaluation.

For step 4, I checked that its only assertions are the functorial equation f^0 s^0=s'^0 followed by fixed coprojections, and cancellation of the two already-established isomorphisms on cohomology. `def-weil-abstract-derived-category` defines the cohomology functors and quasi-isomorphisms used here. No columnwise acyclicity is used to prove the total comparison. These are elementary consequences of steps 1–3.

For step 5, `lem-sfb-condensed-bar-total-naturality` states the total homotopy with (-1)^p, existence of lifts between nonnegative equivariant injective resolutions, equality after localization, canonical derived-unit comparisons and identity/composition compatibility. Its internal condensed-ring setting and actual action-dependent bar complex match this item; its exact/injective-preserving U hypothesis is supplied by the assumed compatible data. I checked the signs explicitly: horizontal terms differ by a minus sign, while the two vertical signs multiply to +1. This is a citation of its statement, not of an auxiliary construction buried in its proof. Homotopic maps are equal under the localization of `def-weil-abstract-derived-category`.

For step 6, `lem-sp-derived-injective-resolution-naturality` specifies the comparison obtained from the fixed augmentation and inverse unit on injectives, and its assembly for a whole diagram. All complexes used here are nonnegative and their chosen resolutions have injective terms; the compatible data makes their underlying resolutions valid simultaneously for the columns. The bar-total naturality statement identifies comparison lifts with the derived internal-Hom maps. The interface definition fixes the augmentation and each summand of the compatible comparisons. Thus the argument concerns Q(a_I), not an arbitrary isomorphism replacing it. I declared this generic off-unit lemma, the double-complex spectral-sequence theorem and the row-collapse lemma in `split_report.tool_uses`; these provide formal categorical tools and do not change the unit's geometric route.

For step 7, the definition of quasi-isomorphism gives V_(I,q)^p=0 for q>0 under the stronger column condition; the row is consequently the zero complex. This is a two-line sufficient-special-case check, not a new node and not an extra assumption on the main proof.

For step 8, I checked the invariant sections after every profinite base change in `def-sfb-condensed-action-module` and the bar-zero augmentation in the compatible-data definition. In degree zero the two faces agree precisely because the action on N is trivial. A total zero-cycle is simultaneously vertically closed and invariant, since the two outgoing summands are separate; via the kernel inclusion s^0 this is exactly N. The square is already b_I u=a_I c on complexes: both maps are s^0 in degree zero, and the other source terms vanish. This checks the identification with the identity and the required compatibility, not just an unnormalized degree-zero isomorphism.

I tested the formal argument at N=0, the zero ring, G=1, total degree zero, and the boundary q=0. None requires a positive-degree source term or a sign at a negative index. For a genuinely weaker positive-row hypothesis, consider vector-space bicomplex data with D^(0,0)=N, D^(0,1)=k, D^(1,1)=k, horizontal differential k→k the identity and all vertical maps zero. Its positive vertical cohomology row is acyclic although the two individual columns have nonzero H^1; the total is N together with the contractible k→k summand. This tests the spectral-sequence argument without falsely assuming column acyclicity. This illustrative generic test is not claimed to be a new bar model or a new DAG theorem.

The statement is self-contained through its existing statement dependencies, no new data definitions are introduced, and no sorry or new axiom appears. All cited statements were opened and copied into citations.json. I checked that the chosen proof dependencies have no path back to the item. All eight proof steps are shorter than 1000 characters, so no step crosses the 2000-character hidden-lemma threshold. No SGA source is used. The server review_split check passed before the final report; the full delivery dry run is the final mechanical gate.
