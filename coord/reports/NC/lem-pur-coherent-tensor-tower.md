# Stage-1 delivery: lem-pur-coherent-tensor-tower

## Files written

- `dag/nodes/sec-smooth-purity/lem-pur-coherent-tensor-tower.json`: statement split into five proof steps, using existing nodes only; not a Mathlib leaf.
- `citations.json`: twelve step/node entries, each checked against the live cited statement, with a verbatim quote.
- `searches.jsonl`: actual NC search-command records. The item's inherited NF search records remain in the node unchanged and attributed by their original timestamps; they are not claimed as searches run by NC.
- `report.md`: this report. `write_split.py` is a sandbox-only preparation helper, not a delivery node.

New nodes: 0. New Mathlib leaves: 0. No unit or chapter records changed.

## Attachments

None. A search of `lean/WeilConjectures/` for the exact blueprint tag, `pullbackTensorTensorTower`, and the coherent-tensor-tower notion found no exact finished declaration. The inherited candidate records `WeilConjectures.pullbackTensorTensorTower_existsUnique` in `Sheaf.Paper.CompletedPullbackTowerRealizations`, but that file is not present in the shared read clone. Its recorded exact header and the resolved parent repair order explicitly describe a sorried obligation, not a finished upstream attachment. The candidate ownership/header is retained.

## WANTED

None: all mathematical source text used is available locally. No Lean writing, compiler, Lake, or build command was used.

## What needed repair

The statement itself is retained byte-for-byte. Its normalization, arbitrary-unbounded-input quantifiers, strict tower conclusion, prescribed components, and uniqueness are unchanged. The item was unsplit with only the parent's retained old step 9. That inherited argument said that the reduction maps preserve units and that tensor generators give compatibility, without actually deriving the quotient-transition square or identifying a cited statement for cochain tensor compatibility.

Step 1 now proves the reduction square from the *given* transpose normalization and the actual limit-cone equation. Steps 2 and 3 cite the existing cochain pullback/tensor theorem, the exact-model semilinear evaluation theorem, and the ordinary cochain horizontal-reduction theorem. This avoids taking cochain normalization from a node whose statement only describes derived evaluation. Step 4 explicitly pastes these squares with the target quotient-tensor transitions. Step 5 constructs the inverse strict morphism and proves uniqueness componentwise.

There were no archived attempts at the assignment's archive glob, and the active sandbox contained only dispatcher markers. I copied the current live node and retained its original statement, provenance, searches, candidate header, and old construction argument. The parent repair note is resolved and assigns this particular extracted theorem to a separate item; it imposes no further new-node quota on this item.

The inherited blueprint ancestry is broken: `blueprint_refs.py ancestor lem-pur-coherent-tensor-tower` returns `None`. I retained that recorded null ancestry and its explanatory place/via fields, rather than inventing an ancestor or editing the parent. The current blueprint is `literature/blueprint/latest` (main-20261026). I read the current purity-conventions unit, smooth-purity chapter, and `def-weil-frobenius-coefficient-twists.md`. The latter's clause that actions commute with finite reduction is the inherited documentary association; it does not itself state this strict tensor-tower theorem. The imported unit record still has its older chapter placement, which this delivery does not edit.

## Search and reuse

The whole-DAG and blueprint searches included coherent reduction, semilinear systems, tensor evaluation, tensor towers, and quotient transitions, as well as the relevant declaration names. The current blueprint search found no exact tensor-tower statement. The broader hits concern coefficient actions, completed-operation or proper-base-change comparisons, with additional hypotheses or different maps. They are not this item.

I opened the complete statements of every node cited in every step. In particular:

- `lem-pur-cochain-pullback-tensor-coherence` explicitly supplies an isomorphism of ordinary total tensor complexes for arbitrary unbounded complexes, and its pure-tensor normalization.
- `lem-coef-semilinear-tensor-evaluation` supplies the tensor comparison for the *chosen* models and fixes its ordinary comparison and chain summands.
- `lem-pur-system-cochain-tensor-reduction` is the ordinary cochain tensor/horizontal-adjoint identity, without flatness or boundedness; the associated source file `lean/Sheaf/Paper/SystemCochainTensorReduction.lean` was read as corroboration, not as a finished upstream attachment.

No new lemma was needed. The final tower assembly is just the definition of a natural transformation and its componentwise inverse. The short unit/cone calculation also should not become a new lemma under the brief's elementary-node rule.

Fresh Mathlib searches used only the required `msearch.py` command: LeanSearch, two distinct LeanFinder phrasings, Loogle `CategoryTheory.NatIso.ofComponents`, and source grep for evaluation/tensor/tower expressions. All services answered. The semantic hits were generic tensor-complex constructions, scalar towers and quotient modules. Loogle gives the general natural-isomorphism assembly constructor, not the ringed sequence-site comparison or its transition normalization. These searches and their returned records are appended to the inherited item's `mathlib_searches` with no-match verdicts for the complete item. There are no newly created nodes requiring separate searches.

## Not duplicates

No new nodes, so there are no new/existing pairs to justify. Existing statements are reused rather than restated.

## Review by NC

I read Stacks `sites-cohomology.tex`, Tag 07A4 (`lemma-pullback-tensor-product`) and its proof, and the sequence-site construction immediately before Tag 0941 (`lemma-derived-limit-is-ok`). The first uses the ordinary direct-sum total comparison on representatives, while the second gives actual evaluation and inverse-system maps. I also read `sites-modules.tex`, Tag 03EK (`section-tensor-product`), including its presheaf definition, sheafification, scalar-extension formula, and bilinear universal property. The item's strict simultaneous normalization is an agent-written assembly of these constructions and existing DAG tools, and `proof_origin.by` says `agent`; neither Stacks tag is falsely claimed to state the full item. There are no new nodes for which additional source assertions need review.

For step 1 I checked the actual sequence-site definition gives the underlying horizontal maps and that the two module-tensor/sheafification nodes give exactly the construction and uniqueness used to pass from pure tensors to maps. The hypothesis on `a_n` is already in the item: its scalar transpose is `pi_n` after the ordinary adjunction unit. Thus its generator value is forced to be `b nu_n(x)`. The limit-cone equation yields the displayed transition calculation; no flatness, epimorphism on sections, or normalization/completeness of an input is used. Naturality then applies to each differential. This is a written elementary calculation, not a new unproved scalar-comparison lemma.

For step 2 I verified that evaluation really is the vertical inverse-image functor with coefficient identification in the cited sequence-site statement. Hence the hypotheses of the ordinary cochain pullback/tensor lemma are met on the small ringed sequence site. That lemma explicitly covers unbounded inputs. The exact-model evaluation lemma fixes the ordinary comparison and each chain summand; the direct-sum universal property identifies its chosen chain map with the inverse of the displayed forward total isomorphism. This checks the inverse direction as well as the absence of a sign or scalar automorphism. The total-tensor definition supplies the direct sums and signed differential.

For step 3 I checked the cochain-reduction node states precisely the comparison of scalar tensor, evaluated chain tensor, and the two horizontal adjoints. Its hypotheses are arbitrary strict systems over arbitrary ring-sheaf towers. The item has such systems by its sequence-site construction. Transposing that stated identity gives the actual semilinear transition square; restriction along the compatible limit projections leaves its section maps unchanged. This is an ordinary cochain assertion, so it does not invoke reconstruction from derived evaluations or faithfulness of derived evaluation. The quoted statement includes the needed compatibility, unlike a mere definition of horizontal adjoints.

For step 4 I checked that the integral-operation definition uses the actual quotient transitions on both inputs and that the core definition specifies the reordering into completed-module towers. The exact component composite in the item is retained. Tensor functoriality and pasting steps 1 and 3 give the displayed strict square; the local formula writes out what the target transition does. Finite composites give all `m >= n` arrows. There is no inverse limit calculation in this step.

For step 5 every factor is already an ordinary cochain isomorphism. Multiplying the forward transition equation by its component inverses proves inverse compatibility directly. Identities and equality of natural transformations are componentwise, so existence and uniqueness require no hidden representability or derived-lifting theorem. I verified that the statement requires uniqueness for each fixed pair `P,Q`, which is what the step proves.

I checked B1-B10: no statement-only new node is falsely marked split, no new statement lacks objects or definitions, inherited TeX is unchanged, all source tags/labels used were read, no Mathlib match or attachment is claimed, and ancestry/search provenance is retained. I checked C1-C8: the non-elementary chain identities have exact cited statements; all twelve citations are verbatim statement excerpts; no argument is borrowed merely from a cited node's proof. The two off-unit statement tools are declared in `split_report.tool_uses`, with their generic use explained; the ordinary cochain tensor theorem is already in this item's unit. A dependency traversal found no path from these statement tools back to this item. I checked D1-D5: the five steps contain the actual unit calculation, comparison identification, transition pasting, and inverse/uniqueness argument, and no clause was moved into a new node. I checked E1-E7 on the equations: ring maps are the actual `B_(n+1) -> B_n`, both scalar projections have the correct direction, and no coefficient-flatness or invertibility-of-ell hypothesis entered.

Small cases checked: `P=0` or `Q=0` gives the unique zero-complex tower isomorphism. For degree-zero modules the square is exactly `(b tensor x) tensor (c tensor y)` reducing both scalars by `tau_n`. For arbitrary degrees `(p,q)`, none of the comparisons permutes the factors, so the differential has the same `(-1)^p` on both routes, including negative degrees. The first level is `B_0=O_E/varpi`, not the zero quotient `O_E/varpi^0`. Equal-index transitions are identities; longer transitions are finite composites. The small site makes every countable total sum legitimate. All steps are below 2000 characters; there is no concealed long-step lemma.

## Unfinished work

None within this stage-1 item. The reused nodes retain their own existing proof/Lean statuses; this delivery makes no claim to finish their Lean proofs or the whole project. Dry-run and push results are recorded below once the required commands finish.
