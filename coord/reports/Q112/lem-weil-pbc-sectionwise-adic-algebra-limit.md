# Stage-1 report

1. Files written: `dag/nodes/sec-proper-base-change/lem-weil-pbc-sectionwise-adic-algebra-limit.json` (statement, split; no Mathlib match). Auxiliary files: `citations.json`, `searches.jsonl`, and `prepare.py`. No new nodes and no new Mathlib leaves. The sandbox initially contained only dispatcher markers; the item was copied from the current read-only DAG. No repository or launcher file was changed, and no compiler, Lake or build command was run.
2. Attachments: none. Searches of the full live `lean/WeilConjectures/` for the exact blueprint id and for sectionwise/adic-limit concepts found no declaration stating the item. The adic-lattice and ordinary coefficient-completion declarations do not state this arbitrary-site, varying-algebra theorem.
3. WANTED: none.
4. The imported item had no proof. Its algebra input already exists as `lem-weil-pbc-limit-flat-modules` (Tag 0912), so no second node is created for that fact. Its blanket final tensor convention was ambiguous in scope; see the type clarification below. I preserved all hypotheses and every substantive conclusion.
5. Unfinished: none at stage 1. The proof is a natural-language split, not a claim that Lean proofs have been supplied.

## Statement clarification

STATEMENT-DISPUTED: a literal application of the final sentence “tensor products mean sheafified module tensor products” to the displayed expression `B(U) tensor_A F` is ill-typed: `B(U)` and `F` are ordinary modules, not sheaves. I corrected only that scope, specifying ordinary tensor products for modules of sections and sheafified tensor products for sheaves. The sectionwise statement is exactly the ordinary-module conclusion of Stacks Tag 0912. No section functor is claimed to commute with sheaf tensor products in general.

## Sources and searches

I read Stacks `more-algebra.tex`, Tag 0912, label `lemma-limit-flat`, including the finite-free resolution and Tor/Mittag-Leffler proof. I read `sites-modules.tex`, Tag 093M, label `lemma-completion-flat`, including its sectionwise flatness proof and finite-generator quotient argument, and Tags 03ES/03ET, labels `lemma-flatness-presheaves`/`lemma-flatness-sheafification`. The present generalized tower needs the additional reduction compatibility already in the item; I supplied its stabilization and projection formulas explicitly and marked proof origin `agent`.

I read the chapter and unit records and current `main-20261015` completed-pullback definition. The ancestor is `def-weil-pbc-completed-pullback`, through `lem-weil-pbc-constant-completion-equivalence`, whose Step 1 requires this theorem. Current blueprint searches for `flat limit`, `completion-flat`, `adic algebra`, and `flat`, together with whole-DAG source-tag and statement searches, found no second blueprint statement of this generalized theorem. The existing ordinary-module and sheafification statements are reused. Their off-unit uses are declared as generic tools in `split_report.tool_uses`.

All new Mathlib searches were made with the prescribed `msearch.py`; their actual summaries are recorded in the node and `searches.jsonl`. Two LeanFinder phrasings, LeanSearch, Loogle and source grep lead to ordinary `AdicCompletion` results or abstract sheaf limits. I read `Mathlib/RingTheory/AdicCompletion/AsTensorProduct.lean`, in particular the finite-module comparison around lines 318–360. Those results concern completion of one fixed ring/module, not an arbitrary varying sheaf-algebra tower. The previous item's search evidence is retained as inherited evidence.

## Not duplicates

No new nodes. In particular the ordinary module tower result is cited as `lem-weil-pbc-limit-flat-modules`, and sheafification flatness as `lem-pc-sites-modules-sheafification-flat`.

## Review by Q112

I checked delivery-errors B–E against the actual statements and sources, including their repeated B section. There are no new statement-only nodes, unsupported Mathlib matches, or new blueprint provenance records to audit. The item retains its ancestor and via chain, and `same_as` is filled after searching. Every proof step is below 2000 characters, so no long step conceals a separate comparison lemma.

Step 1 uses the sectionwise computation actually stated by `def-pur-sheaf-inverse-limit`, including its ring-sheaf clause, and the full flatness/finite-tensor conclusion of `lem-weil-pbc-limit-flat-modules`. I verified annihilation, quotient-ring flatness, linearity, and surjectivity separately. Tensor symmetry and naturality are given by formulas on pure tensors rather than asserted without explanation.

Step 2 uses `lem-weil-pbc-flat-tensor-exact` for exact sequences over A, and `lem-pc-sites-modules-sheafification-flat` with its actual hypothesis of a PRESHEAF base ring. `def-weil-pbc-constant-sheaf` identifies that base's sheafification with R. This avoids the incorrect inference that flatness of B(U) over A directly implies flatness over the generally larger R(U). I wrote the kernel and finite-product comparisons, including empty products, and checked their restriction compatibility. The existing sectionwise-flat-presheaf node assumes a SHEAF base ring and was deliberately not misapplied here.

Step 3 is elementary after Step 1: the inverse tensor/quotient formulas are written out; the reduced tower's constant tail has an explicit inverse from S_n(U). I checked that the given transition-induced identifications commute by their pure-tensor formula, rather than assuming arbitrary isomorphisms commute. The resulting quotient map sends b to its original nth coordinate, proving multiplicativity as well as linearity. This proves no lemma by citing a node whose proof contains the needed fact.

Step 4 uses the finite-generation statement actually in `def-weil-pbc-noetherian-ring` for the ideal I^n and the cokernel preservation actually in clause 2 of `lem-weil-pbc-sheafification-exact`. The finite-generator action has sectionwise image I^nB(U), so its sheaf cokernel is exactly the quotient convention in the item. The presheaf quotient is already isomorphic to S_n; thus no unjustified exactness of arbitrary sections is used.

Step 5 is an elementary equality on representatives using the explicit projection normalization established in Steps 3–4. It verifies all transitions, rather than substituting an abstractly isomorphic quotient object. `citations.json` copies verbatim the statements of all cited nodes, one entry for each step/node pair.

I tested I=0 (reduction compatibility forces all tower maps to be isomorphisms), I=A (all levels and the limit are zero), the zero ring, the zero finite module, n=1, identity/composite transitions, and objects admitting an empty covering (their sheaf sections are zero). None requires a nonempty topos or points. The finite-tensor conclusion needs Noetherianity through Tag 0912; finite generation of I^n is also used explicitly for the sheaf quotient. The additional reduction-isomorphism hypothesis is used precisely to identify the stable reduced tail, not to derive the ordinary flat-limit theorem. No route through SGA is used.
