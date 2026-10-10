Files written:

- `dag/nodes/sec-picard-framework/lem-pc-proper-support-descent.json` (item; split)
- `dag/nodes/sec-picard-framework/lem-pc-support-closed-subscheme-descent.json` (statement-only unsplit node; Mathlib searches found no match)

Attachments:

- None. No sorry-free declaration with the item statement was found under `WeilConjectures/`.

WANTED:

- None; the cited Stacks sources are represented by the project literature metadata.

What was checked and changed:

The item source is Limits Lemma 32.13.5, Tag 081G, used together with Cohomology of Schemes Lemma 30.26.7. I also read the existing DAG node `lem-weil-pbc-eventually-proper`, which states Tag 081F and supplies the finite-stage properness theorem needed after constructing a finite-stage support. The imported item had no proof and no Lean declaration. I added one supporting statement, `lem-pc-support-closed-subscheme-descent`, giving a self-contained inverse-system setup and the finite-stage closed support model; it is intentionally statement-only because its own proof is a separate Stacks result.

Step 1 uses exactly the helper's assertion that a locally finite type closed subscheme `Z_j` exists and that its pullback and underlying subset agree with the module support. Step 2 uses the existing 081F node's hypothesis and conclusion for a proper limit morphism with locally finite type stage morphism. Step 3 uses the helper's support identification and 081F's eventual properness, with only directed reindexing and base-change preservation treated as elementary. The support-proper hypothesis is carried to the morphism `Z\\to S`; finite presentation of `X_i` makes the stage support morphism locally of finite type.

I searched the DAG for Tags 081G, 30.26.7, support descent, and existing properness nodes. The existing 081F node is more general but does not state the module-support construction, so it is cited rather than duplicated. Mathlib searches were run for both the item and the new helper with LeanFinder, Loogle, grep, and LeanSearch; LeanSearch was unavailable and recorded as such. Small edge cases checked were `F_i=0` (empty support, for which the conclusion is immediate) and `F_i=O_{X_i}` (support all of `X_i`, reducing to ordinary properness descent).

## Review by G1

I read the imported item, the parent blueprint reference, the unit record, and the full statement and proof of `lem-weil-pbc-eventually-proper`. The new helper introduces every object it uses (`S_i`, `S`, `X_i`, `F_i`, `X_j`, `Z_j`) and states only the support-model construction, so it does not restate the item's properness conclusion. For each item step, the cited quote in `citations.json` is copied verbatim from the cited node: step 1 takes the helper's finite-stage support; step 2 takes 081F's properness-at-a-stage conclusion; step 3 takes both the support identification and the eventual properness conclusion. The hypotheses used in step 2 (proper limit support morphism and locally finite type stage morphism) are explicitly checked in the step text. The only elementary argument is the final directed reindexing and preservation under base change. No existing Lean declaration, DAG node with the same support-model statement, or Mathlib theorem was found.

## Not duplicates

lem-pc-support-closed-subscheme-descent vs lem-pc-proper-support-descent: the new node constructs a finite-stage closed support model and makes no properness conclusion; the existing item asserts eventual properness of the module support.
lem-pc-support-closed-subscheme-descent vs lem-pc-finite-flat-proper-support-descent: the new node concerns one finitely presented module's support model, while the existing node descends an entire bounded flat complex and properness of every term.
lem-pc-support-closed-subscheme-descent vs lem-pc-noetherian-approximation-data: the new node only constructs a finite-stage support closed subscheme, while the existing node simultaneously descends a scheme, complex, flatness, proper support, and a perfect object.

## Second reading by G1

- Item statement: checked against Limits Lemma 32.13.5 (Tag 081G) and Cohomology Lemma 0CYS / 30.26.7; the specialized affine Noetherian setup is sufficient for the cited application, and the zero-module and full-support cases behave correctly.
- Step 1: checked against scheme-theoretic support (Morphisms 05JU), finite-type support pullback (056J), and closed-subset properness (0CYL); the pullback closed subscheme has the proper underlying support, so its morphism to the limit is proper.
- Step 2: checked against Limits Lemma 081F; the support closed subscheme is locally of finite type over the Noetherian stage, satisfying the eventual-properness hypotheses.
- Step 3: checked against 056J, 05JU, and 0CYL; the underlying set of the descended closed subscheme is exactly the module support, and properness of the subscheme implies properness of that support.
- New helper node: removed; it duplicated existing scheme-theoretic support and support-properness results and asserted only an underlying-set identification, which was insufficient for the original 081F application.
- Changed the item proof to follow the source route through the existing support nodes and 081F, removed the helper from `proof_deps`, corrected the helper's erroneous `created.item` metadata, and refreshed `citations.json` with verbatim statements.
