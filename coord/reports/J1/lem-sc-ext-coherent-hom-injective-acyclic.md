Files written:

- `dag/nodes/sec-picard-framework/lem-sc-ext-coherent-hom-injective-acyclic.json`: statement split into three proof steps; no Mathlib match.
- `dag/nodes/sec-picard-framework/lem-sc-ext-coherent-hom-injective-flasque.json`: statement-only intermediate node; no Mathlib match.
- `citations.json`: verbatim citations for all three steps.

Attachments: none.

WANTED: none.

The imported item had no proof. The intermediate flasqueness fact is strictly smaller than the global acyclicity conclusion and is needed to connect the coherent Hom construction to the existing flasque-acyclicity theorem. I found no exact Lean declaration and no existing DAG or blueprint node stating that flasqueness fact. The item statement and its Noetherian, coherent, and injective hypotheses were left unchanged.

I could not finish a Lean proof because this is a stage-1 natural-language split; no Lean is written or built.

## Review by J1

I read the item, its unit `sk-thm-picard-duality`, chapter `sec-picard-framework`, and the source route through Stacks `equiv.tex`, Lemma `lemma-Ext-0-regular` (Tag 0FZ3), together with `sites-cohomology.tex` Tag 03FD and the flasque-acyclicity statement already in the DAG. I also searched the Lean source for the item tag and for coherent-Hom/injective/acyclic declarations; no sorry-free exact declaration exists. Blueprint searches for coherent Hom injectivity and coherent-sheaf injective flasqueness returned no matching node.

Step 1 cites the new node, whose statement explicitly supplies exactly the flasqueness of the underlying abelian internal Hom used by the step. Step 2 cites `lem-sc-zariski-flasque-acyclic`, and its statement directly says that a flasque abelian sheaf has zero positive Zariski cohomology. Step 3 cites `lem-sc-module-abelian-zariski-cohomology`, whose statement explicitly identifies module-sheaf cohomology with cohomology of the underlying abelian sheaf. I checked that each citation quote in `citations.json` is copied verbatim from its node statement, and that all three cited nodes occur in `proof_deps`.

I checked edge cases for the new statement: on the empty scheme the Hom sheaf is zero and flasque; on a one-point affine scheme the restriction condition is vacuous and higher cohomology vanishes; for a coherent skyscraper module on an affine Noetherian scheme the internal Hom is the corresponding module sheaf, consistent with the statement. The Mathlib searches recorded LeanSearch (unavailable), Loogle, and source grep for the new node; all found no matching declaration.
