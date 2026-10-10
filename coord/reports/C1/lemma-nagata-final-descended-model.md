Files written:

- `dag/nodes/sec-nagata-compactification/lemma-nagata-final-descended-model.json`: statement split into two proof steps; no new nodes.
- `citations.json`: verbatim citations for both steps.

Attachments: none.

WANTED: The imported blueprint source `literature/blueprint/master/blueprint/sec-nagata-compactification/sk-cor-nagata-sketch-fp/lemma-nagata-final-descended-model.md` is not present in this checkout; the split follows the proof text retained in the node and the cited DAG statements.

The imported proof had `lemma-nagata-separated-eventually` in `proof_deps` but did not cite it in its only step, so it did not establish separatedness, finite presentation, or the comparison isomorphism. I made those deductions explicit in step 1 and used the definition node to identify the selected separated stage and `epsilon_Y`. Step 2 applies the final Noetherian base-system statement to the selected stage. No new node was needed: both non-elementary facts already have DAG statements.

## Review by C1

I read the item statement and the definition node `def-nagata-final-descended-model`, then read the full statements of `lemma-nagata-separated-eventually` and `lemma-nagata-final-noetherian-base-system`. Step 1 uses exactly the separatedness, finite-presentation, and canonical base-change clauses of `lemma-nagata-separated-eventually`; the definition node supplies the identification of its notation with `Y_{lambda_Y}` and `epsilon_Y`. Step 2 uses the clause that every `S_lambda` in the final Noetherian system is Noetherian, with the definition node establishing that `S_{lambda_Y}` is such a stage. I checked that each citation quote is verbatim in `citations.json`, that the proof dependencies are the union of the step uses, and that the two steps jointly cover all three conclusions. The only correction was replacing the imported paragraph with these explicit cited steps and marking the item `split`.

## Second reading by C1

- Item statement: checked against the imported statement node and its definition dependency; the hypotheses and all three conclusions agree, including the comparison map being an isomorphism over `S`.
- Step 1: checked against the full statements of `def-nagata-final-descended-model` and `lemma-nagata-separated-eventually`; the selected index/model notation, separatedness, finite presentation, and canonical base-change comparison are all supplied, with no uncited non-elementary fact.
- Step 2: checked against the full statements of `def-nagata-final-descended-model` and `lemma-nagata-final-noetherian-base-system`; the selected stage is in the final system and hence Noetherian.
- New nodes: none; the proof uses existing DAG statements rather than introducing duplicates or restatements.
- Small cases: the statement is consistent for a field base and for the identity morphism (the selected model remains separated and finitely presented, and the comparison is an isomorphism); no empty-scheme or zero-object convention is involved, and no numerical parameter occurs.
- Citations: all four entries in `citations.json` were checked verbatim against the cited node statements; `proof_deps` is exactly the union of step uses.
- Changes: none after the first reading; the split already makes the imported proof's dependencies explicit and passes the mechanical delivery checks.
