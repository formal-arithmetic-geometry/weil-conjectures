Files written:

- `lem-kun-closed-point-field.json`: item split, no new nodes, 0 Mathlib leaves created.
- `citations.json`: verbatim quotes for every cited node.

Attachments: none.

WANTED: none.

The imported proof compressed the affine maximal-ideal argument and the transcendence-degree equivalence into one paragraph. I expanded those arguments and removed the unused support dependency. The existing DAG already contains the Zariski lemma and the finite-transcendence-basis result, so I did not create duplicates.

## Review by F1

I read the item's blueprint proof and checked the corresponding definitions in `def-weil-pbc-scheme-conventions` and `def-kun-transcendence-degree`. I read the statements of `lem-weil-pbc-zariski-lemma` and `lem-weil-pbc-finitely-generated-field-finite-transcendence-basis`; the first supplies finiteness for a field finitely generated over a field, and the second supplies a finite transcendence basis for the residue field extension. I also read both separably closed extension nodes: their hypotheses exactly match the closed-point residue extension obtained in part (a), and their conclusions are precisely pure inseparability and separable closedness.

The proof checks the affine chart and prime/maximal correspondence, applies the Zariski lemma to a maximal quotient, proves the converse by embedding the domain quotient into the finite-dimensional residue field and using injective linear multiplication, then derives the equivalence with transcendence degree zero from the finite transcendence basis. The final clause applies the two cited separably closed field statements. I tested the algebraic assertions on `Spec K`, `Spec K[t]` at `(0)` and `(t-a)`, and a finite purely inseparable extension of a separably closed field. Mathlib searches were run for the item; LeanSearch was unavailable and recorded as such.

## Second reading by F1

- Step 1: checked against the imported blueprint node and every cited DAG statement; the affine reduction, maximality criterion, finite-dimensional converse, transcendence-degree equivalence, and separably closed conclusion are valid under the stated hypotheses after the repair below.
- New nodes: none; the split creates no node files, so B1-B7 and duplicate-node checks are vacuous.
- Small cases: checked `Spec K`, `Spec K[t]` at `(0)` and `(t-a)`, the zero-dimensional affine case, and finite purely inseparable extensions of a separably closed field.
- Changed the finite-residue-field converse so `A/\\mathfrak p` is explicitly a finite-dimensional `K`-subspace of `\\kappa(x)`; multiplication surjectivity therefore yields an inverse in `A/\\mathfrak p`.
- Added `def-weil-residue-field` to `stmt_deps`, since `\\kappa(x)` is used in the statement.
- Rechecked `citations.json`: all four quotes remain verbatim and support the facts used; no citation changes were needed.
