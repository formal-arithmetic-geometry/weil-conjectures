# Stage 1 report

Files written:

- `dag/nodes/sec-picard-framework/lem-pc-finite-inseparable-element.json` — item, statement split, no new nodes, Mathlib no-match.
- `citations.json` — verbatim citations for both proof steps.

Attachments: none.

WANTED: none.

What was wrong in the imported item: `def-pc-field-tower` was omitted from `stmt_deps`, even though it supplies the meaning of “finite” and the finite-to-algebraic observation used in the proof. No statement or source error was found.

What I could not finish: nothing; the dry run passed.

## Review by H1

I checked the item against Stacks Algebra, Lemma Tag 030W, implication (1) => (4) contrapositively, and retained its statement. There is no declaration carrying the blueprint tag in the project Lean source. I also checked the existing DAG for the same 030W consequence and for matching minimal-polynomial language; the only related item is the parent that cites this node, so no duplicate or intermediate node was created.

Step 1 uses the finite/algebraic definitions in `def-pc-field-tower` and `def-weil-algebraic-element`, and the clauses of `def-weil-pbc-separable-field-extension` and `def-weil-pbc-separable-algebraic-extension`. The finite-dimensional linear-dependence argument gives algebraicity, a finite basis gives finite field generation, and the empty transcendence basis handles the separably-generated definition. Step 2 is the direct negation: if every element had a separable minimal polynomial, Step 1 would contradict the hypothesis that the extension is not separable. The cited definitions state exactly these uses, and the elementary flags apply only to these short definitional arguments.

I added `def-pc-field-tower` to `stmt_deps`, since the imported statement's finite-extension hypothesis was previously attributed only to the field-extension definition. I ran LeanFinder, Loogle, grep, and LeanSearch through `msearch.py`; the first three returned only related purely-inseparable/minimal-polynomial declarations, while LeanSearch was unavailable (HTTP 500), so the item remains unsplit rather than a Mathlib leaf.

## Not duplicates

`lem-pc-finite-inseparable-element` vs `lem-pc-finite-extension-tensor-algebraic-closure-reduced-separable`: the existing node proves a tensor-product reducedness criterion and uses this item; it does not state the finite-extension contrapositive.

## Second reading by H1

- Item statement: checked against Stacks Algebra Tag 030W, implication (1) => (4) contrapositively; the finite extension and nonseparability hypotheses and the inseparable-minimal-polynomial conclusion agree.
- Step 1: checked against the statements of `def-pc-field-tower`, `def-weil-algebraic-element`, `def-weil-pbc-separable-field-extension`, and `def-weil-pbc-separable-algebraic-extension`; expanded the argument for every finitely generated intermediate field, including finiteness, the empty transcendence basis, and the two clauses of separability.
- Step 2: checked against the two separability-definition statements and the contrapositive of Step 1; the negation now supplies an element whose minimal polynomial is not separable.
- New nodes: none; there are no new-node B1-B7 checks, and the existing-node search found no duplicate statement (the tensor-product node is strictly different).
- Small cases checked: degree-one extension (the hypothesis is false), a separable finite field extension (no inseparable element), and a finite purely inseparable extension in characteristic $p$ (a generator has inseparable minimal polynomial); no zero-object or empty-scheme cases apply to field extensions.

Changes: expanded Step 1 to handle all finitely generated intermediate fields required by Definition 030O; retained the corrected `def-pc-field-tower` dependency and the existing two-step structure.
