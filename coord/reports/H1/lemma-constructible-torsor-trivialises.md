1. Files written:

- `dag/nodes/sec-proper-base-change/lemma-constructible-torsor-trivialises.json`: repaired statement dependencies, two-step proof, blueprint metadata, and split report.
- `dag/nodes/sec-proper-base-change/def-constructible-torsor.json`: new statement-only definition node for general (possibly non-commutative) sheaf torsors, with no Mathlib match.
- `citations.json`: verbatim quotes for both proof steps.

2. Attachments:

- No Lean declaration attachment; the target has no matching declaration in `weil-src-slopmaster2`.

3. WANTED:

- None. The definition is sourced from Stacks Project `sites-cohomology.tex`, Definition 03AH (label `definition-torsor`).

4. What was corrected:

- The returned version had no definition node for the notion of a torsor under a possibly non-commutative sheaf of groups. I added `def-constructible-torsor`, stating the action, simple transitivity when sections exist, local nonemptiness on every etale object, and triviality by equivariant isomorphism with left translation.
- The returned proof incorrectly asserted finite-local-constant representability and cited `lem-galois-flc-representable`; that route is unnecessary and was removed from the proof, `proof_deps`, and citations. The finite-local-constant hypothesis remains a statement dependency because it remains in the item statement, while the proof explicitly records that finiteness and the blueprint's SGA 4 representability argument are not needed for this conclusion under 03AH.

## Review by H1

I reread the item source in the imported blueprint and the Stacks source `sites-cohomology.tex`, Definition 03AH, label `definition-torsor`. I also opened the existing `def-constructible-finite-locally-constant` node and confirmed that it only defines the finiteness/local-constancy hypothesis; it does not define torsors. A search of the DAG and blueprint found no existing node stating the general 03AH definition, while the existing `def-sc-gm-torsor` concerns abelian groups on a different site, so it could not be reused.

Step 1 cites the new definition and uses exactly its local-nonemptiness clause with U = X to obtain an etale cover whose members have sections. Step 2 cites the same definition for the conditional simple-transitivity clause and the left-translation meaning of triviality. On each cover member U_i, a chosen section s_i restricts to every V -> U_i, so the map g |-> g.s_i is bijective on P(V); uniqueness and restriction compatibility make these bijections an equivariant sheaf isomorphism. The step is otherwise an elementary unpacking of the definition. I checked the empty/trivial edge case: for the trivial group, any chosen local section gives the identity translation map, and the conclusion is immediate.

The new node is statement-only as required for an unsplit definition. I recorded LeanSearch, LeanFinder, and Mathlib-source grep searches for the definition; none found a matching Mathlib notion. The item's blueprint `from.place` is filled, and its split report records that the finiteness hypothesis and representability detour are not needed.

5. What could not be finished:

- Nothing remains in the stage-1 split.
