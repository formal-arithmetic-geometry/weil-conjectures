Files written:

- `dag/nodes/sec-picard-framework/lem-pc-affine-qcoh-derived-equivalence.json`: statement split; no new node; no Mathlib leaf.
- `citations.json`: verbatim statement excerpts for every proof dependency of every step.

Attachments: none.

WANTED: none.

No statement error was found. The imported item already has the precise Tag 06Z0 formulation. The existing `lem-weil-pbc-affine-tilde-gamma-adjunction` node supplies the ordinary affine module/sheaf equivalence, so creating a second module-equivalence node would be a duplicate. The existing `lem-pc-affine-morphism-hi` and `lem-sc-qcoh-acyclic-derived-pushforward-cohomology` nodes supply affine acyclicity and the unbounded derived cohomology comparison. No new child node was needed.

## Review by H1

I read the item against Stacks `perfect.tex`, Section 36.3, Lemma 36.3.5 (Tag 06Z0), and read the full statements of `lem-weil-pbc-affine-tilde-gamma-adjunction`, `lem-pc-affine-morphism-hi`, and `lem-sc-qcoh-acyclic-derived-pushforward-cohomology`. Step 1 uses exactly the first node's adjunction, unit, and counit clauses; its hypotheses specialize from a ring R and affine Spec(R) to the given ring A and Y=Spec(A). Step 2 checks the structure morphism Y -> Spec(Z) is affine, applies the higher-direct-image vanishing node and then the derived cohomology comparison, and uses the ordinary counit clause on each quasi-coherent cohomology sheaf. Step 3 uses the same comparison and unit clause degree by degree to prove the derived unit is a quasi-isomorphism, so the two functors are quasi-inverse. Step 4 is the termwise affine tilde construction applied to the shifted free module A[k]. Every citation quote in `citations.json` is copied verbatim from the cited node statement. I tested the edge cases A=0 and k=0 conceptually: the zero affine scheme gives the zero equivalence, while degree-zero A maps to O_Y. No source correction or dependency repair was required.

What could not be finished: nothing; the required proof split and citation audit are complete.


## Second reading by H1

- Item statement: checked against Stacks `perfect.tex`, Lemma 36.3.5, Tag 06Z0; hypotheses (affine `Y=Spec(A)`, quasi-coherent derived category, derived global sections, and all `k`) agree.
- Step 1: checked the ordinary affine module/sheaf adjunction node and the Tag 06Z0 elucidation; repaired the step to state exactness of the abelian equivalence before passing to derived categories.
- Step 2: checked affine acyclicity and the unbounded cohomology comparison nodes; repaired the step to name the structure map `Y -> Spec(Z)` and the affine-base global-sections identification, preserving the `A`-module structure.
- Step 3: checked the unit clause and Step 2 comparison; repaired the cohomology calculation so the derived unit is proved degree by degree and the quasi-inverse conclusion follows from the two unit/counit quasi-isomorphisms.
- Step 4: checked the shifted-complex clause against the termwise tilde definition; expanded the degree `-k` calculation and removed the vague “unit formula” reference.
- Existing node: the only node in this split is the item itself; its statement is self-contained with definition dependencies, correct Tag 06Z0 source, blueprint ancestry, and recorded Mathlib searches. No new child nodes or Mathlib leaves were needed; duplicate searches found the ordinary affine equivalence already present.
- Edge cases checked: `A=0` gives the zero affine scheme and zero complexes; `A` a field gives the standard affine point equivalence; `k=0` gives `A` and `O_Y` in degree zero; arbitrary negative `k` is handled by the same shift calculation.
- Changes made: repaired proof steps 1–4 as above; retained all existing citations because each cited statement remains exactly the dependency used.
