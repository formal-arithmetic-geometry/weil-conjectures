1. Files written:

- `dag/nodes/sec-picard-framework/lem-pc-perfect-affine-bounded-projective.json`: split item, no new nodes; Mathlib searches found no scheme-level match.
- `citations.json`: verbatim dependency quotes for all proof steps.

2. Attachments: none.

3. WANTED: none.

4. What was checked: the source is Stacks `perfect.tex`, Lemma `perfect-lemma-perfect-affine` (Tag 08EB), whose proof reduces the affine scheme statement to the affine derived comparison and the ring definition of perfectness (Definition 0656). The existing node `lem-pc-affine-qcoh-derived-equivalence` states the required equivalence between `D(A)` and `D_QCoh(O_Y)`, and `def-pc-perfect-complex` states both strict perfectness and its bounded finite-projective affine description. Step 1 uses exactly those two statements to transport the problem to modules. Step 2 checks the forward implication under the hypotheses of the definition and the affine equivalence. Step 3 is the direct two-line converse: finite projectives are direct summands of finite free modules, so their associated bounded complex is strictly perfect. I verified the item’s ring, affine, and derived-category hypotheses and tested the zero complex and a one-term finite free complex as edge cases. The prior `lem-pc-perfect-affine-model` was not recreated because the ledger records it as a duplicate of this item.

5. What remains: no unresolved proof or node dependencies.

## Review by E1

I read the item, `def-pc-perfect-complex`, and `lem-pc-affine-qcoh-derived-equivalence`, plus the Tag 08EB source. Each cited node says exactly what its step takes: the affine equivalence supplies the module/sheaf identification, while the definition supplies the local strictly-perfect and finite-projective clauses. The only elementary step is the converse direct-summand argument. I also checked that the statement is not already a sorry-free Lean declaration and that the four recorded Mathlib searches were actually run; LeanSearch was recorded as unavailable. No new node was introduced, so there are no duplicate-node or additional-source checks.

## Second reading by E1

- Item statement: checked against Stacks `perfect.tex`, Lemma `perfect-lemma-perfect-affine` (Tag 08EB), and its reduction to pseudo-coherence, finite Tor dimension, and the affine module criterion; hypotheses and the `D_{\\mathrm{QCoh}}` setting agree.
- Step 1: checked against the statements of `lem-pc-affine-qcoh-derived-equivalence` and `def-pc-perfect-complex`; the transport to the affine module description is stated.
- Step 2: the original citation was circular because it invoked Tag 08EB itself. Replaced it with the source proof's actual reduction, citing `def-pur-pseudo-coherent-complex`, `lem-pc-affine-tor-amplitude-criterion`, `lem-pc-ring-pseudo-coherent-finite-tor-perfect`, and the affine equivalence.
- Step 3: checked on the zero complex and one-term finite free complex; expanded the direct-summand argument and verified it uses only `def-pc-perfect-complex`.
- New nodes: none; searched existing DAG nodes and Mathlib logs, and retained the four recorded searches (LeanSearch unavailable is recorded as unavailable).
- Changed the forward proof and `proof_deps` to remove the circular self-application and expose the affine reduction; added verbatim dependency quotes for every newly cited node.
