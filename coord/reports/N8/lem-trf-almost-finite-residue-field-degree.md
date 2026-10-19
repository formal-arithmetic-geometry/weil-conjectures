## Files written

- `dag/nodes/sec-trace-formula/lem-trf-almost-finite-residue-field-degree.json`: statement unchanged; complete eight-step split.
- `dag/nodes/sec-trace-formula/lem-trf-normalization-completed-branch-lift.json`: statement-only, unsplit; no Mathlib match after two semantic formulations, LeanSearch, Loogle and source grep.
- `dag/nodes/sec-trace-formula/lem-trf-finite-domain-fraction-degree.json`: statement-only Mathlib leaf, `instFiniteDimensionalFractionRingOfFinite`, `Mathlib/RingTheory/Algebraic/Integral.lean:696–701`.
- `citations.json`: a verbatim statement quote for every step/node citation. `searches.jsonl` retains the actual search command records.

## Attachments

None. Searched the slopmaster2 project under `WeilConjectures/` for the exact blueprint id, almost-finite extensions, and finite residue degrees. The finite-field point-count statements, the p-adic valuation-ring result and the curve/Galois stalk statements do not state this item. The upstream master checkout was reference material only; no sorry declaration was treated as finished. No Lean was written or compiled.

## WANTED

WANTED: Swanson–Huneke, *Integral Closure of Ideals, Rings, and Modules*, local PDF, Proposition 4.8.5 (printed p. 85), Lemma 4.8.3 (printed p. 84), Corollary 2.1.13 (printed p. 27), for this item and `lem-trf-normalization-completed-branch-lift`. Read these places in the [author-hosted book](https://www.math.purdue.edu/~iswanso/book/SwansonHuneke.pdf). No document was downloaded or written to the repository. The explicit reduction is marked agent-written; its standard algebra inputs are existing Stacks nodes.

## Corrections and scope

The item was an unsplit statement, with earlier searches by its creator, and is mathematically correct. Its statement, hypotheses, source record, creation information, unit and historical blueprint ancestry were retained. The finite extension need not be separable and the base need not be normal, excellent or Nagata. Neither C nor its normalization is asserted module-finite over R.

I replaced no unit or chapter step. I read `sec-trace-formula` and `sk-i-curve-zero`. This is the already assigned generic algebra input below the Heinzer normalization-spectrum argument in the ancestor's finite-type alternative. The two off-unit non-leaf tools are declared in `split_report.tool_uses`: completion is Noetherian and complete, and complete local rings are Nagata. The proof uses only these statements, not their proofs or any unsupported geometric conclusion.

## Not duplicates

`lem-trf-normalization-completed-branch-lift` vs `lem-trf-almost-finite-residue-field-degree`: the new statement lifts a prescribed prime through a compatible homomorphism to the normalization of a completed branch. It neither asserts finite residue degree nor assumes a nontrivial finite fraction-field extension. Steps 1–5 and 7–8 carry the field-model construction and the finite-degree argument, so this is not the item renamed.

`lem-trf-normalization-completed-branch-lift` vs `lem-trf-curve-normalization-completion`: the existing result concerns reduced local algebraic curves over a field and tensor/completion comparison. It does not cover arbitrary Noetherian local domains or lift every prescribed normalization prime when completion has nilpotents. Likewise, the existing analytically-unramified N-1 node requires reduced completion; this lifting statement imposes no such condition.

`lem-trf-finite-domain-fraction-degree` vs `lem-weil-pbc-finite-subalgebra-fraction-field`: the existing statement constructs a finite model for a special polynomial/power-series base; it does not give fraction-field finiteness for an arbitrary supplied finite injective domain algebra. The new statement is exactly a Mathlib instance. The existing principal-prime quotient and dimension-one residue results impose extra Noetherian/principal/dimension hypotheses and do not subsume it.

The entire DAG was searched by the statements, declaration names and relevant source labels; the imported blueprint was searched with `blueprint_refs.py` for residue field, integral closure, complete local, completion, birational, finite domain and fraction field. None states either new fact. The algebraic localization theorem already exists as `lem-weil-pbc-integral-closure-commutes-localization`, so no new localization node was made. The completion structure and integral finite-adjoin results likewise reuse their existing nodes. Neither new source record has a Stacks tag shared with an existing node.

## Review by N8

I read the book's Proposition 4.8.5 and its normalization/complete-local reduction, Lemma 4.8.3 and Corollary 2.1.13. The new lifting node expresses the latter input on one minimal-prime component. Its homomorphism compatibility and the two contractions are all stated explicitly. In particular it is not a claim that normalization commutes with arbitrary completion. I checked its domain, local and Noetherian hypotheses, and made no analytically unramified assumption. The product normalization in Corollary 2.1.13 explains why a prime of the reduced-completion normalization selects one branch; the maximal ideal of that branch contracts to the completed maximal ideal. The finite minimal-prime set is supplied here by Noetherianity, so no assertion for infinitely many components is imported.

I opened the statement of every cited DAG node. I also read Stacks `algebra.tex` at labels `lemma-Noetherian-permanence` (00FN), `lemma-integral-transitive` (00GN), `lemma-integral-overring-surjective` (00GQ), `lemma-integral-closure-localize` (0307), `lemma-completion-Noetherian` (05GH), `lemma-Noetherian-complete-local-Nagata` (032W) and `definition-N` (032F). For the leaf I read pinned Mathlib `Algebraic/Integral.lean:690–702`, including the enabled fraction-field algebra instance and the full unnamed finite-dimensionality instance. I checked the local-completion comparisons in `AdicCompletion/LocalRing.lean:55–154`. The searches record actual results; generated instance names do not appear as source text, so the successful grep uses `FiniteDimensional.*FractionRing` and locates its conclusion at line 697. The other failed name grep is retained honestly.

1. Step 1 cites the finite integral-adjoin theorem for precisely a finite set of integral elements, and the finite-algebra Noetherianity theorem for precisely the resulting finite module over R. The polynomial scaling is displayed coefficient by coefficient, and the basis shows that this finite model has fraction field F. No primitive-element or separability theorem is used.
2. Step 2 uses the definition of integral closure for both inclusions; lying over applies to the injective integral inclusion C into D. The specified preimage N intersect C is Q, so the quotient injection is the right one. Transitivity applies to R, A, and the ring generated by an element integral over A, proving equality of the two normalization subrings. This uses the statement of the transitivity node, not a property hidden in its proof.
3. Step 3 checks that P annihilates A/a and explicitly reduces generators. R/P and A/a are domains, the induced map is injective, and their scalar action is torsion-free. Thus the new Mathlib leaf has every hypothesis it requires, including the one absent from a noninjective finite algebra map.
4. Step 4 uses the actual localization-at-prime definition for U's local structure and the Noetherian localization node for its finiteness condition. The integral-closure localization statement applies to A into F and the nonzero denominators outside a, and hence gives precisely E, not D localized at its own prime N. The prime and quotient formula and their identical fraction fields are written out. This distinction avoids an unjustified finite-module claim about a single localization of a finite algebra.
5. Step 5 verifies both hypotheses of the completion theorem: finitely generated m, and Noetherian U/m, a field. Its statement supplies both Noetherianity and completeness. The separate local-completion node supplies the maximal ideal and residue-field identification, making maximal-ideal completeness and the comparison canonical. No assertion of this step comes merely from a definition of completeness.
6. Step 6 applies the new lifting input only after U is a Noetherian local domain and E its birational normalization. The equations on inverse images give the quotient injection, and its A-algebra compatibility gives the commutative residue square needed at the end. The lift is the only non-elementary comparison isolated as a new unsplit node.
7. Step 7 applies the complete-local Nagata statement to H, where its hypotheses hold even if H is not reduced. It directly gives H/p N-2 for the selected prime. The Japanese definition then supplies finite normalization for the degree-one extension. Quotient generators and the stated contraction of M give the finite module T/M over the correct field H/n. The fraction-field leaf now supplies a finite field containing the lifted residue, without any need to identify T/M with a local-ring quotient by an unstated maximality theorem.
8. Step 8 checks denominator nonvanishing in each quotient injection, then the induced maps on fractions. Compatibility from Steps 4–6 makes them embeddings over k0. Multiplying finite spanning sets and bounding independent subsets proves the tower and subspace conclusions explicitly; these are elementary linear algebra, not uncited algebraic geometry.

Small cases checked: R a field, P=0, F=K, C=R, Q=0, an integrally closed base, inseparable finite F/K, and several or nonreduced completed branches. The basis construction works also for degree one; the quotient rings used for fraction fields are always nonzero domains because the ideals are prime; the selected branch is a domain although H may not be. There is no zero-ring case under the original domain hypothesis. No new node is a clause of the item, no proof step uses a downstream theorem (especially the parent's Noetherian-spectrum theorem), and the item/new nodes preserve acyclic ancestry. I checked B1–B9, C1–C8, D1–D5 and E1–E7 against these files. Every new unsplit node has only a statement, every used non-elementary fact is a cited node, and every proof step is shorter than 2000 characters.

## Unfinished work

None within the one-level split. The completion-branch lemma is deliberately unsplit for a later stage-1 item. It and the pre-existing lower nodes are not being claimed Lean-proved.

## Validation

The initial required server dry run exited successfully with `OK (not pushed)` at f65f495ae6. Before the final dry run I corrected the report's description of the existing curve lemma from a perfect field to an arbitrary field, and made the elementwise application of transitivity in Step 2 explicit. The item statement and dependency graph were unchanged by these final clarifications.
