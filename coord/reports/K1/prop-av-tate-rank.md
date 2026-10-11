1. Files written:

- `dag/nodes/sec-abelian-varieties/prop-av-tate-rank.json`: item split.
- `dag/nodes/sec-abelian-varieties/lem-av-tate-module-group-rank.json`: statement, attached closed Lean declaration.
- `dag/nodes/sec-abelian-varieties/lem-av-rational-tate-module-group-rank.json`: statement, attached closed Lean declaration.
- `citations.json`: verbatim citations for the item proof.

2. Attachments:

- `AddCommGroup.tateModule.nonempty_linearEquiv_of_natCard_eq` belongs to `lem-av-tate-module-group-rank`.
- `AddCommGroup.rationalTateModule.nonempty_linearEquiv_of_natCard_eq` belongs to `lem-av-rational-tate-module-group-rank`.

3. WANTED:

None.

4. What was wrong or incomplete:

The imported paragraph used the compatible-basis and inverse-limit argument without naming the group-theoretic theorem that carries it. I made that theorem explicit as the integral attached node and its rational base-change companion. The existing abelian-variety declarations are local proofs but their audit is `rests_on_sorry`, so they are not attachments. The target's old Mathlib search was insufficient; I replaced it with the required LeanFinder, Loogle, grep, and unavailable LeanSearch records.

## Review by K1

I read the target source in `WeilConjectures/AlgebraicGeometry/AbelianVariety/TateModule.lean` (the two declarations at lines 198--224) and the generic source in `WeilConjectures/GroupTheory/TateModule.lean` (the integral theorem at lines 228--295 and rational theorem at lines 337--341). The imported item statement agrees with the blueprint proposition. For the sole proof step, `lem-sc-isogeny-surjective` states surjectivity of multiplication on algebraically closed points, `lem-sc-ntorsion-etale` states the required `(Z/ell Z)^(2g)` torsion group, and `def-wf-abelian-tate-module` defines the two inverse-limit modules; the two new statements then give exactly the integral and rational conclusions. The kernel identification and cardinality calculation are the direct definitions and the displayed finite group isomorphism. Both new node statements were checked against their Lean declarations and tested at `r=0` and `r=1` as ordinary special cases. No duplicate blueprint node or DAG node was found. The corrected split makes every non-elementary rank assertion a named dependency and records the exact source lines.

5. What remains unfinished:

The new attached nodes remain unsplit because their source declarations are closed and sorry-free according to the committed audit map; the item itself is intentionally not attached because its declarations transitively rest on sorry-backed dependencies.

## Second reading by K1

- Item statement: checked against the blueprint proposition and the slopmaster2 Tate-module declarations; the hypotheses `A`, algebraically closed `k`, dimension `g`, `ell != char k`, and both integral/rational conclusions agree.
- Step 1: checked that `lem-sc-isogeny-surjective` supplies ell-divisibility, `lem-sc-ntorsion-etale` at `n = ell` supplies the exact cardinality, `def-wf-abelian-tate-module` identifies the group and abelian-variety Tate modules, and the two attached group-rank nodes supply the stated equivalences; no unsupported compatible-basis claim remains.
- `lem-av-tate-module-group-rank`: checked as a statement-only attached node against `AddCommGroup.tateModule.nonempty_linearEquiv_of_natCard_eq` (lines 228-295), including the prime, divisibility, torsion-cardinality, and integral-rank hypotheses; tested at `r = 0` and `r = 1`.
- `lem-av-rational-tate-module-group-rank`: checked as a statement-only attached node against `AddCommGroup.rationalTateModule.nonempty_linearEquiv_of_natCard_eq` (lines 337-341), including the same hypotheses and rational conclusion; tested at `r = 0` and `r = 1`.
- Existing-node and Mathlib searches: checked the repository for duplicate Tate-module rank statements and reran the recorded LeanFinder, Loogle, grep, and unavailable LeanSearch queries; no existing or Mathlib theorem matched.
- Changes: rewrote the proof step to derive divisibility and `Nat.card(M[ell]) = ell^(2g)` explicitly, removed the unjustified compatible-bases assertion, and expanded all citation entries to verbatim statement fragments long enough for delivery validation.
