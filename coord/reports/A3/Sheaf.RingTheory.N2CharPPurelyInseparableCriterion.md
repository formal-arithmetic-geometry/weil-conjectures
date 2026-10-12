## What changed

Proved `isN2_of_finite_purelyInseparable_integralClosure` in
`Sheaf.RingTheory.N2CharPPurelyInseparableCriterion`, preserving its full signature.
Added proof-only imports of `Mathlib.FieldTheory.Normal.Closure`,
`Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure`, and
`Mathlib.RingTheory.DedekindDomain.IntegralClosure`. The existing proof-only import
`Sheaf.FieldTheory.NormalExtensionFixedField` is used.

Construct the finite normal closure M inside the algebraic closure of L, use the
existing fixed-field theorem to obtain the purely inseparable subfield S and the
separable extension M/S, and apply the hypothesis to S. Mathlib supplies normality
and the fraction-field property of A = integralClosure R S, Noetherianity of A,
and finiteness of integralClosure A M. Transitivity of finite modules and two
injective linear maps give the required finiteness in L. Explicit canonical scalar
structures on the nested integral closure prevent instance search from trying to
construct an S-action on a ring which generally has no such action.

Updated the existing node's proof, proof_deps, and proof_origin to record the
injection argument in place of equality of closures. This node is below the unit's
realized statements and steps; the unit route is unchanged.

## Proved and sorry left

Closed one existing hole:
`isN2_of_finite_purelyInseparable_integralClosure`
(node `lem-weil-pbc-n2-char-p-purely-inseparable-criterion`).
No sorry remains in the item. No holes were added, and nothing was split off.
The proof uses the existing stated theorem
`Normal.fixedField_purelyInseparable_and_galois`, whose proof still has sorry in
its separate module; that existing dependency was not modified or proved here.

Local single-file compilation passed without warnings in approximately eight seconds.

## No longer needed

Pruned the proof dependency `lem-weil-pbc-integral-transitive`: the inclusion of
integralClosure R M into integralClosure A M suffices over the Noetherian ring R.
The reverse inclusion, the equality of these closures, and their transitivity proof
are unnecessary. This dependency is a Mathlib leaf, so no separate Sheaf module is
pruned. No existing imports were removed; each retained or added proof import is
used, and the public imports supply the theorem's statement.

## Where the brief, the DAG or earlier work was wrong

The DAG's route is valid, but step 5 proves more than this argument needs.
An injective linear map into the second closure is sufficient. No statement,
definition, target, or dependency interface was changed.

Searches used the dispatcher's LeanFinder and Loogle services, plus local rg in
Mathlib and both library roots. They found the recorded separable closure theorem
`IsIntegralClosure.finite`, rather than a direct Japanese criterion. The Stacks
Tag 032N proof was read from the locally available copy of algebra.tex under
/home/ubuntu/work-bp/sheaf/literature/stacks-project/, since the project's literature
copy is not populated on this machine.

## Second reading by A3

1. **Visible interfaces — pass.** Diffed the only delivered Lean module against the
   repository and compared the existing theorem signature byte for byte: identical.
   Only proof imports, the proof explanation, and the proof body changed. No definitions,
   public imports, visibility, hypotheses, conclusions, or other modules changed; no
   change record is needed. No existing change record names this item or declaration.
2. **Proof and axioms — pass with the reported existing dependency still open.**
   Independently compiled the delivered file with lcompile.py without errors or warnings
   (8.7 seconds). A scratch copy with `#print axioms` compiled (10.3 seconds) and printed
   `[propext, sorryAx, Classical.choice, Quot.sound]` for the item and for
   `Normal.fixedField_purelyInseparable_and_galois`. The item contains no sorry or forbidden
   declaration/implementation mechanism. The remaining sorryAx is from the existing
   imported fixed-field theorem, not a new hole. This closes the item's one local hole;
   it does not establish an axiom-free target. M, S, A, and the nested closure are concrete
   Mathlib constructions. The open theorem supplies propositions about the already
   constructed fixed field, never arbitrary witness data. Reviewed the scalar towers,
   both linear injections and their injectivity proofs, and the Noetherian hypothesis
   needed by `Module.Finite.of_injective`.
3. **Split statements — pass, none.** No new theorem or node and no split-off hole is
   delivered. Checked the existing fixed-field dependency's statement and construction:
   the normality hypothesis is supplied by the finite normal closure, and its purely
   inseparable and separable clauses are exactly what the proof uses. Trivial extensions,
   a purely inseparable normal extension (fixed field M), and a separable normal extension
   (fixed field K) fit the argument. Independent searches used LeanFinder with a finite
   normal automorphism/fixed-field query and Loogle with
   `IsPurelyInseparable, IntermediateField.fixedField`, plus rg in Mathlib and both
   library roots. They found no direct criterion or replacement for the required
   purely inseparable fixed-field clause.
4. **Route and pruning — pass.** Read Stacks Tag 032N in the local algebra.tex and the
   relevant Mathlib normal-closure and separable integral-closure results. The proof uses
   those Mathlib results directly; the only Sheaf proof dependency is the already stated
   fixed-field theorem. Each added import supplies a used construction or result and
   is proof-only; public imports supply statement notions. Checked the old/new
   proof_deps difference: precisely `lem-weil-pbc-integral-transitive` is removed and
   is fully reported under No longer needed. Its reverse-inclusion argument is unnecessary
   because an injection into a finite module suffices. Read sk-thm-p1's realized statement
   and steps: this node lies below them; none is bypassed or altered. No module is pruned.
5. **DAG consistency — pass.** Diffed the delivered node: only proof step 5,
   proof_deps, and proof_origin change. Checked every retained dependency against its
   Lean declaration or recorded Mathlib match. Step 5 records `IsIntegral.tower_top`
   and the Noetherian injection argument implemented in Lean; proof_deps is the union
   of the steps' uses. There are no new nodes whose required fields need review.

Second reading changed only this report by adding the independent checks and explicit
axiom qualification. The Lean proof and node were retained unchanged.
