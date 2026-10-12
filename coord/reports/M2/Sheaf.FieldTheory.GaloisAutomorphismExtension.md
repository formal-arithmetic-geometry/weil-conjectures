## What changed

Proved `exists_algEquiv_extending_separableClosure` in
`Sheaf.FieldTheory.GaloisAutomorphismExtension`, preserving its signature and public visibility.
Added proof-only imports `Mathlib.FieldTheory.IsAlgClosed.Classification` and
`Mathlib.Algebra.MvPolynomial.Equiv`. Choose a transcendence basis directly over Ks,
conjugate the coefficient automorphism on its polynomial algebra, and extend it using
`IsAlgClosure.equivOfEquiv`. The constant calculation proves the restriction formula and
that the resulting ring equivalence fixes K. Updated the existing node's proof and dependencies.
The old docstring describes a valid longer route; the DAG and this report describe the new proof.

## Proved and sorry left

Closed the only hole: `exists_algEquiv_extending_separableClosure`
(blueprint: lem-exc-galois-automorphism-extension). One hole closed, zero holes added;
no sorry remains. Compilation passed without warnings. The delivery dry run checks axioms.
There is no selection of data from an unproved existence theorem: the transcendence-basis
existence theorem and algebraic-closure equivalences are proved in Mathlib.

## No longer needed

The proof no longer uses `lem-weil-pbc-relative-algebraic-closure-algclosed`
(Mathlib.FieldTheory.AlgebraicClosure) or
`lem-weil-pbc-normal-subextension-automorphism-extends`
(Mathlib.FieldTheory.Normal.Basic). These nodes are removed from this item's proof_deps;
other users may still need them. Neither corresponding module was imported in the original
item, so no actual import was removed. The uniqueness-of-algebraic-closures node stays.
No unit statement or step is bypassed: sk-prop-h2 has no realization in this node.

## Where the brief, the DAG or earlier work was wrong

No statement error. The planned relative algebraic closure and normal-extension detour
is unnecessary: Mathlib handles algebraic closures of domains, so one can work directly
with the polynomial algebra over Ks. The proof even works without using IsSepClosure,
but the original hypothesis and signature are retained. The empty-basis algebraic case,
infinite bases, and positive characteristic are handled by the same Mathlib constructions.

## New nodes

`lem-exc-transcendence-basis-exists` records the existing Mathlib theorem
`exists_isTranscendenceBasis` (Stacks 030F). No new Lean module or hole.

`lem-exc-transcendence-basis-algebraic-closure` records the existing Mathlib theorem
`IsAlgClosed.isAlgClosure_of_transcendence_basis` (Stacks 030E (4), 09GS).
No new Lean module or hole. Both nodes have direct Mathlib matches; searches ran with
leanfinder, loogle and grep, and leansearch returned Internal Server Error (recorded unavailable).
Blueprint search found no matching node for "transcendence basis"; existing finitely generated
basis nodes do not cover the arbitrary extension needed here.

## Second reading by M2

1. Compared the delivered Lean module with the repository version. The theorem signature and
public visibility are byte for byte unchanged; only proof-only imports and the proof body changed.
Verdict: pass.

2. Compiled the module with `lcompile.py`; it compiles without errors or warnings. The proof has
no `sorry`, axioms, unsafe declarations, or hollow definitions. The construction uses Mathlib's
transcendence-basis and algebraic-closure theorems, and the resulting automorphism fixes K and
restricts to g on Ks by the displayed calculations. Verdict: pass.

3. Checked the two split-off node statements against their Mathlib declarations and edge cases
(including an empty transcendence basis). They are true, direct matches, and strictly simpler than
the target; no duplicate library theorem or extra Lean hole was introduced. Verdict: pass.

4. Checked pruning and the DAG route. The proof removes the relative-algebraic-closure and
normal-subextension dependencies, keeps the algebraic-closure uniqueness step, and retains the
unit route through the transcendence-basis and closure steps. The imports are minimal for the
proof. Verdict: pass.

5. Checked that the node proof, proof dependencies, proof origin, and new Mathlib-match nodes
agree with the Lean proof and that the report records all holes and changes. Verdict: pass.

Changed the report only by adding this second-reading record; no further Lean or DAG changes were
needed.
