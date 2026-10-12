## What changed

Proved `RingHom.completion_map_bijective` in
`lean/Sheaf/RingTheory/CompletionMapBijective.lean`, with its signature byte for byte unchanged.
The final proof identifies the extended maximal ideal with the target maximal ideal.
Flat locality gives faithful flatness and injectivity. Residue-field surjectivity gives
surjectivity modulo that ideal; Mathlib `surjective_of_mk_map_comp_surjective` then gives
surjectivity by completeness of the source and separation of the target.

The second reading replaced the first worker's finite-module/Nakayama route by this shorter
Mathlib route, removing its two private projection helpers, the proof-only imports of
`Sheaf.RingTheory.FiniteAfterCompletion` and `Mathlib.RingTheory.Nakayama`, and the previously
open finiteness dependency. The original public imports remain unchanged; the two new
Mathlib imports are proof-only: `Mathlib.RingTheory.AdicCompletion.LocalRing` and
`Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra`. The module docstring, inline comments,
and existing node's `proof`, `proof_deps`, and `proof_origin` describe the final proof.

## Proved and sorry left

Closed the only original hole: `RingHom.completion_map_bijective`
(node `lem-weil-pbc-flat-local-completion-iso-bijective`). Holes added: none.
There are no `sorry`s, split-off statements, new declarations, new modules, or new nodes.
Unlike the first worker's proof, the final theorem has no dependency on
`AdicCompletion.finite_after_completion` or any other open statement.
The scratch-copy `#print axioms RingHom.completion_map_bijective` and delivery probe
check the axiom closure; local compilation and delivery compilation check the proof.

## No longer needed

Removed the original proof-only import `Sheaf.RingTheory.FiniteAfterCompletion`.
Also removed the first worker's newly added `Mathlib.RingTheory.Nakayama` import.
The old proof dependencies now unused are:
`lem-weil-pbc-finite-after-completion` (module `Sheaf.RingTheory.FiniteAfterCompletion`)
and `lem-weil-pbc-finite-flat-local-free` (Mathlib `RingTheory.LocalRing.Module`).
The first worker's proposed `lem-weil-pbc-nakayama-local-generators` dependency is also
unused in the final proof. All other old dependencies remain used.
Whether these nodes and modules remain reachable elsewhere is for the maintainer's queue.

## Where the brief, the DAG or earlier work was wrong

No statement error was found. Both the original rank-one route and the first worker's
finite-module/Nakayama route are valid but unnecessary: Mathlib already provides the
successive-approximation theorem for a precomplete source and Hausdorff target.
The original theorem docstring is retained verbatim as an alternative valid mathematical
proof, although it describes a longer route than the implemented proof.
The final proof uses only the surjectivity part of residue-field bijectivity; this does
not change the statement. No continuity assumption or finite-module hypothesis was added.

## Second reading by B2

1. Compared the delivered module against the repository version with `diff` and checked
   the theorem signature byte for byte. Verdict: unchanged; no definitions or public
   imports changed, no change record needed. The only interface declaration is the
   existing theorem; the two first-worker private helpers were removed.
2. Read the proof from its conclusion through each dependency and compiled it locally.
   Checked for `sorry`, `axiom`, `unsafe`, `opaque`, `implemented_by`, `extern`, and
   unchecked-kernel options: none. The scratch-copy axiom print contains only
   `propext`, `Classical.choice`, and `Quot.sound`. Verdict: a complete proof, with
   no inherited `sorryAx`; server compilation and preflight are the final checks.
3. No statements were split off or added. Checked the residue lifting, the ideal
   equality, and instance transport; field/identity cases reduce to the identity
   map and the zero maximal ideal, for which completeness lifting still applies.
   Trivial rings cannot satisfy `IsLocalRing`. Verdict: no missing edge hypothesis.
4. Re-searched Mathlib and the library using Loogle `AdicCompletion, Function.Bijective`
   and source searches for surjectivity and completeness. This exposed
   `surjective_of_mk_map_comp_surjective`, which removes all staged finiteness holes.
   Checked `dag/units/sk-thm-p1.json` and its realized statements and steps: this node
   lies below those nodes; no realized unit step is bypassed or changed. Imports
   supply the statement, local-completion instances/kernel calculation, and faithful
   flatness respectively. Verdict: shorter route, complete pruning list above.
5. Compared the old and final DAG proof dependencies and read the Mathlib matches
   of the retained nodes. Updated `proof`, `proof_deps`, and `proof_origin` to the
   actual ideal calculation, residue lifting, complete-source surjectivity, and
   faithful-flat injectivity. No new node is needed for a direct application of
   an existing Mathlib theorem. Verdict: DAG and Lean agree.

Changes in this reading: replaced finite-module/Nakayama by completeness lifting;
removed the two private helpers and two proof-only imports; removed the finiteness
and Nakayama dependencies; updated the DAG, module explanation, and report.
