## What changed

Proved `AlgebraicGeometry.affineSpectrum_composition_unit_square` from the selected derived-pullback associativity and unit laws. Private helpers perform the transport and cancellation calculation with abstract functors. A private concrete theorem specializes it while the coherent comparisons are still parameters; the main proof then supplies the selected comparisons, their laws, and the defining formulas of both affine comparisons. All imports and the existing theorem signature are unchanged. Local transparency settings keep derived-pullback constructions from unfolding during the abstract calculation.

## Proved and sorry left

Closed the one original hole: `AlgebraicGeometry.affineSpectrum_composition_unit_square` (node `lem-pc-affine-spectrum-composition-unit-square`). Added zero holes. No `sorry` remains in the delivered module. This is a proof relative to the existing imported comparison laws, not a decomposition into new open statements.

## No longer needed

None of the original proof dependencies or imports is pruned. The first worker's undelivered `affineSpectrum_coherence_core` and its node `lem-pc-affine-spectrum-coherence-core` were removed during second reading.

## Where the brief, the DAG or earlier work was wrong

The first worker's core theorem quantified over arbitrary c, i, A, B without any coherence laws or equations identifying A and B with the canonical comparisons. It is false: negating A in a nonzero rational linear category changes only the left-hand side. Its docstring omitted a proof and used the parent's blueprint tag, and its node recorded a different signature and the wrong creator/item metadata. The target application merely moved the entire hole into this false core. The second reader replaced it with a proved calculation that explicitly assumes the selected associativity and unit laws, then supplies those laws from `exists_derivedPullbackComposition`.

The earlier concrete helper attempt exceeded the compile limit by unfolding large derived constructions. Abstracting the functors and coherent comparison data, then specializing through a concrete private theorem before passing the selection proofs, makes the same argument compile without increasing the heartbeat limit. Local reducibility settings protect the derived and tensor-pullback data while exposing the category-instance aliases needed for their types.

## Second reading by C3

1. Compared the delivered module with the repository version and checked the existing theorem signature byte for byte. It is identical; no existing definition or statement was changed, no other module is adapted, and no semantic interface change occurs. `coord/changes/AffineSpectrumCompositionUnitSquareProofContext.md` records the local proof-context commands conservatively flagged by preflight, with all downstream users and no required adaptations.
2. Reviewed the actual transport/cancellation proof. All helpers are proved, all data definitions are explicit constructions, and there is no `sorry`, axiom, unsafe, opaque, implemented_by, or extern in the delivered code. Compilation and axiom verification are recorded below.
3. Rejected and removed the false undelivered split-off statement and its inconsistent node. The replacement private helpers have explicit coherence hypotheses and proofs; no new open statement is delivered. Checked the identity-map and zero-object cases: the same unit and inverse-cancellation laws apply, with no nonzero or nonidentity assumption. Independent LeanFinder, Loogle, grep searches and source inspection found the standard component cancellation and pseudofunctor coherence tools, but no pre-existing theorem for these selected derived-pullback comparisons.
4. The proof follows the parent's three associativity calculations and two unit laws, below the unit level. The original three proof dependencies are all used. The unit `sk-thm-picard-semicon` has empty realized statement/step lists; no recorded unit route is bypassed or changed. The sole original import supplies definitions that the public statement uses and remains public.
5. Updated the original node's proof steps to match the written calculation; proof_deps and proof_origin remain accurate. The false new node is absent. No new public statements or open nodes are added.

Second reading changed: removed the false core and its node, proved the actual target through fully proved private coherence helpers, corrected the theorem's proof explanation, and synchronized the original node's proof, and documented the proof context in `coord/changes/AffineSpectrumCompositionUnitSquareProofContext.md`.

Validation: a scratch copy of the final module compiled without warnings in 26.6 seconds. `#print axioms` on `tc_assoc`, `square`, `square_with_data`, `concrete_square`, and `affineSpectrum_composition_unit_square` returned only `propext`, `Classical.choice`, and `Quot.sound`; the target has no `sorryAx` dependency. A byte comparison confirmed the original theorem signature is identical, and the delivered source has no forbidden constructs or overlong lines.
