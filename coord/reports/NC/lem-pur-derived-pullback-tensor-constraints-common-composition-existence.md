# Stage-1 repair report: lem-pur-derived-pullback-tensor-constraints-common-composition-existence

Files written:

- `dag/nodes/sec-smooth-purity/lem-pur-derived-pullback-tensor-constraints-common-composition-existence.json` — repaired item statement and three-step colimit-class proof.
- `dag/nodes/sec-smooth-purity/lem-pur-common-stage-pullback-composition-theta-compatibility.json` — new statement-only compatibility node; Mathlib verdict: no match.
- `citations.json` — verbatim excerpts for every cited node and step.
- `report.md` — this repair report.

Attachments: none. `WeilConjectures.pullbackTensorCommonComposition_exists` still has `sorry` in the live Lean source.

WANTED: none.

## Not duplicates

- `lem-pur-common-stage-pullback-composition-theta-compatibility` vs `lem-weil-common-stage-pullback-comparison-data`: the existing node gives a coherent family for the scalar comparison of one pullback functor; the new node states the mixed square relating three scalar comparisons to the pullback-composition isomorphism.
- `lem-pur-common-stage-pullback-composition-theta-compatibility` vs `lem-pur-integral-operations-scalar-extension`: the existing node gives naturality, tower compatibility, and the identity extension case; the new node adds compatibility with the compositor for two composable pullbacks.
- `lem-pur-common-stage-pullback-composition-theta-compatibility` vs `lem-pur-pullback-tensor-composition-coherence`: the existing node concerns tensor/pullback composition predicates at coefficient levels; the new node concerns scalar-extension theta maps and the rational pullback compositor before tensor constraints.
- `lem-pur-common-stage-pullback-composition-theta-compatibility` vs `lem-pur-derived-pullback-tensor-constraints-common-composition-existence`: the new node is the prerequisite theta/compositor square; the item constructs the common-stage isomorphism as its colimit class.

The prior delivery was returned for five related issues. The repaired proof no longer cites `def-pur-completed-pullback-tensor-comparison` for the pullback composition or common-stage pullback objects, and it drops the decorative derived-limit/reconstruction and finite-reduction closure steps. The missing coherence is now an explicit statement-only node. The item now uses the exact Lean coefficient context `[Field Ω] [Algebra ℚ_ℓ Ω] [IsAlgClosure ℚ_ℓ Ω]`, and its proof origin is agent-written from the common-stage paragraph because Stacks 07A4 is the tensor/pullback lemma rather than a source for the full normalized representative construction.

## Review by NC

I reread the returned item, the current Lean declaration at `DerivedPullbackTensorConstraints.lean:230`, the definition of `commonStagePullbackObject` and `commonStagePullbackComparison` at `DerivedPullbackTensorHom.lean:373`, and the common-stage morphism construction immediately following it. I verified that the item has the same three residue-field invertibility hypotheses and the same `IsAlgClosure` coefficient assumptions as the Lean theorem. The statement now refers to the prescribed rational composition comparison and the heterogeneous `ofHom` representative without attributing those objects to the completed tensor-comparison definition.

I added `lem-pur-common-stage-pullback-composition-theta-compatibility`. Its statement introduces finite fields `E ≤ L`, the three scalar-extension comparisons `θ^f`, `θ^h`, and `θ^(h∘f)`, and the rational pullback-composition maps `c_{h,f,E}` and `c_{h,f,L}`. It asserts exactly the square identified by the maintainer:
`c_L(M⊗L) ∘ θ^(h∘f) = h_L^*(θ^f) ∘ θ^h ∘ (c_E(M)⊗L)`.
The node is statement-only because this is the nontrivial missing coherence fact; its statement dependencies are the common-stage operation definition, scalar-extension comparisons, and finite pullback composition.

Step 1 of the item uses only `def-weil-derived-pullback-tensor-hom` for the common-stage objects and `lem-pod-integral-pullback-composition` for the rational composition isomorphism. Conjugating that finite-field isomorphism by the prescribed comparison maps gives an isomorphism at the original stage.

Step 2 cites the new compatibility node and uses its full compositor square. This explicitly proves independence from the chosen larger field and supplies the heterogeneous representative required for every `L`; no inference from the scalar tower identity alone is made.

Step 3 uses the common-stage definition's statement that a representative over a finite common field is sent to its colimit class and that composition is computed after a common enlargement with middle comparisons cancelling. Thus the transported rational isomorphism and its inverse define the required common-stage `e`.

I removed the prior references to completed tensor/pullback comparisons, normalized reconstruction, coherent reduction, legacy derived-completeness comparison, and triangulated closure. Those facts either addressed the wrong operation or were irrelevant because the common-stage Hom is a finite-field colimit, not a derived inverse limit. The new node and the repaired item each have fresh LeanFinder, Loogle, grep, and LeanSearch records; none found the project-specific theta/compositor statement. Edge cases `f = id`, `h = id`, `L = E`, and `M = 0` reduce the square to the corresponding identity/tower equations.

What could not be finished: nothing at stage 1; the Lean theorem itself remains an admitted proving target.
