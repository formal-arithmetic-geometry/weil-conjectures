## What changed

Replaced the sole sorry in
`AlgebraicGeometry.exists_selfTor_conormal_wedge_chart_from_sections` by a complete Lean
reduction, preserving its signature and visibility. Added one prerequisite module,
`Sheaf.AlgebraicGeometry.Modules.ExteriorSheafQuasicoherent`, for quasi-coherence of exterior
powers on an affine scheme, without any local-freeness or finiteness assumptions.

The original module now proves three private helpers: `affine_iso_from_sections`,
`affine_over_iso_from_sections`, and `affine_model_chart_quasicoherent`. The first lifts the
linear equivalence and its inverse using the proved source-library AffineHom API and checks
the inverse equations by affine hom extensionality. The second transports scalar actions and
sections through the open/over-site equivalence and proves the terminal-component equation.
The third proves quasi-coherence of the affine model on the inverse-image chart by pullback
composition and the open-immersion counit, for every input affine module. It does not require
quasi-coherence of the open pushforward on the entire ambient scheme.

The conormal quasi-coherence prerequisite is proved directly from closed pushforward of the
structure module, quasi-coherence of kernels, and uniqueness of the tensor-pullback left
adjoint. The exterior restriction comparison then reduces the remaining geometric step to
exterior quasi-coherence on the affine chart. Proof-only imports were added for the affine
Hom API, closed pushforward, pullback quasi-coherence, and the new prerequisite. Public
imports were preserved. Updated the parent node's proof, proof_deps, and proof_origin.

The two delivered modules compile in import order within the single-file time limit. The
unit record `sk-thm-picard-duality` has no realized nodes at this step; its route was preserved.

## Proved and sorry left

Closed the original hole:
`AlgebraicGeometry.exists_selfTor_conormal_wedge_chart_from_sections`
(node `new-t2-self-tor-conormal-wedge-chart-from-sections`). No sorry remains in the item.
All three private helpers and the direct conormal quasi-coherence argument are fully proved.

Added one hole:
`AlgebraicGeometry.Scheme.Modules.isQuasicoherent_exteriorSheaf_of_isAffine`
(node `new-q1-exterior-sheaf-quasicoherent`). Its proof is exactly `by sorry`, with its source
and complete localization/sheafification proof in the docstring and DAG node. This is a
strict geometric prerequisite: it concerns an arbitrary quasi-coherent module on an affine
scheme and contains no immersion, conormal section equivalence, affine-model functor, or
terminal-component equation.

This delivery is a decomposition, closing one upper hole and adding one lower hole, rather
than a net one-hole proof. Existing dependencies, including exteriorSheaf_restrict_iso,
are used as stated and their modules have not been edited.

Edge cases of the new statement were checked mathematically: for degree zero its associated
module is A; for a zero module, positive exterior powers are zero; for an empty affine scheme,
A is the zero ring and all module sheaves are zero. The localization argument imposes no
characteristic, Noetherian, finite-generation, or regular-immersion assumption. The completed
chart transport handles all of these cases without special hypotheses.

## No longer needed

Removed the proof import `Sheaf.AlgebraicGeometry.AffineConormalSections` and the parent
proof dependency `lem-weil-pbc-affine-conormal-sections`. The section identification with I/I²,
its pullback-unit formula, and its remaining existence subproblem are not needed to extend
the explicit supplied section equivalence. In particular,
`Sheaf.AlgebraicGeometry.AffineConormalSectionsExistence` is not needed through this route.
These are pruning claims for this proof; other target paths may still reach those modules.

Retained `Sheaf.AlgebraicGeometry.Modules.ExteriorSheafRestrictIso`: it is actually used to
transfer the new affine exterior quasi-coherence result to the restricted exterior sheaf.
The new hole needs the affine tilde-Gamma dictionary and algebraic exterior localization,
not the conormal cotangent section calculation or any pure-wedge normalization of e.
No public import was removed, and no unit-level statement or proof step was bypassed.

## Where the brief, the DAG or earlier work was wrong

The parent proof plan bundled quasi-coherence and affine full faithfulness into one step.
The conormal section theorem was stronger than the quasi-coherence needed here: its I/I²
identification can be pruned when e is supplied explicitly. The actual missing declaration
is affine exterior quasi-coherence, which neither the conormal theorem nor the exterior
restriction isomorphism states. This has been separated as one source-backed prerequisite.

The closed pushforward and affine Hom facts used in the implemented proof are already proved
source-library declarations, not new axioms or new unfinished statements. The library-wide
quasi-compact/quasi-separated pushforward theorem is not imported: the specialized proved
closed-immersion theorem suffices for the ideal's closed subscheme.

LeanSearch was unavailable (Internal Server Error), recorded as unavailable without a
negative search verdict. LeanFinder, Loogle, and source searches found the affine Hom API and
exterior universal properties, but no exterior-sheaf quasi-coherence declaration.

## New nodes

`new-q1-exterior-sheaf-quasicoherent`, in
`dag/nodes/sec-picard-framework/new-q1-exterior-sheaf-quasicoherent.json`, states
`isQuasicoherent_exteriorSheaf_of_isAffine` in
`Sheaf.AlgebraicGeometry.Modules.ExteriorSheafQuasicoherent`. Its source is Stacks Section
26.7, Lemmas 26.7.1, 26.7.2(2), and 26.7.4 (Tag 01I6). The statement is strictly one
prerequisite of the chart construction. The node records the localization argument, the
three kinds of searches, the source, signature, and edge cases. No existing definition or
statement was changed, no module was forcibly adapted, and no change record is needed.

## Second reading by Q1

1. **Visible declarations and statements.** Compared the delivered chart module with the repository version. The theorem signature is byte-for-byte unchanged; only proof imports, proof text, and the recorded DAG route differ. The new exterior quasi-coherence declaration is a separate prerequisite with a strictly smaller statement.

2. **Compilation and proof integrity.** Compiled both delivered modules in import order with `lcompile.py`; both compile without errors or warnings. The chart theorem has no local `sorry`; the only remaining `sorry` is the named split theorem `AlgebraicGeometry.Scheme.Modules.isQuasicoherent_exteriorSheaf_of_isAffine`, whose docstring and node give its source and proof. No forbidden declarations or hollow definitions occur. The chart theorem's axioms contain only the permitted foundations plus `sorryAx` transitively through that split prerequisite.

3. **Truth and strength of split statement.** Checked the affine exterior-sheaf statement on degree zero, zero modules, and the zero-ring/empty affine scheme. It imposes no finiteness, local-freeness, characteristic, or regular-immersion hypotheses and is exactly the quasi-coherence fact used by the chart proof. The parent theorem's hypotheses and conclusion remain unchanged.

4. **Shortest route and pruning.** The proof uses the source-library affine Hom and closed-immersion facts, adjoint uniqueness for tensor pullback, and the exterior restriction isomorphism. The former affine conormal-section dependency is not used and is removed from imports and `proof_deps`; the report records this pruning. The new theorem is the sole unresolved geometric prerequisite, rather than a duplicate of the parent target.

5. **DAG and unit consistency.** The parent node's proof steps, dependencies, and origin match the Lean proof, and the new node records its statement, source, proof sketch, searches, and Lean declaration. The unit's route is preserved; no unit statement or realized step is altered.

Changed during second reading: appended this review only; no Lean declarations or DAG statements were changed.
