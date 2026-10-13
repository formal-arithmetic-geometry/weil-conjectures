## What changed

Closed the single hole in `Sheaf.AlgebraicGeometry.Morphisms.FiniteFlatTraceDiscriminantGluing` by constructing `IdealSheafData` explicitly from an intersection of inverse-image ideals and its named localization theorem. The target's signature and public imports are identical to the original. Added three private proof imports and four support modules.

`FiniteFlatAffineBasis` is fully proved: finite flat over the local ring at a prime is free; finite presentation descends its basis to a principal localization; explicit linear and scalar equivalences identify that localization with the scheme sections. `TraceDiscriminantAffineRestriction` is fully proved: Mathlib's localized discriminant formula and the unit determinant of basis change give equality on common principal refinements, and stalks detect equality on arbitrary affine charts. `TraceDiscriminantSectionIdeal` is an actual intersection construction with no chosen witnesses or postponed data.

The main module proves that the explicit intersection equals the discriminant principal ideal on a free chart, constructs the ideal sheaf using localization compatibility, and combines this with the proved local-basis theorem.

All five modules compile without warnings, individually in dependency order through lcompile.py. The delivery dry run also runs the declaration/axiom probes and static preflight. The unit's route is preserved; this is a refinement below the unit level.

## Proved and sorry left

Original hole closed: `AlgebraicGeometry.Scheme.exists_ideal_locally_eq_trace_discriminant_of_finite_flat` (lem-sbc-finite-flat-trace-discriminant-gluing).

New results completely proved: `AlgebraicGeometry.Scheme.exists_affine_basis_of_finite_flat` (lem-sbc-finite-flat-affine-basis), `AlgebraicGeometry.Scheme.trace_discriminant_span_map_affine_restriction` (lem-sbc-trace-discriminant-affine-restriction). The private basis-change, basic-open transport, common-refinement, and ideal-value helpers also have complete proofs.

One hole added and left: `AlgebraicGeometry.Scheme.traceDiscriminantSectionIdeal_map_basicOpen` (lem-sbc-trace-discriminant-section-localization). Its whole proof is `by sorry`, in its own module, with a source and complete finite-cover proof in words. It only asserts restriction compatibility of a concretely defined ideal family; it neither supplies a global ideal sheaf nor supplies local bases, so it is strictly part of the argument. One upper hole closed and one lower hole added is a decomposition, with net hole change zero, not a completed proof without assumptions.

## No longer needed

No original public import or previously planned DAG dependency was removed (the original proof_deps was empty). No existing module or node is claimed pruned.

Removed redundant imports from the new modules: `Mathlib.Algebra.Module.LocalizedModule.IsLocalization` in `FiniteFlatAffineBasis`, and `Mathlib.LinearAlgebra.Dimension.StrongRankCondition` in `TraceDiscriminantAffineRestriction`; their needed declarations are already provided transitively. The considered source-library ideal-sheaf gluing module `WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Functorial` is not imported: direct construction of `IdealSheafData` suffices.

## Where the brief, the DAG or earlier work was wrong

The original node supplied one long prose step, no proof dependencies, and no intermediate Lean declarations. The delivery makes its local-basis and trace/basis-change parts into proved Lean and isolates localization as the remaining step. No incorrect target statement was found.

Edge cases checked: the target is vacuous for empty Y; empty source has rank zero and discriminant one; a smaller affine open may be empty and have the zero section ring; bases on nonempty common refinements have the same cardinality by invariant basis number; discriminants may vanish identically. The affine-restriction proof explicitly handles subsingleton section rings. No domain, separability, fixed positive rank, or quasi-compactness of Y is assumed. The remaining localization proof uses a finite cover only of the affine chart U.

Sources read: Stacks 0BVH (construction before Lemma 49.3.1), 02K9 (finite flat over a locally Noetherian base is finite locally free), 00NX (finite projective modules). LeanSearch was unavailable (HTTP 500); this is recorded as unavailable, not as a negative search result. Loogle, LeanFinder, and Mathlib grep searches ran and are recorded in searches.jsonl. Searches in the existing DAG and source library found no duplicate of the new scheme-section statements.

## New nodes

`def-sbc-trace-discriminant-section-ideal`: explicit intersection construction, no sorry, in `TraceDiscriminantSectionIdeal`.

`lem-sbc-finite-flat-affine-basis`: finite bases on affine neighbourhoods, proved, in `FiniteFlatAffineBasis`.

`lem-sbc-trace-discriminant-affine-restriction`: compatibility of discriminant principal ideals on arbitrary affine restrictions, proved, in `TraceDiscriminantAffineRestriction`.

`lem-sbc-trace-discriminant-section-localization`: the only remaining hole, basic-open localization of the explicit intersection ideal, in `TraceDiscriminantSectionLocalization`.

The existing gluing node's proof, proof_deps, and proof_origin are updated to follow the construction and assembly. There are no statement changes, forced adaptations, or change records. The second-reading section is reserved for the independent second worker.

## Second reading by J3

1. The delivered main module was diffed against the repository version. Its target declaration has the identical signature; the proof only adds proof imports and constructs the explicit ideal sheaf. Verdict: pass.
2. All five sandbox modules compile with `lcompile.py --all`. The only remaining `sorry` is the named public theorem `traceDiscriminantSectionIdeal_map_basicOpen`; it has a matching split node and a source-backed proof docstring. No forbidden declarations or hollow definitions were found. Verdict: pass.
3. The new statements were checked against their definitions and edge cases (empty opens, rank zero, and vanishing discriminant). The affine-basis and affine-restriction lemmas are strictly smaller than the target, and the localization lemma is the necessary remaining compatibility assertion. Searches found no duplicate library theorem. Verdict: pass.
4. The proofs use the shortest available local constructions and Mathlib results found by the first worker; imports used only for proofs are private. The explicit intersection avoids an arbitrary witness. No additional pruning was identified, and the report's removed-import notes are complete. Verdict: pass.
5. The DAG proof steps, `proof_deps`, and `proof_origin` agree with the Lean proofs. The unit record is unchanged: its existing realized arrays are empty. This delivery refines the existing gluing node below the unit level and bypasses no existing realized node. Verdict: pass; the pre-existing empty unit realization is not repaired by this delivery.

Changed during second reading: no Lean declarations, statements, definitions, imports, or DAG nodes; appended this review and clarified that the pre-existing unit realization arrays are empty.
