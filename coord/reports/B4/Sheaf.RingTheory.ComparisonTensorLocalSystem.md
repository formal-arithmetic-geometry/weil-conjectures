## What changed

The original signature of `RingHom.exists_comparison_tensor_local_system` is unchanged.
Its proof now separates the finite-stage comparison diagrams from the limiting cocones,
constructs canonical P-linear maps to the limit, then derives the limiting Q-coordinate
identity by tensor-map composition and `colimit.w`.
Added proof-only imports of `Sheaf.RingTheory.ComparisonTensorDiagrams`,
`Sheaf.RingTheory.ComparisonTensorCanonicalMaps`, and
`Sheaf.RingTheory.ComparisonTensorCanonicalCocones`.

The new theorem `RingHom.exists_comparison_tensor_diagrams` states only the finite-stage
construction: induced P-actions, P-linear initial transitions, the diagrams and comparison,
canonical transitions, pushout squares, left compatibility and the finite-stage Q formula.
It assumes no colimit data, constructs no limiting cocones, and states no limiting
Q-coordinate identity.

`RingHom.exists_comparison_tensor_canonical_maps` constructs the actual canonical
P-linear maps to B from the initial transitions and μB by proving algebra-map compatibility.

The new theorem `RingHom.exists_comparison_tensor_canonical_cocones` explicitly constructs
ULift cocone points and legs for arbitrary diagrams with the stipulated tensor transitions.
It proves naturality using the canonical map identities, tensor induction and `colimit.w`.
It assumes no comparison transformation, initial comparison ψ, or pushout condition.
The existing DAG node and three new nodes record this route.

## Proved and sorry left

Closed the original hole in `RingHom.exists_comparison_tensor_local_system`
(node `lem-weil-pbc-comparison-tensor-local-system-j3`) by a complete Lean reduction.
Added one hole: `RingHom.exists_comparison_tensor_diagrams`
(node `lem-weil-pbc-comparison-tensor-diagrams-b4`).
This is a decomposition, not a net reduction in the number of holes.

`RingHom.exists_comparison_tensor_canonical_maps`
(node `lem-weil-pbc-comparison-tensor-canonical-maps-b4`) is proved from Mathlib,
with no sorry.

`RingHom.exists_comparison_tensor_canonical_cocones`
(node `lem-weil-pbc-comparison-tensor-canonical-cocones-b4`) is proved from Mathlib,
with explicit constructions and no sorry. The main module contains no remaining sorry.
No data definition is introduced or selected from an unproved existence theorem.

## No longer needed

No original import was removed. The old direct dependencies
`lem-weil-pbc-algebra-tensor-base-change-universal-property` and
`lem-weil-pbc-algebra-tensor-pushout-universal-property` are no longer direct
dependencies of the top proof. Both remain transitively needed by the finite-stage
construction; neither module nor node is pruned from the import closure.
The canonical-map and cocone proofs use elementary tensor-map composition,
tensor induction and colimit naturality, so their DAG proof dependencies are empty. The new diagram module uses `Ring.Basic` and
`Category.Preorder` instead of `Ring.Colimits`, since its statement needs no colimit.
The new cocone module omits the unused pushout-definitions import.
No existing module or unit route is pruned.

## Where the brief, the DAG or earlier work was wrong

No statement error was found. The initial module had no proof-dependency imports, since
both original proof dependencies are Mathlib leaves. Searches found component tensor and
ULift lemmas, not this complete indexed construction. LeanSearch returned an internal
server error, recorded as unavailable.

Edge cases: no nontriviality or injectivity of scalar maps is required. Trivial rings,
singleton index types and noninjective transitions are compatible with all three new statements.
The cocone construction uses neither directedness nor a universal property of D or E;
no colimit claim for the constructed cocones is introduced.

## New nodes

`lem-weil-pbc-comparison-tensor-diagrams-b4` is the finite-stage construction portion
of steps 1 and 3. Its theorem is in
`lean/Sheaf/RingTheory/ComparisonTensorDiagrams.lean`; this is the only new proof item.

`lem-weil-pbc-comparison-tensor-canonical-maps-b4` records the proved P-linearity
part of step 2 in `lean/Sheaf/RingTheory/ComparisonTensorCanonicalMaps.lean`.

`lem-weil-pbc-comparison-tensor-canonical-cocones-b4` records the proved canonical-cocone
portion of step 2, independently of the comparison transformation. Its theorem is in
`lean/Sheaf/RingTheory/ComparisonTensorCanonicalCocones.lean`.
No existing statement or definition changed; there are no change records or adaptations.

## Second reading by B4

1. Compared the only existing delivered module with the repository by `diff`
   and compared its complete theorem signature byte for byte: identical.
   Only proof-only imports and the proof body were added; no existing definition,
   visibility, statement, or target changed. There are no forced adaptations
   or change records. Verdict: pass.
2. Read all four modules and compiled them together with `lcompile.py --all`:
   no errors or warnings. The only remaining `sorry` is the complete proof of
   `RingHom.exists_comparison_tensor_diagrams`, as reported. There are no
   definitions containing holes and no forbidden declarations or attributes.
   The canonical maps are explicit ring maps equipped with commutation proofs;
   the cocone points and legs are explicit ULift constructions. The top proof
   eliminates the finite-stage existential inside a theorem, rather than
   defining data by choosing an undetermined unproved witness. Scratch
   `#print axioms` checks show only propext, Classical.choice and Quot.sound
   for the two proved helpers; the finite-stage theorem and the top theorem
   additionally use sorryAx from the one reported open statement. Verdict: pass.
3. Reviewed the finite-stage hole independently. Set the P-action on B_j to
   the composite P -> B_i -> B_j. The map Q -> C_j is the composite of the
   right inclusion, ψ, and the C_i -> C_j transition. By hψ, its P-restriction
   agrees with φ_j after the P-action on B_j. The tensor universal property
   therefore constructs ψ_j with the stated formula. Canonical tensor-map
   composition gives naturality and the Q identity. Tensor cancellation
   identifies D_k with B_k tensor_{B_j} D_j and C_k with B_k tensor_{B_j} C_j;
   hence each comparison square is the base-change pushout of ψ_j. This
   requires neither injective scalar maps nor nonzero rings. For a singleton
   index the transition squares have identity vertical maps; for trivial
   rings the same universal properties still apply. The statement removes
   all limiting constructions and is strictly a finite-stage part of the
   original argument. Its source, docstring proof, and node are present.
   Independent LeanFinder search for extending a ring hom under scalar
   extension with pushout squares, Loogle search for tensor-map composition,
   and grep for tensor cancellation and tensor pushouts found components,
   not a replacement theorem. Read the neighbouring comparison modules and
   `tensor_model_pushout_base_change`; the former depend on this item or
   additional global data, and the latter does not construct this comparison
   diagram. Verdict: pass; one genuine decomposition, zero net holes closed.
4. Read the proof from its assembly through the helpers. The helpers use
   canonical maps, tensor induction, map composition and colimit.w directly.
   All public Mathlib imports are needed by the signatures; all three new
   imports in the existing module are proof-only and used. Both old tensor
   universal-property dependencies are displaced from the top proof but
   remain in the finite-stage subproblem. No module is pruned. Read
   `dag/units/sk-thm-p1.json`: its statement and all realized steps remain;
   this item lies below those unit steps. Verdict: pass.
5. Compared the four DAG `lean.statement` strings with the actual theorem
   signatures: all exact. Checked new-node source, searches, provenance,
   chapter, unit, and Lean records. Corrected the top proof's last step and
   the canonical-map/cocone steps to record elementary tensor-map identities,
   rather than falsely citing the tensor pushout universal-property node.
   Recomputed each affected `proof_deps` as the union of its steps' uses and
   clarified `proof_origin`. Verdict: pass after metadata repair.

Second reading changed only DAG proof dependencies/provenance and this
report's direct-dependency and review account. Lean proofs and signatures
were retained. Source check: [Tag 02JO](https://stacks.math.columbia.edu/tag/02JO)
contains the scalar-extension comparison construction in the proof of (3);
[Tag 00DD](https://stacks.math.columbia.edu/tag/00DD) identifies the canonical
maps used in tensor cocones. No claim of universality for the new cocones is
made here.
