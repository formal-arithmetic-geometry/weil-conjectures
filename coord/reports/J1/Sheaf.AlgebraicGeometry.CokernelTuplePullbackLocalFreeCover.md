## What changed

Proved `AlgebraicGeometry.RingedSpace.cokernel_tuple_pullback_local_free_cover`
in its original module, with its exact signature and existing public import unchanged.
Added proof-only imports of `ModuleFiniteTypeImageExtension` (with `import all` to reuse
its proved private lifting and generator-restriction helpers), Mathlib abelian
refinements, and finite-type enumeration. Added three proved private helpers:
`exact_pullback`, `epi_pullback_generators`, and `tuple_over_eval`.
No interface changes, adaptations, new modules, or new nodes.

The proof takes finite local generators of F itself and maps them into the pullback.
It lifts the tuple on a smaller neighbourhood, proves the resulting coproduct map
is epi by exactness and cancellation, and enumerates the combined finite lists.
This is the construction of [Stacks Tag 01BY](https://stacks.math.columbia.edu/tag/01BY),
cokernel paragraph. The node now records this route. The existing theorem docstring
is retained; its image generators are supplied by the images of our generators of F.

The source module's private helpers are reused with their actual Lean signatures:
`finite_sections_lift`, `generators_over`, `generators_over_finite`,
`section_on_open`, and `sections_ext_top`. These are already proved, not unstated
conclusions inferred from the prose proof of another node. No use of the public
`finiteType_image_extension` theorem is needed. The current unit's realized
statement and steps are unchanged; this item is below them.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.RingedSpace.cokernel_tuple_pullback_local_free_cover`
(lem-weil-pbc-cokernel-tuple-pullback-local-free-cover).
No holes remain in the delivered module and no holes were added or split off.
This is a proof, not a decomposition. Local compilation succeeds without warnings.
The delivery dry run checks compilation and axioms against the shared build.

The empty tuple, zero generators, and arbitrary (possibly non-quasi-compact) opens
are included: finite_sections_lift intersects with the original open even for an
empty family, and the sum enumeration permits m = 0. An empty U cannot satisfy hx.
No coherence of G or global surjectivity on sections is assumed.

## No longer needed

Pruned the proof dependency `lem-weil-pbc-sheaf-finite-type-epi-image`
and its module `Sheaf.AlgebraicGeometry.FiniteTypeEpiImage` from this item's route.
It was not imported in the original module, so no import line was removed.
No separate theorem asserting finite type of the image is required.
Retained the finite-type definition and local-lifting dependencies, and recorded
restriction exactness through `lem-sc-derived-hom-mayer-vietoris`.
The new proof imports are all used. This does not assert that the pruned module
is unreachable from every other target route.

## Where the brief, the DAG or earlier work was wrong

No false statement or unusable interface was found. The planned image-finiteness
step was unnecessary: the images of a local generating family of F give exactly
the required zero-first-coordinate generators. The repository's literature copy
of modules.tex is absent on this machine; the cited Tag 01BY page was read directly.
Searches through LeanFinder, Loogle, the search wrapper's grep service, and local
Mathlib/library rg found the already proved lifting and generator helpers, but no
single theorem proving this pullback cover. Import direction was checked and allowed.

## Second reading by J1

1. **Interface preservation — pass.** Diffed the only delivered Lean module against
   the repository version and compared the existing theorem signature byte for byte:
   identical. The existing public import, visibility, universe and namespace remain
   unchanged. The added imports are proof-only, including `import all` for the proved
   private helpers. No definitions or statements used by other modules changed; no
   change record or forced adaptation is needed.
2. **Proof and axioms — pass.** Independently compiled the module with `lcompile.py`
   without errors or warnings (15.8 seconds). Read all three private helpers and the
   complete target proof. A scratch copy with `#print axioms` for the target and all
   three helpers compiled (19.0 seconds); each uses exactly `propext`,
   `Classical.choice`, and `Quot.sound`, with no `sorryAx`. There is no remaining
   `sorry`, forbidden declaration or hollow definition. The reused data helpers
   `section_on_open` and `generators_over` are actual constructions. The tuple lifts
   come from a proved theorem; the local generators come from the supplied finite-type
   hypothesis, not an unproved mere-existence theorem.
3. **Split statements and edge cases — pass.** No statements were split off and no
   holes were added. The private exactness lemma is valid without assuming either
   original arrow mono or epi: refinements lift precisely the kernel of the pullback
   projection. The second helper needs only an epi onto the first term and a lift
   whose first coordinate is an isomorphism. Finite local lifting retains the original
   open in its finite intersection, so the empty tuple works. Finite sums and their
   enumeration allow zero generators; no compactness or coherence of G is used.
   Independent LeanFinder, Loogle and grep searches with different queries found
   the refinement and exact-factorization APIs already used, and a comparable
   argument inside SnakeLemma, but no shorter ready-made local pullback cover.
4. **Route, imports and pruning — pass.** The proof uses F generators directly,
   then simultaneous local lifts, exactness preserved by restriction, epi
   cancellation, and finite enumeration. Rechecked the proved helpers in
   `ModuleFiniteTypeImageExtension`; it does not apply that module's public
   image-extension theorem. All added imports serve the proof. The only old
   dependency absent from the new route is
   `lem-weil-pbc-sheaf-finite-type-epi-image`, already listed under No longer needed.
   Read `dag/units/sk-thm-p1.json`: this auxiliary node is not a realized unit
   statement or step, and the realized route is preserved.
5. **DAG agreement — pass.** Parsed and compared the old and delivered node:
   only `proof`, `proof_deps`, and `proof_origin` differ. The four proof steps
   follow the Lean construction, and their uses have exactly the recorded union.
   The Mayer–Vietoris node records the restriction functor colimit-preservation
   declarations used here; its derived Hom theorem is not invoked. The finite-type
   definition and local-lifting nodes match the other reused APIs. No new nodes.

Second reading changed only this report, adding the independent review and axiom
results. No Lean proof or node repair was necessary. One original hole is closed,
zero holes are added, and zero statements are split off.
