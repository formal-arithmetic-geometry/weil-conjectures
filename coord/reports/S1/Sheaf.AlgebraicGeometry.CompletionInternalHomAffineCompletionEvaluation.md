## What changed

Repaired the landing refusal for the duplicate private theorem
`AlgebraicGeometry.finite_coherent_affine_sections` in
`CompletionInternalHomAffineComponentwise`. Removed that declaration entirely.
Both componentwise and parent proofs now use the existing, more general theorem
`AlgebraicGeometry.Scheme.Modules.finite_sections_of_finiteType` from
`QuasicoherentFiniteTypeAffine` directly, after installing its quasi-coherence and
finite-type instances with the existing coherence criterion. No replacement helper
or duplicate statement is added.

The parent now uses a plain import of the componentwise module and proof-only imports
of CoherentFiniteTypeLocallyNoetherian and `import all QuasicoherentFiniteTypeAffine`
(the reused theorem is private). Updated both DAG proof records to reflect those uses.
All public imports and existing theorem signatures stay unchanged. No existing library
module outside the assigned parent is adapted; the two supporting modules are new.

The completed delivery constructs quotient coordinates, completed evaluation by tensor
induction, and the compatible limit map, then proves the parent's two implications
by projection comparison. It reuses the existing affine Hom evaluation bijection.

## Proved and sorry left

Closed one original hole:
`AlgebraicGeometry.completion_internal_hom_affine_completion_evaluation`
(node `lem-weil-pbc-completion-internal-hom-affine-completion-evaluation`).

Two new supporting theorems are proved:
`AlgebraicGeometry.completion_affine_sections_coordinates`
(node `lem-weil-pbc-completion-affine-sections-coordinates`) and
`AlgebraicGeometry.completion_internal_hom_affine_componentwise`
(node `lem-weil-pbc-completion-internal-hom-affine-componentwise`).

No delivered theorem contains sorry. Zero holes are added; zero statements are split
off with sorry. The independent axiom audit shows only propext, Classical.choice and Quot.sound
for the parent and both supporting theorems; no sorryAx occurs in their proof closures.
The ledger tools determine closure progress for the overall targets.

## No longer needed

Removed the duplicate private finite-section declaration and the parent's `import all`
of Componentwise; only its public componentwise theorem is needed. No separate
coherent finite-section lemma or module is added. The existing finite-type affine
criterion supplies the required finiteness directly.

Compared with the original parent, CompletionInternalHomQuotient and
CoherentFormalModulesAffine are not needed. CoherentSheafHom and
Modules.IdealTimesQuasiCoherentAffineSections are used by the new supporting modules,
not directly by the parent. AsTensorProduct, coherent finite-type criteria, finite-type
affine sections, affine Noetherian rings, and affine Hom evaluation remain used.
The old tilde/Gamma adjunction remains below the existing affine Hom evaluation theorem.

The prior import-closure audit found these 20 project modules removed; the current
repair only makes direct imports explicit for modules already in that closure:

- `Sheaf.Algebra.Category.ModuleCat.AdicTowerCompletedFreeSurjection` — `lem-weil-pbc-adic-tower-completed-free-surjection`
- `Sheaf.Algebra.Category.ModuleCat.AdicTowerCompletedScalarLimit` — `lem-weil-pbc-adic-tower-completed-scalar-limit`
- `Sheaf.Algebra.Category.ModuleCat.AdicTowerFiniteLimit` — `lem-weil-pbc-adic-tower-finite-limit`
- `Sheaf.Algebra.Category.ModuleCat.AdicTowerFreeKernelCorrection` — `lem-weil-pbc-adic-tower-free-kernel-correction`
- `Sheaf.AlgebraicGeometry.CoherentFormalModuleAffineSectionsAdic` — `lem-weil-pbc-coherent-formal-module-affine-sections-adic`
- `Sheaf.AlgebraicGeometry.CoherentFormalModulesAffine` — `lem-weil-pbc-coherent-formal-modules-affine`
- `Sheaf.AlgebraicGeometry.CoherentFormalModulesAffineComplete` — `lem-weil-pbc-coherent-formal-modules-affine-complete`
- `Sheaf.AlgebraicGeometry.CoherentFormalModulesAffineLimit` — `lem-weil-pbc-coherent-formal-modules-affine-limit`
- `Sheaf.AlgebraicGeometry.CoherentFormalModulesAffineQuotient` — `lem-weil-pbc-coherent-formal-modules-affine-quotient`
- `Sheaf.AlgebraicGeometry.CoherentFormalModulesAffineQuotientCone` — `def-weil-pbc-coherent-formal-modules-affine-quotient-cone`, `lem-weil-pbc-coherent-formal-modules-affine-quotient-cone`
- `Sheaf.AlgebraicGeometry.CoherentFormalModulesAffineReconstruction` — `lem-weil-pbc-coherent-formal-modules-affine-reconstruction`
- `Sheaf.AlgebraicGeometry.CoherentFormalModulesAffineReconstructionAssembly` — `lem-weil-pbc-coherent-formal-modules-affine-reconstruction-assembly`
- `Sheaf.AlgebraicGeometry.CoherentFormalModulesAffineReconstructionObjectwise` — `lem-weil-pbc-coherent-formal-modules-affine-reconstruction-objectwise`
- `Sheaf.AlgebraicGeometry.CompletionInternalHomQuotient` — `lem-weil-pbc-completion-internal-hom-quotient`
- `Sheaf.AlgebraicGeometry.CompletionInternalHomQuotientAnnihilation` — `lem-weil-pbc-completion-internal-hom-quotient-annihilation`
- `Sheaf.AlgebraicGeometry.CompletionInternalHomQuotientIso` — `lem-weil-pbc-completion-internal-hom-quotient-isIso`
- `Sheaf.AlgebraicGeometry.FormalModuleQuotientAffineProjection` — `lem-weil-pbc-formal-module-quotient-affine-projection`
- `Sheaf.RingTheory.AdicCompletionNoetherian` — `lem-weil-pbc-adic-completion-noetherian`
- `Sheaf.RingTheory.FiniteModuleComplete` — `lem-weil-pbc-finite-module-complete-over-complete-noetherian`
- `Sheaf.RingTheory.PowerSeriesOntoCompletion` — `lem-weil-pbc-power-series-onto-completion`

## Where the brief, the DAG or earlier work was wrong

The landing check correctly found that the componentwise private finite-section helper
restated `Scheme.Modules.finite_affine_coherent_sections` from the tensor dictionary.
The earlier repair merely moved reuse from the parent to the duplicate helper, leaving
that duplication unresolved. This repair removes the helper itself and applies the
existing more general finite-type section theorem at all five use sites.

The tensor dictionary imports the parent. Importing it into the delivered componentwise
module would create the cycle Dictionary → Parent → Componentwise → Dictionary.
Therefore we reuse the lower-level existing theorem `finite_sections_of_finiteType`
instead of importing the downstream dictionary or restating its helper.

The old formal-category equivalence and quotient-factorization isomorphism route is
unnecessary below the unit level. The existing affine Hom evaluation theorem avoids
the earlier proposed duplicate affine evaluation node. No unit statement or realized
step changes.

## New nodes

`lem-weil-pbc-completion-affine-sections-coordinates`: proved; constructs quotient
coordinates, scalar and transition formulas, and the inverse-limit property.

`lem-weil-pbc-completion-internal-hom-affine-componentwise`: proved; constructs rho and
E and proves their component formula, with no compatible t, supplied epsilon, or final
iff. Uses existing affine Hom evaluation and finite-type affine sections directly.


## Second reading by S1

1. **Visible interface: PASS.** Compared the parent with the read-only repository using
   diff and a byte-for-byte signature comparison. Its existing theorem signature and all
   public imports are unchanged. Only proof bodies, a private proof helper, and proof-only
   imports changed. The other two modules are new; no definition or existing interface
   is changed, and no change record or forced adaptation is needed.
2. **Proof and axioms: PASS.** Independently compiled all three modules in dependency
   order (7.5, 22.9 and 11.2 seconds), with no errors or warnings. Scanned the delivered
   sources: no sorry, axioms, unsafe, opaque, implemented_by or extern. A scratch copy
   of the parent with #print axioms checks showed exactly propext, Classical.choice and
   Quot.sound for all three public theorems and the private extensionality helper.
   The quotient equivalences chosen in Coordinates are uniquely specified on the
   surjective ordinary quotient map. The parent's w(x) is uniquely specified by its
   projections, using hinjM. Equiv.ofBijective selects unique inverses. These choices
   do not extract arbitrary data from mere unproved existence.
3. **Supporting statements: PASS.** No statement is split off with sorry. Read the
   two new statements and their complete docstring proofs: Coordinates supplies the
   actual projections and their limit/scalar properties; Componentwise constructs
   rho and E and proves evaluation components, without the parent's compatible t or
   final iff. Neither restates the item. Checked zero ideal (constant positive-level
   system), unit ideal (zero system), zero modules and the empty affine: the argument
   uses no nonzero assumption and handles the omitted exponent-zero quotient explicitly.
   Independently searched with grep, loogle and leanfinder for inverse-limit quotient
   sections and extensionality of completed-module maps. Existing Mathlib map_ext lemmas
   concern Cauchy sequences, not agreement on ordinary generators; the short tensor
   induction is appropriate. Existing FormalCompletionAffineSections gives quotient
   isomorphisms and an evaluated sheaf-limit isomorphism, not the full coordinate/scalar
   interface; its lower-level quotient ingredients are already reused here. The affine
   Hom evaluation and finite-type section theorems are reused, not restated.
4. **Route and pruning: PASS.** Read the parent top-down, the tensor construction and
   both generator inductions, then the quotient-coordinate construction. The final iff
   uses joint injectivity and quotient surjectivity in the correct directions. All
   proof-only imports are plain imports (including import all for private reused facts).
   No shorter exact library result was found. The unit sk-thm-p1 realized record is
   unchanged; none of these three nodes is a realized unit statement or step. Every
   old proof dependency absent from the new parent's proof_deps is accounted for:
   completion-internal-hom-quotient and coherent-formal-modules-affine are discarded;
   coherent-sheaf-hom-coherent and ideal-times-quasi-coherent-affine-sections are used
   through the new supporting modules; affine-tilde-gamma-adjunction is used below the
   existing affine evaluation theorem. The 20 pruned modules are listed above.
5. **DAG: PASS.** Compared the existing node JSON with the repository: only proof,
   proof_deps and proof_origin differ. Checked each proof step against its Lean body
   and checked proof_deps against the union of uses. Both new nodes include source,
   statement dependencies, proof origin, searches, creation/blueprint/unit/chapter
   records and their actual Lean declarations. Their statements match the Lean.

Second reading changed only this report: recorded the independent checks and corrected
its conservative axiom-closure wording to the verified standard-axiom result. No proof
repair was needed; the removed duplicate finite-section helper remains absent.
