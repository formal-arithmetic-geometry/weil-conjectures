## What changed

Kept the signature of AlgebraicGeometry.coherentFormalModule_kernel_affine_section_quotients
unchanged. Its proof constructs the finite completed modules from the affine section towers,
takes L to be the kernel of the induced completed-linear morphism, and compares its projected
range with the stabilized image using Artin--Rees. It then constructs the maps to S through
the inverse of the linear equivalence from each monic j component to its range. Range equality
proves surjectivity; injectivity proves the zero criterion; naturality proves compatibility.

Added two proved theorem modules, CoherentFormalModuleCompletedProjectionsLinear and
CoherentFormalModuleStabilizedKernelSectionRange, and their DAG nodes. The first strengthens
the existing private additive completed_projections construction in
CoherentFormalModuleAffineKernelImageComparison to retain the A-linear structure of p.
Its proof is the existing limit construction with that structure retained. The second uses
that module's proved private quotient_map_eq_iff_additive_image_eq and kernel_transition_range
helpers through a proof-only import all, and combines them with adic_kernel_image_bound.
There are no interface changes to existing declarations and no forced adaptations.

The source calculation was read at https://stacks.math.columbia.edu/tag/087X and
https://stacks.math.columbia.edu/tag/087W. The positive-power indexing is n+1 throughout.

## Proved and sorry left

Closed the sole original hole:
AlgebraicGeometry.coherentFormalModule_kernel_affine_section_quotients
(node lem-weil-pbc-formal-kernel-affine-section-quotients).

Also proved, without any local sorry:
AlgebraicGeometry.coherentFormalModule_completed_projections_linear
(node lem-weil-pbc-formal-completed-projections-linear), and
AlgebraicGeometry.coherentFormalModule_stabilized_kernel_section_range
(node lem-weil-pbc-stabilized-kernel-section-range).

No holes added or left in any delivered source. This is a proof from existing library
lemmas, not a decomposition into new unproved assertions. Existing dependency holes remain
the responsibility of their own modules; the delivery does not claim to close them.

## No longer needed

No original Lean import was removed: both public statement imports remain necessary.
The second reader removed the redundant public Mathlib.LinearAlgebra.Quotient.Basic
import from the new completed-projections module; its statement contains no quotient.
The direct DAG route no longer uses lem-weil-pbc-coherent-formal-modules-affine
(Sheaf.AlgebraicGeometry.CoherentFormalModulesAffine),
lem-weil-pbc-coherent-formal-modules-restriction-objects
(Sheaf.AlgebraicGeometry.CoherentFormalModulesRestrictionObjects), or
lem-weil-pbc-module-restriction-open-immersion-colimits
(the Spec transport/restriction route). It uses the already established affine section
adic tower instead, without constructing a restriction equivalence.

The former direct dependencies on adic-completion-noetherian, affine-tilde-gamma-adjunction,
ideal-times-quasi-coherent-affine-sections, quasi-coherent-module-kernel,
quasi-coherent-module-cokernel-image, and new-adic-kernel-image-bound are not claimed
pruned globally: they remain directly or transitively used by the new proof's dependencies.
No unit statement or realized unit step is bypassed; the item is below the unit level.

## Where the brief, the DAG or earlier work was wrong

The old plan's affine equivalence/restriction route is longer than needed. The completed
projection construction and the affine kernel transition range computation are already
proved in CoherentFormalModuleAffineKernelImageComparison, but the public comparison
theorem forgets the actual projections and its private construction only exports additive
p maps. Retaining the A-linear p maps is sufficient for this delivery. The remaining
quotient-map construction and compatibility are genuine Lean proofs in the assigned file.

Checked the empty affine open, zero modules, and zero and unit ideals: no nontriviality,
properness of the ideal, or nonemptiness hypotheses were introduced. The projection action
is determined by the limit universal property and the residue equation. The morphism f
is explicitly constructed from the limit map, and L is explicitly its kernel. Each q is
constructed by the inverse range equivalence of an injective map; no arbitrary witness
of an unproved existence theorem supplies data to a definition.

Searches: LeanSearch was unavailable (Internal Server Error). LeanFinder returned eight affine-scheme limit/ideal-sheaf hits, none the required
formal module interface. Loogle found LinearEquiv.ofInjective, used in the proof. msearch
grep returned no stabilization hits; local rg located the existing private helper proofs.

## New nodes

lem-weil-pbc-formal-completed-projections-linear records the proved completed-module
construction with A-linear source projections, their kernels, and naturality. It uses the
existing affine-section adic tower, completed scalar limit, and finite limit statements.

lem-weil-pbc-stabilized-kernel-section-range records the proved affine range identification
for already given projection data. It applies the Artin--Rees bound at the maximum of the
supplied stabilization index and its own bound, then uses affine image exactness and hc.
It constructs neither completed modules nor quotient maps into S.

No change records are necessary: every existing signature and visibility is unchanged.

## Second reading by P2

1. Compared the assigned module with the repository using diff and an exact signature
comparison: the sole existing theorem signature is byte-for-byte identical. The only
changes outside its proof are proof-only imports and a local elaboration option.
The existing node changes only proof, proof_deps and proof_origin. There are no public
definition changes, forced adaptations, or change records. Verdict: pass.

2. Read all three proofs and the upstream private helpers used by the range theorem.
There is no sorry, axiom, unsafe, opaque, implemented_by or extern in any delivered
source, and no new global definition. The completed modules come from the canonical
limit comparison with its residue equation (which determines the completed action),
not from arbitrary existence data. The map f is explicitly lifted from the natural
transformation; L is its kernel; q is the inverse range equivalence of an injective
linear map. All three modules compile cleanly through deliver3.py using lcompile.py. Its
per-declaration axiom probes and the full stage-3 preflight passed. Verdict: pass.

3. No unproved statement is split off. The two new proved statements are strictly
parts of the argument: construction of linear projections, then identification of
an already supplied kernel range. Read Stacks Tags [087W](https://stacks.math.columbia.edu/tag/087W)
and [087X](https://stacks.math.columbia.edu/tag/087X), specifically their limit reduction
and stabilized-image calculations. The Lean convention uses n+1 throughout. In the
range proof, max(m+c,m+d) separately meets stabilization and Artin--Rees bounds; only
N needs to be finite. The proof also works for c=0, m=0, zero modules, the empty affine,
and zero/unit ideals: it uses no cancellation by a nonunit or nontriviality assumption.
Independent Loogle query `LinearMap.range, LinearEquiv` found ofInjective and related
range equivalences but no whole formal-module statement. Independent msearch grep
`adicTower|completedScalarLimit|restrictScalars_map_smul_eq` found the scalar-restriction
lemma; local rg found only the existing private additive projections and range helpers.
Retaining the linear p data is necessary to construct A-linear q. Verdict: pass.

4. Read the original dependency list and dag/units/sk-thm-p1.json realized record.
The item and new helpers realize no designated unit statement or step, so this shorter
section-tower route is below the unit level. All nine former direct dependencies are
accounted for in No longer needed: three affine/restriction nodes are omitted there,
and the other six remain used directly or transitively by helper imports. No global
module pruning is claimed. Removed the unnecessary public quotient import from the
new projection module; other proof dependencies are private imports, with import all
needed to reuse the already proved private range helpers. Verdict: pass.

5. Matched each Lean statement to its node and read the proof/proof_deps/proof_origin
records. The projection node cites section adic towers, completed scalar limits and
finite limits; the range node cites completion Noetherianity, Artin--Rees, coherence,
kernel and image exactness, plus the comparison module's proved private helpers.
The item cites both new helpers and explicitly describes the range-inverse construction
and naturality cancellation. Replaced the range node's non-self-contained phrase
"as above" with its actual objects and hypotheses. Verdict: pass.

Second-reading changes: removed one redundant public import; made the new range node
statement self-contained; added this detailed review. No proof or existing signature
required repair.

Validation: deliver3.py --no-push printed OK; review class CODEX because the
delivery adds two fully proved helper modules and their nodes.

Explicit #print axioms in a scratch copy confirmed that all three delivered theorems
depend only on propext, Classical.choice and Quot.sound, with no sorryAx. The scratch
copy compiled cleanly and was removed before delivery.
