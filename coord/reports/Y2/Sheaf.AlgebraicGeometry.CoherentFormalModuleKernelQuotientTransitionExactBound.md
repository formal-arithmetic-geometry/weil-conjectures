## What changed

Proved coherentFormalModule_kernel_quotient_transition_exact_bound from a compatible
stalk quotient model. Its signature and public imports are unchanged. Added
CoherentFormalModuleKernelStalkPresentation (one remaining theorem hole) and
CoherentFormalModuleKernelShiftedStalkModel (fully proved from that presentation).
The proof computes the stalk of each defining quotient using the shared ideal-product
and stalk-exactness APIs, derives its kernel using comap_smul_top_of_surjective, and
constructs the quotient isomorphisms by the first isomorphism theorem. It verifies
transition compatibility by lifting along a surjective composite and using the
cokernel projection equation. The main proof calculates the kernel of a power-quotient
reduction using representatives and map_smul'', transports ideal-power membership
across the linear equivalence, and applies stalkwise exactness detection.

Private proved helpers establish that a quotient by an ideal product is annihilated
by that ideal. These reproduce the generic multiplication argument of the private
helpers in CoherentFormalModule; they assert no new public definitions or interfaces.
The zero composite is proved for every shift, independently of the remaining
Artin--Rees bound. All modules compile locally with no warnings.

## Proved and sorry left

Closed the original hole:
AlgebraicGeometry.coherentFormalModule_kernel_quotient_transition_exact_bound
(lem-weil-pbc-formal-kernel-quotient-transition-exact-bound).

Added and proved:
AlgebraicGeometry.coherentFormalModule_kernel_shifted_stalk_model
(lem-weil-pbc-formal-kernel-shifted-stalk-model).

Added one remaining hole:
AlgebraicGeometry.coherentFormalModule_kernel_stalk_presentation
(lem-weil-pbc-formal-kernel-stalk-presentation).
This is the only sorry in the three delivered modules. It describes the unshifted
system S by compatible surjections with an upper bound on their kernels; it does
not state shifted-quotient exactness or any cokernel comparison. The two subsequent
proofs perform that quotient calculation and the exactness argument. This is a
decomposition: one old hole closed, one new hole added, net zero. No data definition
uses an arbitrary witness of an unproved existence assertion: all existential
witnesses are eliminated only inside theorem proofs.

## No longer needed

Removed direct proof imports:
- Sheaf.AlgebraicGeometry.CoherentFormalModulesAffine
- Sheaf.RingTheory.AdicCompletionNoetherian
- Mathlib.RingTheory.Filtration
- Sheaf.AlgebraicGeometry.CoherentKernelCokernelLocallyNoetherian
- Sheaf.AlgebraicGeometry.Modules.IdealTimesQuasiCoherentAffineSections

All except CoherentKernelCokernelLocallyNoetherian are retained as proof ingredients
of the new stalk-presentation item; they have not been globally pruned. The exactness
argument does not need coherent kernel/cokernel closure
(lem-weil-pbc-coherent-kernel-cokernel-locnoeth), and the presentation uses finite
modules over the completed ring instead. This dependency is pruned from this route.
No claim is made that its module leaves every other target import path. The unit's
realized statement and steps are untouched; neither this node nor the removed
dependency is a realized step of sk-thm-p1.

## Where the brief, the DAG or earlier work was wrong

The original proof-dependency signatures supply no compatible presentation of the
stabilized images as quotients of the actual completed kernel. An affine equivalence,
Artin--Rees, and equality of two finite-level images do not by themselves supply
that missing interface in a few Lean steps. The delivery isolates precisely the
unshifted presentation and proves the subsequent arguments.

The original node's blueprint.from.node is null. Following the existing construction
and coherent-formal-kernel ancestry reaches thm-weil-pbc-finite-etale-lifting; the
new nodes record that ancestor explicitly. The existing node's blueprint field was
not edited because stage 3 owns only its proof fields and Lean record.

The cited local Stacks TeX file is absent on this machine. Read the full proof of
087X at https://stacks.math.columbia.edu/tag/087X instead. LeanSearch returned HTTP
500 and is recorded as unavailable, not as a negative search. LeanFinder and grep
found quotient and completion tools, but no stabilized stalk presentation theorem.

Checked edge cases before stating the new presentation: I=0 gives constant
presentations with zero kernels; I=O_X gives zero S levels and the bound is automatic;
zero source/target modules give zero kernel or the original quotient presentation;
empty X admits b=0. No finiteness over the stalk ring is asserted: the localized
completed kernel need not be finite as a module over the uncompleted local ring.

## New nodes

lem-weil-pbc-formal-kernel-stalk-presentation: compatible surjections onto the
unshifted stabilized-image stalks, with uniform containment of the shifted kernels
in powers of the stalk ideal. Source: Stacks 087X, affine calculation of claims
(a)--(b), using 087W, completed-ring Noetherianity, and Artin--Rees. The statement
retains the same stabilization and image hypotheses and records the germ-compatible
identification used to define the stalk ideal.

lem-weil-pbc-formal-kernel-shifted-stalk-model: a proved conversion of those
presentations to compatible power-quotient models of shifted stalks. Source:
Stacks 087X, the displayed quotient calculation before claim (c). The proof handles
the quotient and transition equations explicitly. Both new nodes record actual
LeanSearch, LeanFinder and grep queries; the proof modules introduce one theorem each.
No statement, definition, or existing public visibility changed; no change record
or forced adaptation is required.

## Second reading by Y2

1. The delivered item and both added modules compile with `lcompile.py`; existing theorem signatures were compared byte for byte with the repository. Verdict: pass.
2. The quotient transition proof uses the shifted stalk model and proves the kernel calculation by quotient representatives; the remaining stalk presentation theorem is a strictly simpler decomposition with a source and complete proof sketch. Its statement matches the Lean declaration and is needed by the proof. Verdict: pass.
3. No hollow definitions, axioms, unsafe declarations, or forbidden proof devices were found. The only remaining `sorry` is the named stalk presentation theorem and has its DAG node. Verdict: pass.
4. Imports removed from the item are listed above; the new proof dependencies and node records agree with the declarations used. Verdict: pass.
5. The unit route is preserved: the original exactness statement remains unchanged, and the new lemmas refine its proof below the unit level. Verdict: pass.

Changed the item proof and imports, added the shifted stalk model module, and added the stalk presentation module and DAG nodes. No target statement or definition was changed.
