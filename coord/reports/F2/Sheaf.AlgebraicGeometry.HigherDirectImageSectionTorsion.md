## What changed

Replaced the sole sorry in HigherDirectImageSectionTorsion by a complete Lean proof from
presheaf localization, affine-basis sheafification, and the existing canonical
higherDirectImagePresheaf comparison. Added two separate modules for the unfinished
localization and basis-comparison steps. Existing signatures and public imports stay identical.
The main module uses three proof-only imports. No data is chosen from an unproved existence:
I is the standard injective resolution, and the comparison morphisms are explicit.

## Proved and sorry left

Closed AlgebraicGeometry.Scheme.Modules.higherDirectImage_section_pow_annihilates
(node lem-pc-higher-direct-image-section-torsion); no sorry remains in the item.
Added two named holes:
- AlgebraicGeometry.Scheme.Modules.higherImageCohomologyPresheaf_isLocalized,
  node lem-pc-higher-image-cohomology-presheaf-localization.
- AlgebraicGeometry.Scheme.Modules.isIso_sheafificationUnit_app_of_affine_localizing,
  node lem-pc-affine-localizing-presheaf-sheafification.

This is a decomposition: one upper hole closed and two lower holes added. It is not
an unconditional sorry-free proof. The first step concerns presheaf cohomology, never
higher-image sheaf sections; the second is independent of f, F and derived functors.
Both are strictly separate parts of the original argument. All three modules compile.
The delivery's direct hole balance is 1 closed minus 2 added, hence -1; it claims no
net reduction of holes in the targets' import closure.

## No longer needed

No existing import was removed: the item initially imported only DirectImage.Basic.
No mathematical branch is pruned: invertS_cohomology, the associated-module sections,
and sheaf-on-basis extension remain needed under the two new nodes.
The original direct proof dependencies lem-sc-invert-s-cohomology,
lem-weil-pbc-spec-module-tilde-sections, and lem-weil-pbc-sheaf-on-basis-extends now sit
under the appropriate intermediate nodes. Convention and coefficient definitions
remain statement dependencies. The cyclic DirectImage.Sections affine comparison
and quasi-coherence theorem are not imported. Pruned modules: none.
Explicitly, def-pc-morphism-conventions and pqf-def-coherent also leave the original
node's proof_deps, while remaining in stmt_deps and in the localization node's
stmt_deps. Thus all five removed direct proof dependencies are accounted for;
lem-weil-pbc-higher-direct-image-presheaf remains a direct dependency.
The second reading replaced the new basis module's unnecessary public import
Mathlib.AlgebraicGeometry.Modules.Tilde with the statement dependencies
Mathlib.AlgebraicGeometry.Modules.Presheaf and Mathlib.AlgebraicGeometry.AffineScheme.

## Where the brief, the DAG or earlier work was wrong

The original plan is mathematically sound, but its interfaces leave tensor-unit
fraction identification, scalar compatibility, and the canonical affine sheafification
comparison to implement. An arbitrary additive localization equivalence would not
suffice: the scalar action and canonical restriction must be identified. These are
spelled out in the new docstrings. No statement, definition, or unit route was changed.
The unit record has empty realized lists; this delivery keeps the item's existing route.
The ancestor script returns None because created.item is a module name; the existing
blueprint.from correctly identifies lem-pc-finite-support-hi and is used for the new nodes.

Read Stacks 09MR, 01E4, 01HV, 009N and 009Q online because the local Stacks sources
are absent. WANTED: local Stacks cohomology.tex, cohomology-schemes.tex, schemes.tex,
and sheaves.tex for these tags. Proof origins are marked agent. LeanSearch returned
Internal Server Error (recorded unavailable); LeanFinder, Loogle, and grep ran.
The existing module_sheafification_iso_of_affine_restriction requires a given basis
isomorphism with a global sheaf, which is precisely the construction missing here;
it does not immediately prove the new localizing-presheaf theorem.

Checked edge cases: q=0, zero coefficients, a=0, units a, empty affine W. At a=0
the target localization is zero. For empty W, Γ(T,W) is the zero ring, so every
unital section module is zero. The basis argument stays inside W and needs no
separatedness of T. The canonical injective-resolution choice is existing proved data.

## New nodes

lem-pc-higher-image-cohomology-presheaf-localization: specialization of 09MR to
presheaf homology of a pushed-forward injective resolution, with canonical linear
restriction. Module HigherImageCohomologyPresheafLocalization.

lem-pc-affine-localizing-presheaf-sheafification: general presheaf theorem recovering
its affine sections after sheafification from localization on principal opens.
Module AffineLocalizingPresheafSheafification. It uses the existing basis-extension
node as a generic tool; it preserves the unit route and does not replace a unit step.
No change record or forced adaptation is needed.

## Second reading by F2

1. Unchanged interfaces: compared the item with the repository using diff and checked
   the theorem signature and section variables byte for byte. Both match exactly.
   The existing public import is unchanged; all three added imports are proof-only.
   Neither new module defines data or changes an existing declaration. No change
   record involving this item was found in coord/changes.

2. Proof and axioms: compiled all three modules locally through lcompile.py, with
   no errors or warnings. Scratch copies with #print axioms for each declaration
   report only propext, Classical.choice, Quot.sound and sorryAx. Exactly the two
   reported public theorems retain sorry; no definition, private helper, axiom,
   unsafe, opaque, implemented_by or extern occurs in the delivered modules.
   Read the actual reduction: theta is the adjoint of the canonical comparison c,
   not a chosen identification. Its affine components are invertible by the unit
   theorem. Naturality and injectivity on D(a) give res(x)=0; eq_zero_iff supplies
   a power killing x; the linear component theta_W transports that equation to t.
   injectiveResolution is standard existing data, not an arbitrary witness chosen
   from an unproved existence statement in this delivery.

3. Split statements: read Stacks Tags 09MR, 01E4, 01HV and 009Q online and read
   invertS_cohomology, higherDirectImagePresheaf, and
   exists_sheaf_extension_of_basis_gluing in the library. The localization theorem
   uses qcqs only over an affine base open and quasi-coherence of F; its arbitrary
   injective resolution computes the same cohomology. The tensor-unit fraction
   formula pins the canonical map and its scalar compatibility. The basis theorem
   quantifies over all affine opens and all their principal restrictions, exactly
   what hP in the main proof supplies. Principal intersections inside W are again
   principal, so the basis extension theorem's intersection hypothesis is met;
   addition and scalar multiplication extend locally from its abelian-group result.
   These are independent portions of the original plan, not aliases of its kernel
   conclusion. Checked a=0, a a unit, q=0, F=0 and W empty: localization at zero
   gives the zero module, at a unit an invertible restriction, and empty W has a
   zero section ring and hence zero unital modules. No separatedness of T is used.
   Each hole has a source, full prose proof and matching new node. Independently
   searched with LeanFinder for the affine-unit localization criterion, Loogle
   for IsLocalizedModule.Away, and grep for affine sheafification/cohomology
   localization. Results give structure-ring localization and algebraic local
   criteria, not either new theorem. An initial Loogle query with unqualified
   IsIso was rejected by that service; the successful replacement query was used.
   Read module_sheafification_iso_of_affine_restriction: it requires an already
   constructed global sheaf and affine-basis isomorphism, so it does not close the
   new theorem immediately. Neither hole has a short existing proof found here.

4. Route and pruning: the original plan's tensor-unit localization, principal-basis
   sheaf comparison and canonical higher-image comparison are all retained.
   Read dag/units/sk-thm-picard-coherence.json: realized.statement and its sole
   realized.steps entry are empty; this delivery changes no unit record or step.
   All removed direct proof dependencies are enumerated above, with mathematical
   dependencies moved to the appropriate lower nodes. No existing module is
   pruned. Replaced the new basis module's tilde import with the narrower imports
   needed by its signature; the repaired module compiles. This is a decomposition,
   not a net proof-completion claim.

5. DAG agreement: the existing node changes only proof, proof_deps and proof_origin.
   Its steps match P, c, theta, affine-unit invertibility and localization torsion
   in the Lean proof. The two new nodes record their exact signatures, source,
   prose steps and dependency union, agent proof origin, searches, split status,
   F2 creation metadata, blueprint ancestor, chapter/unit and Lean records.
   Read the declarations named by their dependencies; the 01HV node supplies
   associated-module principal sections, the basis node supplies extension, and
   the 01E4 node supplies the resolution comparison with restriction compatibility.
   No dependency was replaced by an unproved arbitrary equivalence.

Changes made by this reading: narrowed the new basis module's imports, enumerated
all removed direct proof dependencies, recorded the hole balance, and added this
independent review. No theorem statement or proof was rewritten.

