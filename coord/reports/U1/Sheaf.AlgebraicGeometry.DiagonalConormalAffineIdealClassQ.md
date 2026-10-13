## What changed

The unchanged declaration `AlgebraicGeometry.diagonalConormal_affine_ideal_class_q`
is proved from an affine-chart comparison. Its proof constructs the affine open W
as the image of the self-fibre product of U over V, proves Δ⁻¹W = U, and computes
the diagonal section map in the supplied coordinates as tensor multiplication.
It proves surjectivity using a ⊗ 1, identifies the kernel with the Kähler ideal,
and converts the tensor-ring linear comparison into an A-linear equivalence.
The required formula follows for every inclusion proof by proof irrelevance.

The new module `Sheaf.AlgebraicGeometry.AffineOpenKernelConormalSections` proves
`AlgebraicGeometry.Scheme.Modules.affineOpen_kernel_conormal_sections` from the
existing `affine_conormal_sections_existence` and an open-chart transport lemma.
It proves that the restricted affine morphism is closed from section-map
surjectivity, transports the kernel equality through the open-section ring
isomorphisms, and composes the two comparisons with explicit scalar and unit
calculations. This declaration contains no sorry.

The new module `Sheaf.AlgebraicGeometry.OpenKernelConormalTransport` isolates only
localization of the actual kernel and its tensor pullback, with unit compatibility.
It has no tensor coordinates, no ideal quotient, no Kähler differentials and no
A-linearity conclusion. The main theorem and affine-chart helper contain complete
Lean proofs combining it with existing results; the original hole has not simply
been renamed. All existing statements, definitions and public imports are unchanged.
No existing module other than the assigned item is adapted.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.diagonalConormal_affine_ideal_class_q`
(node `stage3-diagonal-conormal-affine-ideal-class-q`): 1 of 1 original holes.
Also proved the new declaration
`AlgebraicGeometry.Scheme.Modules.affineOpen_kernel_conormal_sections`
(node `lem-sc-affine-open-kernel-conormal-sections`).

Added exactly one remaining hole:
`AlgebraicGeometry.Scheme.Modules.open_kernel_conormal_transport`
(node `lem-sc-open-kernel-conormal-transport`). Its proof is exactly `by sorry`.
There are no sorries in the assigned module or in the affine-chart helper, and
no definitions were added or changed. This is a decomposition, with one hole
closed and one strictly smaller localization hole added; its net hole count is zero.

All three modules compile without warnings through lcompile.py in import order.
The remaining theorem was checked mathematically on an identity morphism, empty
opens, an empty closed subscheme, and a morphism which is only closed on the chosen
chart. The preimage equality is essential and retained: U is the entire inverse
image of W. No global separatedness, quasi-compactness or quasi-coherence is assumed.
The affine helper also allows zero-ring charts, using the same surjective map and
kernel identities. Its source is Stacks Tags 01R3, 00A0 and 0096; the main chart
calculation is the affine calculation of Tag 08S2. The tags were read online.

## No longer needed

Removed the assigned module's direct proof import
`Sheaf.AlgebraicGeometry.AffineConormalSectionsExistence`, replacing it with
`Sheaf.AlgebraicGeometry.AffineOpenKernelConormalSections`.
The original affine conormal theorem remains needed and is imported by the new
helper. Consequently no original dependency node or module is globally pruned.
The original diagonal-conormal definition and pullback-adjunction dependency remain.
Added only `Mathlib.AlgebraicGeometry.PullbackCarrier` for the chart-range proof.
No source-library PullbackCarrier import or affine tensor-chart existence/core lemma
is needed: the two assumed projection formulas suffice for the multiplication map.
The old direct proof-dependency edge to
`lem-weil-pbc-affine-conormal-sections-existence` is replaced by the new affine-chart
helper; that node remains reached through the helper. The second reading removed
the redundant direct public import `Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree`
from OpenKernelConormalTransport, since its public IdealSheaf.Module import already
exports it. This removes no reachable module.

## Where the brief, the DAG or earlier work was wrong

The planned application of affine_conormal_sections_existence is not a direct
application to Δ: the theorem requires a globally closed immersion and uses its
quasi-coherent ideal module, while this item's Δ may only be closed on W and uses
the actual module-sheaf kernel. The missing interface is localization, including
the canonical-unit comparison. The existing nonempty_tensorPullback_open_kernel
also assumes the original morphism globally closed and does not provide that unit
formula, so it cannot fill this gap unchanged.

The local Stacks source file named by the old node was absent on this machine;
the cited tags were read from the Stacks Project website. LeanSearch returned
Internal Server Error; no absence verdict was drawn from that service. LeanFinder,
Loogle, focused Mathlib searches and project searches supplied the other checks.
No mathematical error or change of the unit route was found.

## New nodes

`lem-sc-affine-open-kernel-conormal-sections`, in
`dag/nodes/sec-picard-framework/lem-sc-affine-open-kernel-conormal-sections.json`,
records the proved generic affine-chart comparison. Its module is
`Sheaf.AlgebraicGeometry.AffineOpenKernelConormalSections`; the kernel, closedness,
scalar transport and unit calculation are all written in Lean.

`lem-sc-open-kernel-conormal-transport`, in
`dag/nodes/sec-picard-framework/lem-sc-open-kernel-conormal-transport.json`,
records the remaining localization statement. Its module is
`Sheaf.AlgebraicGeometry.OpenKernelConormalTransport`. It compares sections of the
restricted closed-immersion ideal pullback with sections of the original actual
kernel pullback, and retains the included-section and canonical-unit equations.
It inherits the item's chapter, unit and blueprint ancestor. Its docstring contains
the complete natural-language restriction/adjunction proof. No change record is
required, since no existing signature, definition or visibility changed.


## Second reading by U1

1. Interface: PASS. Compared the assigned module with the repository by diff and
   checked the full declaration signature, including its tensor-coordinate hypotheses
   and its formula for every inclusion proof. The signature and existing public
   imports are byte-for-byte unchanged. Neither new module exists in the repository;
   no other existing module is adapted, no definition is changed, and no change
   record is needed. The existing node changes only its proof, proof_deps and
   proof_origin among the fields accepted for a stage-3 delivery.

2. Proof and trust: PASS as a decomposition. All three modules compile locally
   without warnings. A scratch module printed axioms for all three declarations:
   each uses only propext, Classical.choice, Quot.sound and sorryAx. The one explicit
   remaining sorry is exactly the named open_kernel_conormal_transport theorem.
   There are no definitions containing sorry and no prohibited declarations or
   attributes. The upper proofs still depend on that localization hole and existing
   open dependencies; this is not a sorry-free target proof or positive net progress.

3. Split statements: PASS. Read both new signatures and their docstring arguments,
   and independently checked Stacks Tags 01R3, 00A0 and 0096. The preimage equality
   makes the open square Cartesian, so restriction identifies the actual kernel
   even without a global closed-immersion or quasi-compactness hypothesis. The local
   closed-immersion ideal is that kernel. The canonical left-adjoint comparison
   transports the unit and the displayed scalar action. Identity maps give zero
   conormal modules, empty opens give zero sections, and a morphism closed only on
   the chosen chart is allowed because its entire preimage is U. Zero-ring affine
   charts require no nontriviality assumption. The open transport has no affine,
   tensor-coordinate, ideal-quotient or differential conclusion, and is strictly
   a localization part of the original argument. Repeated searches with different
   wording through LeanFinder, Loogle and rg. Read OpenRestrictionKernelModule,
   KernelTensorPullbackIsoExists, TensorUnitOpenLocalization, and the upstream
   IdealSheaf.Module interface. The first two require globally closed immersions;
   the slice-site localization result does not identify the restricted kernel with
   the ideal module or provide this chart section comparison. None is an exact
   substitute. Closing the remaining transport requires a sheaf-level construction
   and unit calculation, not a few-minute application of an existing declaration.

4. Route and pruning: PASS. Read the full chart proof from its target downward:
   preimage and affineness, multiplication and surjectivity, the affine conormal
   comparison, then scalar restriction. The two projection assumptions suffice;
   no separate tensor-chart existence theorem is needed. Read the unit record
   dag/units/sk-thm-picard-duality.json and its realized field. This delivery changes
   neither that field nor any realized unit statement or step: the calculation is
   below the unit route. The original affine-conormal dependency remains used
   transitively; the report now explicitly lists its removed direct edge. Public
   imports in the new modules support their signatures. Removed one redundant
   direct PullbackFree import from the transport module, already publicly exported
   by its IdealSheaf.Module import. No original dependency module is globally pruned.

5. Nodes: PASS. Checked all three node files against the actual Lean signatures
   and proof bodies. The original node records the chart/multiplication/scalar
   argument and cites the new affine helper; that helper cites precisely the old
   affine conormal comparison and new transport used by its proof. The remaining
   transport node records the restriction, kernel and adjunction-unit argument,
   its source, searches, statement dependencies, proof dependencies, creation and
   Lean records, and the inherited chapter, unit and blueprint ancestor. Both new
   nodes have matching public declarations and complete natural-language proofs.

Changes by this reading: removed the redundant transport-module PullbackFree
import, made the direct-edge pruning report explicit, and added this independent
review. No mathematical statement or Lean proof body needed repair.
