## What changed

Proved `AlgebraicGeometry.exists_selfTor_nonpositive_chosen_comparisons` from intrinsic
derived self-Tor coordinates, bounded-above flat K-flatness, the existing proved
K-flat derived tensor comparison, and the existing proved augmented quotient tensor
comparison. The signature and public imports of the assigned module are unchanged.

The proof constructs a global sheaf isomorphism by tensoring the inverse of Q(q),
composing the K-flat tensor counit, then taking derived homology and its factorization.
It composes the intrinsic coordinates with the induced section equivalences, constructs
psi/a/k from kernel-ideal containment, and proves the element equation by naturality.
This discharges the resolution-dependent transport and the algebraic lift construction.

One new module `Sheaf.AlgebraicGeometry.DerivedSelfTorAffineCoordinates` isolates the
remaining geometric step for a fixed intrinsic object: it has no K, q, flatness or
boundedness inputs, and it does not construct comparison lifts. Its restriction formula
is conditional on supplied augmented lifts. The external-resolution identification,
lift existence and transport back to the original homology are proved in the parent,
not assumed by the new lemma. Both files compile locally. The continued attempt also replaces the parent docstring
with the actual derived-tensor transport proof, rather than the superseded cone zigzag.

## Proved and sorry left

Closed: `AlgebraicGeometry.exists_selfTor_nonpositive_chosen_comparisons`
(node `new-h3-self-tor-nonpositive-chosen-comparisons`), 1 of 1 original holes.
No sorry remains in the assigned module.

Added: `AlgebraicGeometry.exists_derived_selfTor_affine_coordinates`
(node `new-p1-derived-self-tor-affine-coordinates`), exactly `:= by sorry` in its own module.
This is a decomposition, with one hole closed and one added, not a net hole elimination.
No definition or arbitrary data choice from a sorried existence theorem was added.

## No longer needed

Removed direct proof imports from the assigned module:
- `Sheaf.AlgebraicGeometry.AffineQuotientResolutionSheafification`
- `Sheaf.AlgebraicGeometry.Modules.IsKFlatRestriction`
- `Sheaf.AlgebraicGeometry.AffineChartTotalTensor`
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorClosed`
- `WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone`
- `WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic`

The following old direct `proof_deps` are all removed from the assigned node:
- `lem-pc-affine-chart-total-tensor`
- `lem-pc-kflat-open-restriction`
- `lem-pc-sheaf-modules-tensor-closed`
- `lem-pc-tensor-mapping-cone-iso`
- `lem-pur-quasi-iso-cone-acyclic`
- `lem-sc-affine-quotient-resolution-sheafification`
- `lem-weil-pbc-affine-tilde-gamma-adjunction`
- `lem-weil-pbc-spec-module-tilde-sections`

The affine total-tensor, tilde adjunction and tilde sections nodes remain in the
new intrinsic lemma's proof plan; K-flat restriction and tensor closedness remain
transitive comparison dependencies. This list records removal from the parent
node, not removal from the targets' import closure.

The direct cone proof nodes `lem-pc-tensor-mapping-cone-iso` and
`lem-pur-quasi-iso-cone-acyclic`, and the sheafified-resolution existence node
`lem-sc-affine-quotient-resolution-sheafification`, are no longer needed by this route:
the proved derived tensor counit replaces the augmentation-cone zigzag.
The remaining affine calculation uses the quotient module identification and the
existing affine derived tensor chart comparison instead of that resolution existence
statement. Open K-flat restriction, affine total tensor, and tensor closedness remain
transitive tools of the existing comparison APIs; no claim is made that their modules
leave the full target import closure. Global closure pruning is for the ledger to measure.

## Where the brief, the DAG or earlier work was wrong

No false statement or tool defect was found. The original plan is mathematically valid;
its affine derived normalization and naturality require more interface glue than its
listed existence statements alone expose. In particular an arbitrary quotient sheaf
isomorphism cannot establish the required normalized section square. The new lemma's
proof explicitly constructs the quotient-section-normalized identification and carries
that normalization through the tensor and homology comparisons.

The unit record `sk-thm-picard-duality` has no realized nodes for its statement or step;
this change concerns only the local self-Tor calculation below that unit, and changes
no unit or chapter route. Sources read: Stacks 08DX(2), 06YH, 01I9 and 00LS(1),(2).
Searches: Lean Finder, Loogle, Mathlib grep, local SelfTor modules, and imported
blueprint searches; LeanSearch was unavailable with Internal Server Error.

Edge checks: n=0 keeps the augmentation; I=top gives a zero quotient and zero
self-Tor; the empty affine/basic open has zero sections and the same zero comparison.
For the identity immersion I=0, positive self-Tor vanishes. Neither scheme separation
nor flatness of arbitrary ring homomorphisms is assumed: only basic open restrictions
are used in the geometric equation. Projectivity of restricted target terms is not used.

Verification on continuation: both sandbox modules compiled (4.1 seconds for the
intrinsic lemma and 14.3 seconds for the assigned module). The dry run printed OK;
the final dry run follows the docstring correction. Repeated Lean Finder search found
basic-open ideal localization tools, but no geometric derived self-Tor theorem.
The existing new lemma is a strict geometric subargument: the parent still proves
resolution-dependent transport, existence of augmented lifts, and the final naturality
calculation. The remaining hole is reported as a decomposition, not a net proof.

## New nodes

`new-p1-derived-self-tor-affine-coordinates`, in
`dag/nodes/sec-picard-framework/new-p1-derived-self-tor-affine-coordinates.json`, states
the intrinsic derived geometric calculation with supplied lifts and records the affine
construction, normalized homology coordinates and basic-open naturality proof.
Its chapter/unit and blueprint ancestor are inherited from the assigned item.
No change record is needed: no existing statement, definition or visibility changes.

## Second reading by P1

1. Compared the assigned module with the repository version. The theorem signature and its public imports are unchanged; only the proof-local imports, options, docstring, and proof body differ. Verdict: pass.

2. Compiled both delivered modules with `lcompile.py --all`; compilation succeeds. The only remaining `sorry` is the named theorem `AlgebraicGeometry.exists_derived_selfTor_affine_coordinates`, and it is isolated in its own module and node. No definitions contain `sorry`; no forbidden declarations were added. The scratch axiom checks for both declarations report only `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx` (the intrinsic lemma and any still-open upstream dependencies). The existential coordinates are eliminated inside a proof of a proposition; they are not used to define any object. The derived tensor structure is the existing fixed K-flat construction. Verdict: pass.

3. Reviewed the split statement and node. It is a strict intrinsic affine coordinate subargument: it has no K, q, flatness, boundedness, or lift-existence inputs, and its restriction formula is conditional on supplied augmented lifts. Its docstring gives the construction and cites Stacks Tags 08DX(2), 06YH, 01I9, and 00LS; I read these sources. Checked n=0 (ordinary quotient tensor), I=top and empty opens (zero modules), and I=0 (zero higher Tor). For identity inclusions, quotient surjectivity forces psi=id and augmented resolution maps induce identity homology, so arbitrary supplied lifts do not contradict naturality. Projective source terms suffice after restriction of scalars; target projectivity is not assumed. Independent Lean Finder, Loogle, service grep and local rg searches found only algebraic/tilde tools or downstream self-Tor results, not an acyclic replacement for the geometric theorem. Verdict: pass.

4. Checked pruning and route. The parent now uses the proved K-flat derived tensor comparison, the quotient-resolution tensor comparison, and the new intrinsic lemma; the removed cone and sheafified-resolution imports are not used by the proof. The parent proof still follows the intrinsic derived tensor route and the unit route is unchanged. Verdict: pass.

5. Checked DAG agreement. The parent node proof steps and `proof_deps` match the Lean proof, and the new node records its statement, source, proof plan, searches, module, declaration, chapter, and unit. Verdict: pass.

Second-reader changes: report only, recording these checks and the decomposition verdict; the first worker's Lean and node files needed no repair. Mechanically checked the existing signature byte for byte, both nodes' recorded Lean statements, and equality of each proof dependency list with the union of its proof-step uses. The new public imports supply its exposed signature and derived tensor instance; the geometric proof-plan imports are plain imports. The unit has realized.statement=[] and realized.steps=[[]], and no unit is bypassed. The intrinsic geometric hole needs substantial comparison glue and is not closable by a short existing-lemma application. One original hole closed and one hole added gives net zero; no global module pruning is claimed. Delivery dry run passed and printed OK (CODEX).
