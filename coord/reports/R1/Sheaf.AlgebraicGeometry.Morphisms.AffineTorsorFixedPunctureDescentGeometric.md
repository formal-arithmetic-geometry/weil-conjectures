## What changed

Preserved every original signature, definition, visibility and public import of
AffineTorsorFixedPunctureDescentGeometric. Replaced the final theorem's sorry with
an explicit composition of orbit-component descent and finite-product principal-open
assembly. Added proof-only imports of AffineTorsorOrbitComponentDescent and
FiniteProductPrincipalOpen. Updated the geometric node's route accordingly.

FiniteProductPrincipalOpen gives a complete constructive proof from Mathlib's
sigmaSpec, coproduct reindexing, piCongrLeft, and the open-immersion range API.
Its projection equation is proved by coproduct extensionality and ring-map composition.
The universe lift is necessary because Mathlib's sigmaSpec takes its index type
in the ring universe, whereas Fin m lives in universe zero.

The component-descent theorem keeps the etale and unique-rotation hypotheses and
requires complete, distinct representatives with their exact stabilizers for the
actual label action. It stops at the coproduct of the component principal opens;
it does not include the finite-product spectrum identification.

Validation status: FiniteProductPrincipalOpen compiles locally with no errors or warnings.
Its #print axioms lists only propext, Classical.choice and Quot.sound.
The deliver3.py --no-push dry run was attempted and stops at the missing dependency. Compilation of
the delivered set is currently prevented by the absent published compiled module
Sheaf.AlgebraicGeometry.Morphisms.AffineTorsorSplitAction. The source exists, but
lcompile.py reports that its .olean does not exist. No library or tool was modified
to work around the last-green-build rule. The wrapper therefore still awaits
compilation against the published interface; this report makes no READY claim.

## Proved and sorry left

Closed in the source: AlgebraicGeometry.Scheme.affine_torsor_fixed_orbits_geometric,
from the two genuine argument steps below. Its final compilation is pending the
published dependency. This is a decomposition, not a net reduction in holes.

Proved: AlgebraicGeometry.Scheme.finite_product_principal_open
(node lem-sbc-finite-product-principal-open), with no sorry.

Added exactly one named sorry:
AlgebraicGeometry.Scheme.affine_torsor_orbit_component_descent
(node lem-sbc-affine-torsor-orbit-component-descent).
It has a sourced full natural-language argument and a separate module.
The original fixedOrbitData_of_action proof is untouched. No sorry is added to
a definition, private declaration or partial proof.

## No longer needed

None. The original public imports support the unchanged statements and definitions.
The existing split-label laws remain needed through the component-descent module.
No blueprint unit statement or realized step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The earlier attempt weakened the theorem and removed its essential action and
torsor hypotheses. None of those changes is retained: FixedOrbitData, hEt, hrot,
hD and the full projection equation remain exactly as in the repository.

The original node's only dependency is the split-label-laws module, which supplies
the action but does not state effective orbit-component descent or finite-product
principal-open assembly. The two separate argument steps are now explicit.
The edge cases m=0, d=0 and zero component rings are included in the product theorem;
component descent uses the original domain and nonzero-puncture hypotheses.

The compiled publication lacks AffineTorsorSplitAction despite its presence in
the source checkout. Repeated compilation cannot check the original module until
that dependency is published. The artifact-sync timestamp advances, but that
module remains absent.

## New nodes

lem-sbc-affine-torsor-orbit-component-descent: geometric descent and localization
for the individual orbit components, before product-spectrum assembly. Its sole
sorry is in the corresponding new module AffineTorsorOrbitComponentDescent.

lem-sbc-finite-product-principal-open: the complete finite-product assembly theorem,
proved in FiniteProductPrincipalOpen. It is independent of the geometric torsor
hypotheses, and includes its structural-map compatibility.

No interface change or forced adaptation is made, so no change record is required.

## Earlier second reading (a previous round; superseded)
The item and both split-off modules compile with lcompile.py --all. The
orbit-component theorem is a strict intermediate reduction; finite-product
assembly is independent and fully proved. The remaining orbit-component sorry
is documented and sourced in its declaration and node.

## Second reading by R1

1. **Visible changes and statements.** Compared every delivered module with the
repository version. The existing declarations, definitions, signatures,
visibility, and public imports of the item are unchanged; the target theorem's
proof and its node route are the only existing-node changes. The two added
modules and their node records agree verbatim on theorem statements.

2. **Proof and axioms.** Compiled all three delivered modules individually and
with `lcompile.py --all`; all compile without errors or warnings. The only
remaining `sorry` is the named theorem
`AlgebraicGeometry.Scheme.affine_torsor_orbit_component_descent`, whose source,
docstring proof, and node are present. The finite-product theorem and the target
theorem have no `sorry`; no forbidden declarations occur. The finite-product
proof is constructive up to the permitted Mathlib axioms. The orbit-component
declaration intentionally reports `sorryAx` until its split proof is supplied.

3. **New statements.** Checked both split-off statements against their edge
cases (including empty finite index and zero component rings for finite-product
assembly, and the completeness/distinctness/stabilizer hypotheses for orbit
descent). The orbit statement is a strict intermediate reduction and the
finite-product statement is exactly the independent assembly step; neither
restates the target. Searches found no existing upstream declaration matching
either theorem.

4. **Pruning and route.** The target proof follows the stated route: convert
`FixedOrbitData` to the orbit-component hypotheses, apply component descent,
then apply finite-product principal-open assembly and compose the structural
maps. No unit statement or realized step is bypassed, and no import or proof
dependency can be removed without losing a declaration used by a statement or
proof.

5. **DAG agreement.** Updated proof, `proof_deps`, and `proof_origin` of the
existing target node to match the Lean proof. The two new nodes contain the
required source, proof route, searches, Lean records, chapter, and unit fields;
their status is `split`. No statement-change or forced-adaptation record is
needed.

**Changes made during second reading:** added this required review section only;
no Lean code or theorem statements were changed.
