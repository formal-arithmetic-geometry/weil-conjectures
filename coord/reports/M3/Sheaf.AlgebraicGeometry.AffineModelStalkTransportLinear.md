## What changed

Proved `AlgebraicGeometry.affineModelStalkAddEquiv_smul` in the assigned module,
without changing its statement or the explicit additive equivalence. Four proved
private helpers calculate inverse ring-map germs, restriction-stalk semilinearity,
inverse semilinearity, and the composite chart scalar germ. The middle comparison
uses the existing proved `Scheme.Modules.Hom.stalkLinearMap`.

The germ argument for the first two helpers follows the already proved private
helpers in `Sheaf.AlgebraicGeometry.Modules.RestrictionStalkExtensionIso`; that
module is not imported. The remaining helpers and assembly are proved directly
from Mathlib. The node's existing elementary proof plan is followed; the second reader updated
its proof description and provenance to record the implemented route.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.affineModelStalkAddEquiv_smul`
(node `new-s2-affine-model-stalk-transport-linear`).
No sorries remain in the item, and no holes or modules were added.
The complete file compiles without errors or warnings through `lcompile.py`.

## No longer needed

None. Both existing public imports remain necessary for the definition, its
scalar-action instances, and the proved stalk linear map. No additional project
proof-dependency imports were introduced. No DAG nodes or modules are pruned.

## Where the brief, the DAG or earlier work was wrong

None. The stated plan is executable using germ representatives and ring-map
identities, including arbitrary modules. The zero-module case needs no extra
hypothesis, and the point-membership hypothesis excludes an empty affine chart.

## Second reading by M3

1. Compared the complete module with the repository version. PASS: the existing
   additive equivalence definition (including its body) and theorem signature are
   byte-for-byte unchanged. Only proved private helpers, proof-local elaboration
   options, and the theorem proof were added. No interface change or change record.
2. Independently compiled the delivered file through lcompile.py without errors
   or warnings. PASS: no sorry or forbidden declaration occurs. A scratch copy
   with #print axioms for both public declarations and all four private helpers
   reports only propext, Classical.choice, and Quot.sound, with no sorryAx.
   The inverse maps are inverses of explicit isomorphisms; no arbitrary witness
   is selected from an unproved existence theorem.
3. PASS: no statements were split off and no new holes were added. Read all four
   private proofs: common-neighbourhood germ representatives prove semilinearity,
   bijectivity proves the inverse formula, and chart section-ring identities prove
   the scalar germ formula. These arguments apply to zero modules and arbitrary
   scalars; an empty chart has no hx. The helpers are fully proved, not renamed
   versions of the target.
4. PASS: searched the library and Mathlib for restriction-stalk scalar identities,
   semilinearity, and inverse stalk-map germ formulas. Existing reusable public
   declarations supply the germ formulas and the middle stalkLinearMap; the two
   identical helpers elsewhere are private. No shorter public assembled scalar
   transport identity was found. Both public imports are needed: Tilde supplies
   the model and coordinate action; FlatPullbackStalk supplies the module action
   on arbitrary scheme-module stalks that the theorem's statement uses. The old
   proof_deps list is empty, so No longer needed is complete. Read the unit's
   realized record: this elementary argument bypasses no realized unit step.
5. PASS after documentation repair: retained the node's statement and empty
   proof_deps, and updated only proof and proof_origin to name the actual germ
   calculation and the M3 proof provenance. No new nodes are needed.

Second reading changed the DAG proof description/provenance and this report;
no Lean repair was necessary. Net holes closed: 1; holes added: 0.
