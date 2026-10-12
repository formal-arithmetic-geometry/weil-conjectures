## What changed

Proved `LinearMap.idempotent_image_baseChange` in
`Sheaf.LinearAlgebra.IdempotentImageBaseChange`, with its signature unchanged.
Added proof-only imports `Mathlib.LinearAlgebra.Projection` and
`Mathlib.LinearAlgebra.TensorProduct.Pi`. All original public imports are needed
for the statement and its finite/projective conclusions.

The proof uses Mathlib's projector complement identities and the split-summand
projectivity theorem. It tensors the inclusion and retraction of the projector
range and uses `TensorProduct.piScalarRight` to identify the ambient tensor
product with the coordinate module. A pure-tensor matrix calculation proves
the two split maps compose to the entrywise base-changed projector. Their
opposite composite is identity, proving injectivity, idempotence, range equality,
and the canonical equivalence. Updated the existing node's proof steps to
record these exact maps; its dependencies and the unit route stay the same.

## Proved and sorry left

Closed the only hole: `LinearMap.idempotent_image_baseChange`
(node `lem-weil-pbc-idempotent-endomorphism-image-base-change`).
One of one original sorries proved; zero holes added or split off.
No sorry remains in the delivery. The complete proof compiles cleanly through
`lcompile.py`. All mathematical input is proved Mathlib theory.

The argument includes `n = 0`, the zero and identity projectors, arbitrary ring
maps, and zero rings: no nonzero, flatness, injectivity, or positivity hypothesis
is used. Tensoring preserves this injection because it is split.

## No longer needed

None. No imports were removed and no planned dependency was bypassed.
The existing universal-property dependency is supplied directly by Mathlib's
base-change pure-tensor formulas, as recorded by that dependency node.
No new Sheaf dependency modules are imported.

## Where the brief, the DAG or earlier work was wrong

No mathematical error found. The base-change assertion needs no flatness
assumption because the original inclusion admits an explicit linear retraction.
Mathlib provides the finite-coordinate tensor equivalence and all the split-map
machinery, so no new intermediate statements are necessary.

## Second reading by A2

1. Compared the delivered Lean module and node against the repository with `diff`.
   Pass: the existing theorem signature and docstring are byte-for-byte unchanged;
   only its proof and two plain, proof-only imports were added. No definitions,
   target statements, or other modules changed, and no change record is needed.
2. Independently compiled the complete file with `lcompile.py`: clean, no warnings.
   Compiled a scratch copy with `#print axioms LinearMap.idempotent_image_baseChange`:
   exactly `propext`, `Classical.choice`, and `Quot.sound`. Inspected the entire proof:
   no sorry, forbidden declaration, hollow definition, or arbitrary unproved witness.
   Pass: the explicit inclusion/retraction and coordinate equivalence construct the maps.
3. Pass: no new or split-off statements and no new nodes. Checked the mathematics at
   n = 0, p = 0, p = 1, and for zero rings and noninjective ring maps. The split
   retraction survives tensoring without flatness, including these cases.
4. Pass: searched the library, upstream source, and Mathlib by range/baseChange,
   projector, and split-map concepts; found no existing theorem replacing the whole
   assertion. The proof uses Mathlib directly for complementarity, projectivity,
   scalar tensor equivalence, and the universal-property formulas. Each original
   public import supplies statement vocabulary; both new plain imports supply used
   proof declarations. The sole old proof dependency is the Mathlib-matched module
   base-change universal property, realized by the tensor formulas used here, so no
   old dependency is unused. Checked `dag/units/sk-thm-p1.json` realized statement and
   steps: none is removed or bypassed by this local projector calculation. The
   No longer needed section is complete.
5. Pass: the node's three proof steps describe the actual complement, split tensor
   maps, matrix computation, and range equivalence. Its proof_deps is exactly the
   union of the steps' uses; the universal-property dependency has a Mathlib match.
   The source-based proof_origin still accurately describes this argument. All other
   node fields are unchanged, and no new-node checks are required.

Second reading changed only this report: no repair to the Lean proof or DAG was needed.
Independently confirmed one original hole closed and zero holes added.
