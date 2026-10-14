## What changed

Replaced the sole sorry in `CartierGenericStalkGaloisModelCore.lean` by a complete
assembly from a concrete integral-closure product presentation and a proved residue
comparison. Its declaration signature and existing docstring are unchanged.
Added two proof-only imports, `CartierStalkNormalizationProduct` and
`StalkProductResidueComparison`.

`CartierStalkNormalizationProduct.lean` states the whole-product geometric step,
independently of any selected point. It specifies actual rings `integralClosure R E_i`
and an isomorphism over `Spec R`; it does not choose data in a definition.
Its proof plan uses the original field-component and stalk-normalization declarations,
whose modules are imported, together with the component Galois-group theorem.

`StalkProductResidueComparison.lean` is fully proved. It lifts the point to the stalk
base change, selects its affine coproduct component, constructs both residue equivalences
from bijective residue maps of preimmersions, and proves the square by affine residue
naturality and morphism composition. Its two private helpers are also fully proved.
The core restricts the field action to the integral closure, proves the base map injective,
uses the finite extension fraction-field theorem, descends the Galois group to the rings,
and lifts it to precisely the canonical fraction-field algebra and action in its signature.

Updated the parent DAG proof and dependencies and supplied nodes for both new modules.
All three delivered files compile together through lcompile.py with no errors or style
warnings. The original public signature remains verbatim. No existing interface, definition,
target, or other group's module changes; no forced adaptations or change records are needed.

## Proved and sorry left

Original hole closed (1 of 1):
`AlgebraicGeometry.Scheme.cartier_generic_stalk_galois_model_core`, node
`lem-sbc-cartier-generic-stalk-galois-model-core`.

New public theorem fully proved:
`AlgebraicGeometry.Scheme.stalk_product_residue_comparison`, node
`lem-sbc-stalk-product-residue-comparison`. Both private helpers,
`residueMap_bijective` and `spec_residue_naturality`, have complete proofs.

One new hole:
`AlgebraicGeometry.Scheme.cartier_stalk_normalization_product`, node
`lem-sbc-cartier-stalk-normalization-product`; its entire proof is `:= by sorry`.
It is the geometric construction before selecting x, not the original assertion
renamed or a hypothesis-repackaged copy. It supplies no residue equivalences and no
action/Galois assertion for the integral closure or its canonical fraction field.
Those steps are now proved in the delivery. This is a decomposition (one upper hole
closed, one lower hole added; net zero holes), with the residue and arithmetic steps
proved, not an axiom-free proof of the entire original result.

## No longer needed

No original import was removed and no original node/module is globally pruned.
The original planned dependencies `FieldTorsorGaloisComponents` and
`NormalizationStalkBaseChange` remain needed below the new product-model node; they
are no longer the direct dependencies of the core. The additional existing
`FieldTorsorComponentGaloisGroup` supplies actual subgroups and actions, which the
field-degree theorem alone does not expose.

The earlier rejected arbitrary-model Data, Residue and unused Aux files remain
excluded from delivery. They are not prerequisites of this proof. No new arbitrary
model residue existence statement is introduced. The geometric scheme isomorphism
in the new proved residue theorem is essential.

## Where the brief, the DAG or earlier work was wrong

The earlier residue split omitted all geometric relation between S and x and was
false: with N = Spec Z and a closed point over p, taking S = Q would demand an
isomorphism F_p with Q. This delivery repairs that issue by retaining an isomorphism
of the entire stalk base change over Spec R, selecting its actual component, and
proving the residue comparison rather than assuming it. The Q counterexample does
not satisfy the new geometric presentation hypothesis.

The original plan is mathematically retained. Its field-component statement exposes
IsGalois and degree divisibility, but not a subgroup action; the separately stated
component Galois-group theorem is needed to supply that action. The original core
docstring mentions flatness, dimension and ring-level Galois conclusions although
its signature requests neither flatness nor dimension; only the ring-level Galois
result is used internally as a proved bridge. Stacks Tag 09EB is the arithmetic
ramification formula, not the geometric model construction; the new node records
0307, 03SF, 03QR and the precise parent steps instead. The unit's realized record
has no nodes assigned, and no unit statement or route is bypassed.

Edge cases checked: empty coproducts have no lifted point and make the residue claim
vacuous; the new product theorem permits n = 0. For the identity/trivial torsor,
its field factor is K and integral closure is the DVR R, giving the correct closed
residue characteristic. Split and disconnected torsors keep every field factor and
allow the proved point-selection step to choose the actual one containing x.
The residue theorem needs neither finite nor domain algebras: its correctness rests
on the explicit coproduct presentation and preimmersion residue isomorphisms.

## New nodes

`lem-sbc-cartier-stalk-normalization-product` in
`dag/nodes/sec-smooth-base-change/lem-sbc-cartier-stalk-normalization-product.json`:
the remaining geometric product-model construction (parent steps 1 and 2), with
concrete integral closures, finite-module statements and structure-map equation;
source, complete proof plan, exact Lean signature and all required search kinds recorded; LeanSearch was unavailable.

`lem-sbc-stalk-product-residue-comparison` in
`dag/nodes/sec-smooth-base-change/lem-sbc-stalk-product-residue-comparison.json`:
general residue comparison from an actual stalk product presentation, corresponding
to parent step 3; fully proved from Mathlib, with its exact signature, proof and
search records (including unavailable LeanSearch). No change record is required.

## Second reading by V3

1. Compared the delivered core module with the repository version. The existing
declaration signature is byte-for-byte unchanged; only proof imports and proof
terms differ. Verdict: pass.

2. Compiled all three delivered modules with `lcompile.py --all`. There are no
compiler errors, forbidden declarations, or unlisted `sorry`s. The sole remaining
`sorry` is the named split theorem `cartier_stalk_normalization_product`, with a
matching DAG node and proof docstring. Verdict: pass.

3. Checked both split-off statements against their source and small edge cases.
The residue comparison requires an actual coproduct presentation and is strictly
more general than the parent residue step; the product theorem contains only the
geometric construction and no selected point or residue assertion. Neither repeats
the parent statement. Verdict: pass.

4. Checked the proof route and pruning. The core uses the product construction,
residue comparison, and the necessary field/Galois arithmetic APIs; the unit route
is preserved and no import or node is removed without justification. Verdict: pass.

5. Checked DAG agreement: declarations, signatures, proof steps, proof dependencies,
origins, new-node metadata, and report entries match the delivered Lean files. The
remaining product theorem is explicitly reported as a decomposition. Verdict: pass.

Changed during second reading: added this required review section only; no Lean,
DAG, or proof changes were needed.
