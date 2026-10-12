## What changed

Replaced the sole `sorry` in
`lean/Sheaf/AlgebraicGeometry/IsolatedFibrePointBaseChange.lean` with a complete proof.
Added the proof-only import `Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite`.
All public signatures, public imports and existing docstrings are unchanged.
The second reading also updates the item’s DAG proof and proof_origin.

The proof follows the node's four steps. Mathlib's
`isPullback_fiberToSpecResidueField_of_isPullback` identifies the cartesian square
of fibres. The projection identity `pullback.lift_fst` identifies the chosen
point, with `fiberHomeo` and `Homeomorph.setCongr` transporting the open-singleton
hypothesis between equal base points.

The fully proved private helper `isOpen_singleton_of_field_pullback` implements
steps 2–4. It constructs the actual open singleton subscheme U. Its structure
map is locally of finite type and injective because its domain is subsingleton,
so `LocallyQuasiFinite.of_injective` applies. Pasting
`isPullback_morphismRestrict` with the fibre square shows that the inverse-image
open subscheme is its base change. Stability of local quasi-finiteness and
`IsLocallyArtinian.of_locallyQuasiFinite` give discreteness over the extension
field. The open inclusion sends the chosen point's open singleton to the
required singleton. This is the Mathlib realization of the existing
`lem-weil-pbc-discrete-field-base-change-artinian` and open-base-change steps,
not a different unit route. The second reading updates the original node’s proof and proof_origin to record
these exact Mathlib realizations. Its proof_deps remain applicable and unchanged.

Validation: local compilation succeeds without warnings. The delivery dry run
also compiles with the project's axiom probe and checks the delivery format.
The helper admits arbitrary fields and arbitrary maps between their spectra;
no finiteness or separability assumption on the extension, reducedness of the
singleton scheme, or global quasi-finiteness assumption on f is added.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.isolated_fiber_point_base_change`
(node `lem-weil-pbc-isolated-fibre-point-base-change`).

The private helper `isOpen_singleton_of_field_pullback` is also fully proved.
No `sorry` remains in the item's module. No holes are added or split off, and
no unproved library theorem is used.

## No longer needed

None. No imports are removed. All original proof dependencies describe steps
still used, realized entirely by their Mathlib declarations and instances.
No Sheaf or WeilConjectures proof-dependency module needs to be imported.
No unit-level statement or step is bypassed.

## Where the brief, the DAG or earlier work was wrong

No mathematical correction was needed. The short proof is available by
assembling the Mathlib leaves already recorded in the node. The open pullback
is constructed directly as the inverse-image open subscheme, with its
cartesian square given by `isPullback_morphismRestrict`; a separate pullback
object and range calculation are unnecessary.

## Second reading by E2

1. PASS: diffed the sole delivered Lean module against the repository. The existing
   theorem signature, both public imports, and its docstring are byte-for-byte
   unchanged. Only a proof-only QuasiFinite import, a fully proved private helper,
   and the replacement proof are added. No definition or change record is needed.
2. PASS: compiled with lcompile.py without errors or warnings. A scratch copy’s
   #print axioms checks for both the helper and isolated_fiber_point_base_change
   show only propext, Classical.choice, and Quot.sound. No sorry, axiom, unsafe,
   opaque, implemented_by or extern occurs in the delivered code. U and zU are
   explicitly constructed; no object is chosen from an unproved existence theorem.
3. PASS: no statement is split off and no hole is added. The private helper is a
   proved combination of the existing singleton-open and discrete-base-change
   steps, not a renamed copy of the item. It allows arbitrary maps of field spectra;
   identity extensions and nonreduced singleton schemes require no extra premise.
   Empty source schemes have no chosen z and give a vacuous implication. No global
   quasi-finiteness of the original f is inferred or assumed.
4. PASS: searched Mathlib and both Lean roots for pointwise quasi-finiteness under
   pullback and isolated fibre points, and read the relevant Mathlib declarations.
   No direct scheme-level pointwise base-change lemma provides a shorter route.
   All three imports are used; all eight old proof dependencies remain represented
   by their Mathlib realizations. No imports or nodes are pruned. Read sk-thm-p1’s
   realized statement and steps: this item is below those unit-level nodes and its
   four-step fibre/open-singleton/discrete-pullback/topology argument keeps the route.
5. PASS after metadata repair: proof_deps remains the union of the four steps’ uses.
   Updated proof with the exact fibre transport, singleton injectivity, restricted
   pullback, Artinian discreteness, and open-image arguments. Corrected proof_origin’s
   claim that the implementation avoids quasi-finiteness: it uses local
   quasi-finiteness of the singleton open, as the discrete-field-base-change leaf’s
   Mathlib match already prescribes. No new nodes or statements are introduced.

Second reading changed only the DAG proof/proof_origin and this report. The Lean
proof was sound and required no repair. Closed 1 original hole, added 0 holes,
split off 0 statements; this is a proof, not a decomposition.
