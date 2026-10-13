## What changed

Proved `AlgebraicGeometry.Scheme.Modules.changeOfRings_tensor_balancing_universal_exists`
in `Sheaf.AlgebraicGeometry.ChangeOfRingsTensorBalancingExists` without changing its signature,
visibility, docstring, or imports. Evaluating the action-composite equality supplies the balanced
pairing. Mathlib `TensorProduct.liftAddHom` constructs its sectionwise additive lift; tensor
induction proves O-linearity and naturality. Restriction of the sheafification unit remains
locally bijective, so `PresheafOfModules.homEquivOfIsLocallyBijective` extends the presheaf map
into the given O-module sheaf. The tensor sheafification adjunction and pure-tensor
extensionality prove the required composite equality. Updated the existing node's proof,
proof dependencies, and proof origin to this direct route. No interface or other module changes. The local single-file compile is clean; the delivery
axiom probe found no axioms beyond propext, Classical.choice, and Quot.sound.

## Proved and sorry left

Closed the sole hole:
`AlgebraicGeometry.Scheme.Modules.changeOfRings_tensor_balancing_universal_exists`
(node `aux-lem-weil-pbc-change-of-rings-tensor-balancing-universal-exists`).
No holes remain in this module; no holes or new declarations were added elsewhere.
This is a proof, not a decomposition. The sectionwise restriction construction used is
already proved in `Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProduct`.

## No longer needed

Removed the proof dependency on `lem-weil-pbc-change-of-rings-tensor-balancing-universal`
(module `Sheaf.AlgebraicGeometry.ChangeOfRingsTensorBalancingUniversal`). It is a consumer
of this clause and must not be imported to prove it. It remains needed by its own consumers;
this is removal of the circular edge, not a claim that the parent module is globally unused.
No imports were removed: all three existing public imports support the unchanged statement.
No additional action-map construction, uniqueness clause, cokernel presentation, or
restriction/sheafification comparison module is needed for this proof. No unit statement or
realized unit step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The node's old sole proof dependency was its parent universal property, whose proof already
uses this existence clause. Following that edge would be circular. The parent docstring,
however, gives the valid sectionwise balancing/sheafification argument implemented here.
Mathlib's locally bijective module-map universal property avoids constructing a separate
restriction/sheafification isomorphism and correctly permits Q to have only an O-action.
No mathematical statement correction was required.

## Second reading by U4

1. Compared the delivered Lean module with the repository version by `diff` and checked
   the complete existing theorem signature byte for byte. Verdict: unchanged. The only
   Lean changes are scoped elaborator options and the proof replacing the sole `sorry`;
   imports, visibility, definitions, and the existing docstring are unchanged. The node
   changes only `proof`, `proof_deps`, and `proof_origin`; there are no change records or
   adapted modules.
2. Compiled the delivered file locally with `lcompile.py` (clean, about 15 seconds), then
   compiled a scratch copy with `#print axioms` for
   `AlgebraicGeometry.Scheme.Modules.changeOfRings_tensor_balancing_universal_exists`.
   Verdict: only `propext`, `Classical.choice`, and `Quot.sound`. No forbidden declarations,
   holes, or overlong lines occur. Read the imported change-of-rings construction:
   `exists_changeOfRingsMap` is proved, and its pure-tensor formula uniquely determines
   `changeOfRingsMap`; the choice used here is not an arbitrary unproved witness.
3. No statements were split off and no new declarations or nodes were introduced.
   Verdict: no new mathematical obligations. Checked the construction on zero tensors,
   sums, and empty opens: it uses additive maps, tensor induction, and sheafification,
   with no nonemptiness assumptions. The balanced equation follows from the specified
   `a`, `d`, and their composite equality; only O-linearity of Q is used.
4. Read the proof from its conclusion backwards: pure-tensor extensionality reduces
   `g ≫ t = f` to the given formula for g and the sheafification factorization of the
   explicitly constructed sectionwise balanced lift. Rechecked library balancing
   declarations with `rg` and Mathlib ingredients with launcher `msearch.py` (`grep`,
   `homEquivOfIsLocallyBijective|liftAddHom|balancing_universal`). Verdict: the proof uses
   the existing tensor and locally bijective universal properties directly; no shorter
   ready-made sheaf theorem was found. All three public imports serve the unchanged
   signature. The old parent dependency is completely listed under No longer needed;
   the parent itself still consumes this existence clause. Read `dag/units/sk-thm-p1.json`
   including `realized`: this auxiliary construction bypasses no realized unit step.
5. Read both versions of the node against the Lean proof. Verdict: the four new steps
   record respectively balancing and additive lifting, O-linearity and naturality,
   extension along the locally bijective unit, and pure-tensor comparison. Their uses
   have union exactly the recorded `proof_deps`; `proof_origin` identifies the source
   and actual route. No statement, source, blueprint, or unit record was changed.

Second-reading changes: appended this independent review only. No repair to the proof,
imports, or node was necessary. Confirmed one hole closed, zero holes added, and no
module import pruned (the circular parent DAG dependency alone was removed).
