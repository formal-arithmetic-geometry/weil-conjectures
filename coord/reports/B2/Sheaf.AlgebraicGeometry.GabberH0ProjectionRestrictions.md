## What changed

Proved AlgebraicGeometry.gabber_h0_projection_restrictions without changing its signature,
existing docstring, or public imports. Removed the redundant plain import of
Sheaf.AlgebraicGeometry.EtaleSetInverseImageCompositionUnits, already publicly
re-exported through FiniteSurjectiveSetDescentInjective. Added fully proved private helpers for composition
of section comparisons, equality transports, pullback of a compatibility equation, and
cancellation of the composition comparison. The proof constructs both pullback lifts and
identifies both restricted projections with the same pullback of t. The DAG proof now
records the actual Lean calculation.

## Proved and sorry left

Proved AlgebraicGeometry.gabber_h0_projection_restrictions (the module's one original
sorry). Every private helper is proved. No sorry remains and no new statement is split off.
The proof uses the already proved etaleSetInverseImageCompositionUnits, including its
unit naturality, composition-unit, and associativity clauses. No axioms were added.

## No longer needed

Removed the redundant direct plain import
Sheaf.AlgebraicGeometry.EtaleSetInverseImageCompositionUnits; this module remains
a proof dependency and is reached through the existing public import chain. No
node or module is pruned. The original public import supplies the definitions used in the unchanged statement;
the finite-surjective descent theorem itself is not used in this proof. Both existing
proof dependencies, def-pc-fibre-product and
lem-weil-pbc-sets-etale-inverse-image-composition-units, are used. No unit step is bypassed.

## Where the brief, the DAG or earlier work was wrong

No mathematical error found. The first dry run classified local notations and file-level
options as interface commands. Replaced the notations with full names and scoped every
option to its individual theorem; the interface checker now reports no change. Directly instantiating dependent cast calculations inside the
large target caused excessive kernel conversion; generic proved helpers for equality
transports keep those conversions small. The final proof respects the original plan and
also works for identity morphisms and empty schemes, since it uses only units,
composition coherence, and pullback universal properties.


## Second reading by B2

1. Compared the delivered module against the repository version. The existing
theorem signature is byte-for-byte identical, and its docstring is unchanged.
No definitions or public imports changed; the only removed import is redundant
through the public import chain. Verdict: pass.
2. Compiled the complete module locally with lcompile.py. Read every private
helper and the target proof: no sorry, forbidden declaration, or hollow
definition is present. A scratch #print axioms check of the target reports exactly propext,
Classical.choice, and Quot.sound; the delivery axiom probe also checks every
added declaration.
The chosen composition comparison comes from an already proved theorem whose
fixed-sheaf uniqueness clause determines it; no arbitrary unproved witness is
used. Verdict: pass.
3. No statements were split off and no new public statements or nodes were added.
Equality-transport helpers use equality induction, cancellation uses actual
isomorphisms, and the square helper is a strict consequence of composition
associativity. Identity morphisms and empty schemes require no extra hypotheses.
Verdict: pass.
4. Read the proof from the target downward and searched the library for comparison
composition and unit lemmas. The existing comparison_unit only handles sections
coming from the original sheaf, whereas this argument must handle an arbitrary
section of h inverse image; it does not replace comparison_assoc. The proof uses
the stated composition-units dependency and pullback coherence directly. Both old
proof dependencies remain used. The unit sk-thm-iff realized statement and step
remain unchanged; this subsidiary calculation bypasses no unit step. Verdict: pass.
5. Compared the node diff and read proof, proof_deps, and proof_origin against the
Lean calculation. They record the two pullback lifts, composition associativity,
transport, and cancellation accurately; other node fields are unchanged. No new
node requirements apply. Verdict: pass.

Second reading changed only this report: documented the redundant import removal
and recorded the independent review. No proof repair was needed.
