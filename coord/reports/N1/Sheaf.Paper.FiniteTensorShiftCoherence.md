## What changed

Replaced the single `sorry` in
`WeilConjectures.PurityFiniteSetting.finiteTensorShiftCoherence` by the formal assembly
of first- and second-variable tensor-shift squares. Added proof-only imports
`Sheaf.Paper.FiniteTensorShiftFirst` and `Sheaf.Paper.FiniteTensorShiftSecond`.
The two new modules state the individual squares for the existing normalized core,
existing adjunction-induced scalar shift, and native derived tensor shifts.
No existing declaration signature, definition, attribute, or public import changed.
The parent DAG now follows the Lean assembly; each new node records its remaining
representative-normalization argument.

The assembly expands the simultaneous shift and the scalar shift addition law,
cancels the source addition comparison, uses scalar-shift naturality, applies the
second-variable square under the first shift and then the first-variable square,
and finishes using tensor-shift naturality and tensor interchange.

## Proved and sorry left

This is a decomposition, not a net proof gain: one original hole closed and two
strictly smaller holes added (net -1).

Closed:

- `WeilConjectures.PurityFiniteSetting.finiteTensorShiftCoherence`
  (`lem-pur-finite-tensor-shift-coherence`), from the two named one-variable squares.

Added and left:

- `WeilConjectures.PurityFiniteSetting.finiteTensorShiftFirst`
  (`lem-pur-finite-tensor-shift-first`): only the first input shifts.
- `WeilConjectures.PurityFiniteSetting.finiteTensorShiftSecond`
  (`lem-pur-finite-tensor-shift-second`): only the second input shifts.

There are zero textual holes in the assigned module and one in each new module.
The new statements impose no flatness condition on the quotient or boundedness
condition on the inputs. The underlying cochain check is unsigned in the first
variable and has the same (-1)^(np) on both sides in the second. This works for
n=0, n=1, n=-1, zero inputs, empty schemes, and characteristic two. The parent
assembly allows all a,b, including negative and cancelling shifts. The assigned
module compiled cleanly through lcompile.py (31.0 seconds). Both new statement
modules also compiled; their only proof holes are the named statements above.

## No longer needed

No existing imports or modules are withdrawn. The existing public imports remain
needed by the statement and its native monoidal and shift instances.

The following former direct proof dependencies are now delegated to the two new
one-variable nodes, rather than required directly by the formal assembly:
`lem-pc-kflat-resolution`, `lem-pur-kflat-change-of-rings-independent`,
`lem-weil-pbc-site-derived-tensor-descent`,
`lem-sbc-derived-scalar-extension-counit-shift`,
`lem-weil-pbc-cochain-pullback-tensor-shift`, and
`lem-weil-pbc-derived-tensor-shift-descent`. They are still mathematically needed;
this delivery does not claim their pruning.

The old plan's constructibility/Tor-interval detour through
`det-sp-scalar-extension-functor` and `lem-sf-reduction-flat-model` is unnecessary
for this square, which concerns arbitrary ambient derived objects.
`lem-pur-cochain-comparison-monoidal-equations` and
`lem-pur-cochain-pullback-tensor-coherence` are not direct requirements of the
shift argument: the more specific cochain tensor-shift theorem supplies its chain
square. The existing normalized core is used without reconstructing its
associator, unit, and symmetry axioms. These nodes/modules may remain needed by
other declarations and their dependencies; none is withdrawn here.

## Where the brief, the DAG or earlier work was wrong

No statement error was found. The old plan mixed constructibility, line twists,
and associativity/symmetry into an ambient two-input shift equation. Those extra
claims do not help prove this equation. The existing intrinsic-site descent and
counit-shift declarations do not directly identify their data with the particular
fixed-scalar core and adjunction shift in this theorem; that identification is
now explicitly included in each one-variable proof obligation rather than
silently assuming the models definitionally agree.

The new obligations are genuine strict parts: each permits only one shifted
input and neither concludes simultaneous shift coherence. Their combination is
written as Lean proof, using shift addition and naturality.

## New nodes

`lem-pur-finite-tensor-shift-first`, in
`lean/Sheaf/Paper/FiniteTensorShiftFirst.lean`, states the unsigned first-input
square and records the K-flat descent and normalization proof. Its source is
Stacks 07A4 and 0FNH, item-shift-tensor.

`lem-pur-finite-tensor-shift-second`, in
`lean/Sheaf/Paper/FiniteTensorShiftSecond.lean`, states the Koszul-signed
second-input square with the same actual data and sources. Neither new node
changes the unit route. No change record is needed because existing interfaces
and public imports are preserved. Blueprint search for tensor/shift returned no
matching imported node; the new nodes retain the existing purity-transport unit
and point back to its finite-reduction theorem.

## Second reading by N1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
