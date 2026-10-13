## What changed

Proved `polynomial_chart_stalk_flat_comparison_forward`. The proof uses the existing
flat-locus theorem for affine finitely presented morphisms, constructs the flat open
neighbourhood containing the chart point, pulls it back to the residue-field fibre,
and transports flatness through the canonical stalk isomorphisms. Added the proof-only
import `Sheaf.RingTheory.OpenFlatLocus`.

## Proved and sorry left

Closed the sorry in `AlgebraicGeometry.polynomial_chart_stalk_flat_comparison_forward`.
No sorry remains in the delivered module. No new sorry declarations were added.
This is a proof from existing library declarations, including
`Module.isOpen_setOf_flat_localizedModule`, rather than a new decomposition.
The three private helpers are completely proved. The single-file compile and
axiom/direct-sorry probe passed in the delivery dry run.

## No longer needed

The planned dependency `lem-weil-pbc-criterion-flatness-fibre` is not needed for the
forward implication; it is used by the reverse direction. Its module `Sheaf.RingTheory.FlatOfFlatClosedFiber` is not imported by this
forward proof. No existing import was removed: the original three public imports
are retained for the unchanged statement. No other planned nodes or modules are
pruned; no claim is made that the criterion is globally unreachable.

## Where the brief, the DAG or earlier work was wrong

The original proof plan assigned the fibre flatness criterion to this forward direction.
Forward flatness follows directly from openness of the flat locus and base change; the
criterion is needed only for the converse.

`lem-weil-pbc-openness-of-flatness` is used as a tool from another unit: its existing
statement supplies openness for a finitely presented algebra and its self-module.
The present unit has no equivalent openness declaration. The normal-form unit
route is preserved, and its realized lists do not assign this helper to a fixed step.
The Spec/affine openness helpers adapt the already proved private helpers in
`Sheaf.AlgebraicGeometry.AffineFibreCohenMacaulayLocus` without importing that
downstream module (which would cause a cycle).

Edge cases remain covered: n may be zero, the base is arbitrary, and the flat
locus need not be all of U. The selected point supplies membership in the flat
locus; no Noetherian hypothesis or global flatness of e is assumed. All original
public signatures and docstrings are unchanged.

## Second reading by K3

1. **Statements and visibility.** Compared the delivered module against the repository version. The public theorem signature and docstring are byte-for-byte unchanged; the only import addition is the proof-only `Sheaf.RingTheory.OpenFlatLocus`. No public declaration or definition was altered.

2. **Proof and axioms.** Compiled the module with `lcompile.py`; it succeeds without warnings. The proof contains no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or hollow definition. The argument uses the flat-locus theorem, affine transport, pullback stability, and stalk isomorphisms, and preserves the stated hypotheses and conclusion.

3. **Split-off statements.** No declarations were split off and no new nodes or sorry holes were added. The existing theorem is proved directly from library declarations; its edge cases (including `n = 0` and arbitrary base) are covered by the quantified proof.

4. **Pruning and imports.** The proof-only openness import is required by `Module.isOpen_setOf_flat_localizedModule`; all three public imports remain required for the statement and chart constructions. The reverse-direction fibre criterion is not used. The node's `proof` and `proof_deps` agree with the implemented route, and the unit route remains unchanged.

5. **Truth and strength.** The open locus is defined exactly by stalk flatness, and pullback cancellation transports that flatness to the canonical fibre stalk map. The final compositions use only stalk-map isomorphisms and bijective flat maps, so the original theorem is established at its full strength.

I changed only this report section; no Lean source or DAG node required repair.
