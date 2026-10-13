## What changed

Reduced `AlgebraicGeometry.Scheme.exists_finite_base_of_power_series_depth_two`
to the comparison over the inverse image of the punctured coefficient spectrum.
The statement and all existing public imports are unchanged. The new proof proves
boundary depth on both finite extensions and extends the open isomorphism by
`iso_of_finite_depth_two_extensions`, then transports the standard pullback square.
Added proof imports of `MvPowerSeries.Equiv`, `FlatLocalDepthFormula`,
`AdicCompletion.AsTensorProduct`, `DepthTwoFiniteExtensionUniqueness`, and
`PowerSeriesPuncturedFiniteModel`. Two private helpers prove depth monotonicity
for a flat stalk map and the closed-point depth estimate.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Scheme.exists_finite_base_of_power_series_depth_two`
(node `lem-sbc-power-series-depth-two-base-change`). No sorry remains in the item's
module. Added one hole:
`AlgebraicGeometry.Scheme.exists_power_series_punctured_finite_model`
(node `lem-sbc-power-series-punctured-finite-model`), in its own new module.
This is a decomposition, not a net reduction in holes: it leaves only an open
comparison and coefficient-model construction. The global comparison, enlarged
boundary-depth estimates, and cartesian-square assembly are proved in Lean.
The new lemma does not assume the original E boundary depth and does not assert
a global isomorphism or cartesian square. Empty covers are allowed.

## No longer needed

No original public imports were removed. The planned dependency
`lem-sbc-mv-power-series-constants-flat`, module `Sheaf.RingTheory.MvPowerSeriesFlat`,
is not needed: five lines transfer Mathlib's flatness of adic completion through
`toAdicCompletionAlgEquiv` and use `Module.Flat.trans`. No replacement declaration
of constants flatness is introduced. This prunes that dependency from this proof;
other users may still need its module. The original node's direct dependency on
`lem-sbc-depth-two-finite-extension` (module
`Sheaf.AlgebraicGeometry.Morphisms.DepthTwoFiniteExtension`) moves to the
punctured-model node; it remains needed transitively and is not pruned globally.
No global removal from the targets closure is claimed.

## Where the brief, the DAG or earlier work was wrong

The original DAG's single step used power-series full faithfulness (Tag 0EY9)
but named no declaration for it; the three recorded dependencies alone do not
supply the punctured comparison. The new node isolates precisely this gap with
the coefficient-model construction from Tag 0EYA. The proof also has to enlarge
the supplied E boundary depth from T minus V to T minus W; etaleness on V and
the flat local depth formula supply the additional points. The unit route is
preserved. No statement is disputed or changed. The flat-constants source module
was initially absent from the last green compiled snapshot. The final shorter
route uses Mathlib instances and linear equivalence directly, without importing
that module or adding any constants-flatness declaration. Both delivered modules
compile through lcompile.py (about four seconds each).

## New nodes

`lem-sbc-power-series-punctured-finite-model`, module
`Sheaf.AlgebraicGeometry.Morphisms.PowerSeriesPuncturedFiniteModel`, states the
finite coefficient model and comparison only over W = t inverse U. Its source
is Tag 0EYA before the construction of Psi, using Tags 0EY9 and 0EY6. Blueprint
searches for 0EY9 and punctured power series found no matching imported node.
There are no change records because no existing interface changed.

## Second reading by A4

1. **Interface and unchanged statements.** Compared both delivered modules with the repository versions. The existing target declaration and all pre-existing declarations have byte-for-byte identical signatures; the added declaration is recorded by its new node. No target definition or hypothesis was changed. Verdict: pass.

2. **Proof and allowed axioms.** Compiled both modules with `lcompile.py --all`; both compile cleanly. The target has no `sorry`, and the only remaining `sorry` is the named split-off theorem `exists_power_series_punctured_finite_model`, with its source, natural-language proof, and matching DAG node. The split theorem is public, contains no hollow definition, and introduces no forbidden declaration. Verdict: pass, with the split-off theorem intentionally still open.

3. **Truth and strength of the split statement.** Checked the punctured-model statement against the target reduction: it assumes exactly the local depth, proper open, away-from-closed-point condition, finite cover and etaleness on that open, and concludes only a finite coefficient model, boundary depth, and comparison over the punctured coefficient inverse image. It asserts neither a global comparison nor etaleness of the coefficient model, so it is strictly weaker than the target and is sufficient for the remaining proof. Empty covers are covered by the stated construction. Verdict: pass.

4. **Shortest route and pruning.** The target proof uses Mathlib's adic-completion linear equivalence and flatness directly, then the existing depth formula and finite extension uniqueness. The unused planned constants-flatness module was removed from the proof imports and is recorded under “No longer needed”; no other import was removed. The proof-dependency fields and proof steps in both DAG nodes match the declarations actually used. Verdict: pass.

5. **Unit route and changes.** The realized unit route is preserved: the new node isolates the punctured comparison step and the target assembles it with the finite depth-two extension and uniqueness steps. No existing interface change or change record is required. Verdict: pass.

I changed only this report section after the first delivery check; no Lean code or DAG statement was altered.
