## What changed

The statement of `finiteFixedRefinementOpenIso_normalization` is unchanged. Its proof
first normalizes the fixed-scalar proper/open comparison at the retained etale
antecedent, conjugates by `fixedOriginWitness`, and transfers the resulting identity
through the finite-coordinate restriction equation. Cancellation of the two open
units gives precisely the original conclusion.

`Sheaf.Paper.ProEtaleProperOpenUnitNormalization` constructs `properOpenRestriction`
as the inverse-image compositor followed by restriction of the derived proper
counit, and proves `properOpenProEtaleIso_unit`. Its proof establishes the etale
normalization from `properOpenIdentification_unit`, transports the equation through
the three normalized site-comparison squares, and proves compatibility with the
bounded-below inclusion. All categorical pasting and conjugation helpers are proved.

`Sheaf.Paper.FiniteRingOpenRestrictionCoordinates` isolates the remaining scalar
coordinate calculation for an arbitrary morphism. It does not assert that any
specified proper/open comparison has the required normalization: the site comparison,
retained-origin conjugation, and final cancellation are carried out in this packet.
The new imports of the item are private proof imports. No existing public interface,
source-library declaration, or target changes.

Validation: all three modules compile in import order through `lcompile.py --all`: 
26.9 s for the pro-etale normalization, 7.8 s for the coordinate statement, and
10.5 s for the item. No compiler warnings remain.

## Proved and sorry left

The original hole `WeilConjectures.ConstructibleExceptionalCoefficients.finiteFixedRefinementOpenIso_normalization` is closed by a complete proof from the
coordinate lemma. This is a decomposition, not a net hole reduction: one original
hole is closed and one new hole is added.

`AlgebraicGeometry.ProEtale.properOpenProEtaleIso_unit` is proved without adding a
hole. The item's module has zero `sorry` occurrences.

The delivery leaves exactly one new `sorry`:
`WeilConjectures.ConstructibleExceptionalCoefficients.finiteOpenRestriction_endomorphism_coordinates`, attached to
`lem-sf-finite-ring-open-restriction-coordinates`. It is only the finite-scalar
transport step: its arbitrary input morphism need not have any normalization,
and it has no etale antecedent or canonical proper/open comparison. Its docstring
specifies the unit, counit, and section-normalized compositor calculations still
needed. No definition or private helper contains `sorry`.

## No longer needed

The original planned dependency `lem-cbc-proper-open-derived-unit-normalization`
(`Sheaf.AlgebraicGeometry.ProperOpenDerivedUnitNormalization`) is not used by this
argument. The already proved `properOpenIdentification_unit` supplies the actual
etale normalization, and exact inclusion compatibility is proved here. No import
of that module was added. No existing import was removed from the item's original
file, and no module is withdrawn.

Other original dependencies still occur through the new subargument or the
remaining coordinate lemma; they are not claimed as globally pruned. In particular,
the intrinsic adjunction, open-square, and finite pullback compositor dependencies
remain relevant to the scalar-coordinate step. The unit's realized route is preserved.

## Where the brief, the DAG or earlier work was wrong

No statement defect was found. The DAG's first step named an additional derived
normalization obligation, but the normalized bounded-below restriction is already
proved by `properOpenIdentification_unit`. Its transfer to the pro-etale unbounded
map requires separate unit, counit, and composition compatibility calculations;
these are now explicit Lean proofs. Empty opens, identities, and zero objects use
the same adjunction equations, so no geometric side hypothesis was added.

## New nodes

`lem-sf-proetale-proper-open-unit-normalization` records the constructed restriction
and the proved normalization before finite or intrinsic realization. Its module is
`Sheaf.Paper.ProEtaleProperOpenUnitNormalization`.

`lem-sf-finite-ring-open-restriction-coordinates` records only the scalar-coordinate
calculation for an arbitrary morphism. Its module is
`Sheaf.Paper.FiniteRingOpenRestrictionCoordinates`. The parent node's proof and
proof dependencies now follow the actual conjugation and cancellation argument.
There are no change records: no existing definition or statement changed.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.FiniteRingFixedOpenNormalization": "82606d4e27b29d16499cfeae189e2cfc30a45c3a", "Sheaf.Paper.FiniteRingOpenRestrictionCoordinates": "4da94f2718696433a4dca1265e7882383f4dc19e", "Sheaf.Paper.ProEtaleProperOpenUnitNormalization": "80abdb66d3d8265a5ced9b95debb1b6e85cb1db3"}, "results": {"Sheaf.Paper.FiniteRingRefinementCoordinatesCore": {"hash": "1b066b8c1de4ce2ce7cd228ed7eb9f2b58ed65d2", "status": "OK"}}, "seconds": 24, "time": "2026-10-28T14:56:39+0800", "transitive": 0, "version": 1}
```

## Second reading by Q2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
