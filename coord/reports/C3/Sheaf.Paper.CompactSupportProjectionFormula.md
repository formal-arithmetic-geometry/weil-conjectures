## What changed

Proved `WeilConjectures.compactSupportProjectionFormula_coefficients` in
`Sheaf.Paper.CompactSupportProjectionFormula` from the existing generic ordinary
coefficient-change square
`PurCompactSupport.compactSupportProjectionCoefficientChange`.

The proved private helper `projectionChange_of_comp` packages that square with
the two coefficient pullback-composition identities required by
`CompactSupportProjectionChange`. The proved private helper
`finiteProjectionPull_comp` obtains the finite identities from
`proEtaleCoefficientInverseImageMap_comp` and `Iso.ext`. The completed identities
are the existing `PurCompactSupport.completedPull_comp`. The four cases instantiate
these helpers at finite quotient change, completed-to-finite reduction, completed
scalar extension and ramified finite scalar extension, respectively. The ramified
target level remains exactly `e * n` with its published positivity proof.

Added private proof imports `Sheaf.Paper.CompactSupportProjectionCoefficientChange`
and `Sheaf.AlgebraicGeometry.ProEtaleConstantRingComposition`. Updated the main
node's proof, proof dependencies and proof origin for this direct route. All public
signatures, definitions, reducibility attributes and other theorem proofs are
unchanged. There are no consumer adaptations or new declarations visible to importers.

The generic square holds for arbitrary derived inputs, so the original finite-Tor
hypotheses can be retained without additional assumptions. Identity coefficient
changes, equal quotient levels, ramification index one and zero inputs require no
exception: the same canonical square applies in each case.

## Proved and sorry left

Closed one of the six original holes:
`WeilConjectures.compactSupportProjectionFormula_coefficients`.
No holes added and no statements split off.

Five original holes remain, all attached to `fix-prop-projection-formula`:

- `WeilConjectures.CompactSupportWeilProjection.openMate_isIso`.
- `WeilConjectures.CompactSupportWeilProjection.restriction`.
- `WeilConjectures.CompactSupportPbcTransport.bridge_existsUnique`.
- `WeilConjectures.CompactSupportPbcProjection.forward`.
- `WeilConjectures.CompactSupportPbcProjection.tensor_identification`.

The imported ordinary coefficient-square theorem has its existing outstanding
proof in `Sheaf.Paper.CompactSupportProjectionCoefficientChange`, node
`lem-pur-compact-support-projection-coefficient-change`. This delivery uses that
already stated dependency; it introduces no new hole or copy of its statement.

## No longer needed

Removed the redundant private import `Sheaf.Paper.PbcWeilCategory`; it is already
publicly available through `WfTensorCompletionFrobenius` and `WeilTensorProduct`.

For the coefficient theorem, the generic ordinary square removes the need to
reconstruct its four cases separately through the concrete reduction, integral
cone or field-descent statements. Those dependencies remain needed by the
module's stage-law assembly and other outstanding obligations, so no existing
node or module is withdrawn and their existing proof steps are preserved. No
unit-level route is bypassed.

## Where the brief, the DAG or earlier work was wrong

The coefficient theorem's proof plan can be shortened: its required equation is
already exactly the existing ordinary coefficient-square declaration. The two
pullback-composition identities must still be proved, rather than assumed; the
finite and completed composition theorems supply them.

The existing `STATEMENT-DISPUTED` marker at
`CompactSupportPbcTransport.bridge_existsUnique` is preserved. Its normalization
omits the inverse of `pbcActualCompletedPullback_tower`, comparing a strict tower
with reflector completion by heterogeneous equality. This delivery does not
repair that separate statement or use its disputed normalization in the new proof.

The attachment of `lem-fix-weil-operations` supplies the etale mixed-support cup
pairing result rather than the literal rational `component` equivariance equation.
The remaining restriction proof therefore still needs the coefficient and
adjunction comparisons described in its docstring.

## Second reading by C3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
