## What changed

Closed `Derivation.exists_fraction_field_derivation_of_not_pth_power` by transferring
characteristic `p` to the fraction field, applying the Kähler differential
zero criterion, and invoking the split differential-to-derivation theorem.
The upper theorem already used the fraction-field and denominator-clearing declarations; its proof is unchanged. Added Sheaf.RingTheory.Derivation.NonzeroDifferentialToDerivation with a named linear-functional obligation, and added Mathlib.Algebra.CharP.Algebra as a proof-only import. Removed the added file-level linter option and used the preferred `let` instance bindings in the fraction-field proof.

## Proved and sorry left

Decomposed: Derivation.exists_fraction_field_derivation_of_not_pth_power; one existing hole is replaced by one strictly smaller named hole. Derivation.exists_apply_ne_zero_of_not_pth_power was already proved from the two substeps and is unchanged.

Sorry left: `Derivation.exists_domain_derivation_of_fraction_derivation` (node
`lem-weil-pbc-domain-derivation-from-fraction`) and
`exists_derivation_of_nonzero_kahler_differential` (node
`lem-weil-pbc-nonzero-differential-to-derivation`). The latter is the one new
split-off hole; it is a strict linear-functional substep, not a restatement of
the target.

## No longer needed

Removed the nine unused direct Sheaf imports listed in this delivery. Added direct proof-only imports Mathlib.Algebra.Algebra.ZMod and Mathlib.Algebra.Field.ZMod for the prime-field structures.

- `Sheaf.FieldTheory.ExistsPBasis`
- `Sheaf.FieldTheory.IntersectionSubfieldsDifferentials`
- `Sheaf.Paper.DerivationExtendsFiniteType`
- `Sheaf.RingTheory.CohenRing`
- `Sheaf.RingTheory.CompleteLocalDomainFiniteOverRegular`
- `Sheaf.RingTheory.CompleteLocalQuotient`
- `Sheaf.RingTheory.NoetherNormalizationOverDomain`
- `Sheaf.RingTheory.PowerSeriesFieldCohenRegularComplete`
- `Sheaf.RingTheory.PowerSeriesRingSubfields`

## Where the brief, the DAG or earlier work was wrong

The fraction-field dependency record omitted the differential-zero criterion, and unused imports remained. This delivery corrects those records and prunes those imports. No existing import changes visibility.

## Second reading by K3

1. Existing declarations were compared with the repository version. All existing theorem signatures and visibility are byte-for-byte unchanged; only proof-only imports, proofs, and the new split module were added. Verdict: pass.
2. Both delivered modules compile with `lcompile.py --all`. The only remaining `sorry`s are the two named split theorems (`Derivation.exists_domain_derivation_of_fraction_derivation` and `exists_derivation_of_nonzero_kahler_differential`); no forbidden declaration form or hollow definition was introduced. Verdict: pass.
3. The new differential-to-derivation theorem is a strict intermediate statement: it removes the finite-type, complete-local, and fraction-field hypotheses and supplies only the linear-functional conversion needed by the fraction-field proof. Its source, docstring, and DAG node agree, and no duplicate declaration was found. Verdict: pass.
4. The fraction-field proof uses the characteristic-p differential criterion and the new conversion theorem; the upper proof still uses denominator clearing. The nine unused Sheaf imports were removed, while the needed characteristic and ZMod imports are proof-only. Verdict: pass.
5. The characteristic-p edge case has the required orientation: zero differential yields a pth root, contradicting the hypothesis. The unit route remains represented by the original target and its fraction-field/domain substeps. Verdict: pass.

Changed in this second reading: normalized this report section to the required heading and recorded the checks above. No Lean proof or statement changes were needed.

## New nodes

`lem-weil-pbc-nonzero-differential-to-derivation` is the strict intermediate
Kähler-differential-to-derivation statement used by the fraction-field proof;
its declaration is in `lean/Sheaf/RingTheory/Derivation/NonzeroDifferentialToDerivation.lean`
and its node is under `dag/nodes/sec-proper-base-change/`. No existing import changes visibility; no change record is needed for these added proof-only imports.
