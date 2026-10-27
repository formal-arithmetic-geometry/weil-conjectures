## What changed

Restored the quarantined item from its recorded archive, preserving every declaration
signature, definition body, existing public import, and its theorem attachment. Added a private proof
import and a public import reexporting the unchanged normalization definitions and replaced `kummer_strict_target_transport`'s proof by assembly of a
residue-linear lifting theorem and strict Kummer adjunct compatibility. The assembly
uses the same target data for every level and arbitrary source; it obtains a residue
class, applies compatibility to that class, and pairs the two equations.

Added `Sheaf.Paper.DiagonalFiniteArrowLift` and
`Sheaf.Paper.KummerStrictAdjunctCompatibility`, one public theorem per module, with
source citations and full natural-language proof plans. Updated the item's proof DAG
and added their two nodes. No other existing module or target statement changed. Moved `kummerComparedUnit`
and `kummerRootNormalization` verbatim into the new compatibility module and
publicly reexported them from the item. Sharing those concrete normalization terms
avoids the repeated unfolding that made the final file exceed 60 seconds. The new predicates and concrete proposition aliases name the
displayed formulas over shared category parameters, and a proved private generic
assembly lemma combines them before concrete specialization. This avoids repeatedly
elaborating the large concrete sheaf coefficient constructions; it changes no formula
and chooses no mathematical data.

Validation: `lcompile.py --all` accepted all three delivered modules with the
60-second gate, then accepted the four unchanged direct importers:
`DiagonalCartierAdjunctUniqueness`, `KummerSheafPredicates`,
`KummerTransportAssembly`, and `DiagonalFiniteCartierNormalization`.
Their verification-only copies were removed. No downstream adaptation was needed.
All profiling and trace options were removed before these checks.

## Proved and sorry left

Closed the original textual hole in
`AlgebraicGeometry.ProEtale.kummer_strict_target_transport`
(`lem-sfb-kummer-strict-target-transport`) by a complete proof from the two new
statements. This is a decomposition, not a completed mathematical proof: one hole
closed and two holes added, net minus one.

The only remaining holes in the delivery are:

- `AlgebraicGeometry.ProEtale.diagonal_finite_arrow_lift`
  (`lem-sfb-diagonal-finite-arrow-lift`): existence of a residue-linear lift of
  evaluated derived-reduction arrows, for arbitrary endpoints and arbitrary prescribed
  pure source/target identifications. It has no Kummer or roots assumptions.
- `AlgebraicGeometry.ProEtale.kummer_strict_adjunct_compatibility`
  (`lem-sfb-kummer-strict-adjunct-compatibility`): construct the strict roots target
  and compute the adjunct of any supplied residue lift. It does not assert the
  existence of a residue lift.

These are distinct parts of the argument: the first factors evaluated derived
reduction through residue coefficients, whereas the second computes its Kummer
normalization. Neither asserts the original existence of a residue class satisfying
both equations. There are zero `sorry`s in the item itself and two across the delivery.
No objects are defined by choosing arbitrary witnesses of an unproved existence claim.

## No longer needed

No existing import, declaration, module, node attachment, or unit route is withdrawn.
The original eleven proof dependencies are no longer used directly by the item's
assembly: `def-sfb-geo-cartier-interface`, `lem-sfb-canonical-sheaf-ext`,
`lem-pc-kflat-resolution`, `lem-amb-kummer-any-base`,
`lem-sp-cartier-reduction-site-comparison`, `lem-pur-constant-two-term-resolution`,
`lem-weil-pbc-site-module-sheaf-constant-ring-equivalence`,
`def-pur-roots-of-unity-sheaf`, `def-kun-truncations`,
`def-sfb-diagonal-system-interface`, and
`lem-sfb-divisible-extension-derived-reduction`.
They remain needed as statement dependencies or below the two new nodes; none is
claimed globally pruned. The existing public `CanonicalSheafExt` import stays. The compatibility import is
public because it now supplies the two normalization definitions, under their
unchanged fully qualified names. No declaration has been withdrawn.
The new modules import only the coefficient/interface module their signatures need.

## Where the brief, the DAG or earlier work was wrong

The original plan hides the comparison between strict-system evaluation and derived
extension to a finite residue ring. The existing divisible-extension theorem is for
one exponent and internal module sheaves; its statement alone does not identify the
arbitrary `DiagonalDerivedReduction` evaluation. The new finite-arrow node makes
this comparison obligation explicit and separates it from Kummer normalization.

The item and its coefficient interface were initially quarantined; the rework row
was read before restoration. Their sources became available in the live tree during
this session. The archived source was preserved, and no deletion or withdrawal was
attempted. The unit's target, transition calculation, and naturality route stay intact.

Edge cases were checked in the statements and proof plans: the empty scheme and zero
source/target give zero Ext classes; level zero is exponent one, never exponent zero;
the lifting lemma needs no invertibility on W; the Kummer lemma retains invertibility;
arbitrary s and t change the lifted arrow by conjugation, and require fullness only on
the hearts, never on all derived morphisms. No equality in the strict derived category
is inferred from levelwise equality.

## New nodes

`lem-sfb-diagonal-finite-arrow-lift` records the finite-residue existence step in
blueprint steps (2) and (4), independently of the Kummer calculation. Its conclusion
is only the restriction equation, with completely arbitrary M,H,P.

`lem-sfb-kummer-strict-adjunct-compatibility` records the strict roots target from
step (3) and the adjunct calculation of step (4) conditional on a supplied residue
lift. The lifting problem is absent from its conclusion. Both nodes inherit
`sk-prop-diagonal-tower` and use the current blueprint source.

Change record: `coord/changes/B6-kummer-normalization-sharing.md`.

## Second reading by B6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
