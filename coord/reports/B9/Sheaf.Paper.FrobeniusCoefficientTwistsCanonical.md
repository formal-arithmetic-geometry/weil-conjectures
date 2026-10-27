## What changed

Replaced both positive-family holes in
`Sheaf.Paper.FrobeniusCoefficientTwistsCanonical` by coefficient-unit normalization,
degree-one root transport, tensor-power induction, and uniqueness through the module
adjunction and root-generator extensionality. Original public signatures, definition
bodies, attributes and public imports are preserved. Prime invertibility on the
schemes has not been added.

Added `FrobeniusPositivePowerTransport`, a proved generic extension from a first-module
comparison to nonnegative tensor powers, with unit and pure-tensor formulas. Added
four strictly smaller root-line obligations, each in its own module.

Extracted the already proved generic signed/internal-Hom argument, generic tower
augmentation helpers (including its quasi-isomorphism proof), and normalized
localization descent into
`FrobeniusSignedPowerTransport`, `FrobeniusAugmentationGeneric`, and
`FrobeniusNormalizedDescent`. Their proofs are retained. The original item took
69.4 seconds before its holes were changed; these extractions separate generic
proof checking from the coefficient-specific and derived constructions. Local
transparency attributes keep large definitions folded. The finite normalization
proof restores the usual transparency of `constantSheaf` only in its own section.
The common-stage comparison uses the established stage-category cache pattern
from `CommonStageTensorRightUnitorNaturality`, with locally reducible category
projections. In the section containing only `commonDerivedLineMap`,
`ScalarLocalization.category` stays folded. This removes the repeated conversion
of the entire choice predicate without changing any public definition body.
These settings and attributes are not exported.

All added imports of the item are private proof imports. The old direct private
imports of `CartesianCoefficientTwists` and `PurInverseImageHomComparison` moved to
the extracted signed helper. `SfDerivedCompleteLegacyComparison` moved to the
augmentation helper, where its sole use now lives. No other existing
module is modified.

Validation: `lcompile.py --all` accepted all nine delivery modules in import order.
The augmentation helper passed again after import cleanup. Profiling the final
local scalar-category setting reduced the common-stage comparison from about
10.5 seconds to 0.14 seconds; the whole item typechecked in 45.7 seconds.
Diagnostic commands and profiling options have been removed for delivery.
The item has zero holes; the four split statements are the only holes in the packet.

## Proved and sorry left

This is a decomposition of two original holes into four smaller obligations. The
item itself contains zero `sorry`.

Closed original holes:

- `WeilConjectures.FrobeniusCoefficientTwists.existsUnique_positiveLineMaps`.
- `WeilConjectures.FrobeniusCoefficientTwists.existsUnique_finitePositiveLineMaps`.

New proved generic power theorem:

- `WeilConjectures.frobeniusPositivePowerTransport`.

Existing proved arguments extracted without adding holes:

- `WeilConjectures.FrobeniusCoefficientTwists.genericSignedProof`.
- `WeilConjectures.FrobeniusCoefficientTwists.augmentationCocone_ext`, with the
  private exact-functor and augmentation-isomorphism proof helpers.
- `WeilConjectures.FrobeniusCoefficientTwists.normalized_descent`.

Four added holes, each exactly the whole proof of a named public theorem:

- `WeilConjectures.frobeniusIntegralRootTransport`
  (`lem-weil-frobenius-integral-root-transport`).
- `WeilConjectures.frobeniusFiniteRootTransport`
  (`lem-weil-frobenius-finite-root-transport`).
- `WeilConjectures.integralRootPower_hom_ext`
  (`lem-weil-integral-root-power-generators`).
- `WeilConjectures.finiteRootPower_hom_ext`
  (`lem-weil-finite-root-power-generators`).

The first pair concerns only degree one and asserts neither higher powers nor
uniqueness. The second pair gives extensionality into an arbitrary module, with no
pullback or comparison family. The new induction and original theorems combine
these different parts by real Lean proofs.

## No longer needed

Removed the item's direct private imports of `CartesianCoefficientTwists`,
`PurInverseImageHomComparison`, and `SfDerivedCompleteLegacyComparison`; they remain
dependencies of the extracted signed and augmentation arguments. The augmentation
helper also avoids the unused triangulation import. No original DAG dependency or library module is withdrawn. Original proof
dependencies remain needed by the retained signed, augmentation, derived and Weil
constructions. No declaration of the adopted source library was changed or removed.

The power proof uses the canonical ordinary tensor pullback theorem. It does not
use the stronger local-freeness/prime-invertibility hypotheses of the existing
normalized signed-line existence theorem; that module supplies only its proved
pullback-of-unit normalization helper.

## Where the brief, the DAG or earlier work was wrong

The original module exceeds the 60-second limit before these changes. Profiling
shows costly choice-predicate conversion and substantial kernel checking of generic
proofs. The final approach preserves public definition bodies and extracts only
private generic proof code. The item has 23 direct importers; a compatibility check
of the first, `ConstantPurityFrobeniusSquare`, took 92 seconds. That importer does
not mention the definition considered for a proof-only normalization refactor.
The refactor was discarded, so the delivery changes no public definition or import
and does not adapt that importer.

The assigned statements cover arbitrary scheme isomorphisms, without requiring
prime invertibility. Existing root-line APIs assuming invertibility do not directly
fit. The four obligations preserve the original generality. Edge-case review covers
zero and one powers, arbitrary positive quotient exponent, ramification, vanishing
root groups, and the empty scheme. The finite first module is the recorded
change-of-rings sheafification of the integral root-limit tensor. Its generators
are therefore the root-limit generators used here. Generation is local after
sheafification; arbitrary sheaf sections need not globally lift to the tensor
presheaf.

The current blueprint file is in `sec-six-functors-basics`, while the imported DAG
node retains chapter `sec-smooth-purity`. Sources distinguish the current blueprint's
natural Weil isomorphism sentence from expanded DAG clauses 2 and 3.

A raw traversal of the shared DAG finds a pre-existing cycle from this node through
`lem-pur-derived-pullback-tensor-iso`, the operation/reduction/compact-support
records, `def-pur-integral-compact-support-coefficient-data`, and
`def-pur-conventions` back to this node. It is present before this delivery. The
Lean imports used here have no cycle. Those other nodes are unchanged.

## New nodes

`lem-weil-frobenius-integral-root-transport` records transport of the first completed
line, normalized on every completed scalar/root tensor.

`lem-weil-frobenius-finite-root-transport` records its ordinary finite scalar
extension, normalized on the recorded finite generators.

`lem-weil-integral-root-power-generators` gives arbitrary-target extensionality from
integral scalar/root generators, passing the actual generator family with its
recursion equations.

`lem-weil-finite-root-power-generators` gives the finite version.

`lem-weil-frobenius-positive-power-transport` records the proved tensor induction,
including degree zero, degree one, and the binary tensor formula.

`lem-weil-frobenius-signed-power-transport` records the extracted signed/internal-Hom
proof with its slice evaluation normalization.

`lem-weil-frobenius-augmentation-cocone-ext` records the extracted mapping-cocone
coordinate argument. Its module also preserves the private generic tower
augmentation constructions used by the item.

`lem-weil-frobenius-normalized-localization-descent` records the extracted descent
proof. No change record is needed: public interfaces and definition bodies of all
existing modules are unchanged.

## Second reading by B9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
