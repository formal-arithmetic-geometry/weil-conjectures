## What changed

Replaced the proof hole of `WeilConjectures.compactSupportSystemNormalizedPresentation`
without changing its statement. The proof constructs all operation instances, uses the
existing normalized open-section presentation, and assembles the ten required clauses.
The ordinary open comparison is proved in the new
`Sheaf.TraceFormula.CompactSupportOpenOrdinaryMate` module. Exact localization of its
inverse mate gives the specified canonical derived left comparison, and the general
mate unit and counit equations give both open normalization formulas.

The finite-coefficient comparison and the system direct-image evaluation specialization
are separated into two independent statements in new modules. Neither includes the open
immersion or the full presentation data. All new proof imports are private imports;
the original public import is unchanged. No existing definition, statement, attribute,
instance, source-library module, or consumer is changed.

Validation: all four sandbox modules compiled through `lcompile.py`; the final main
module compiled without warnings in 27.9 seconds. Its statement was checked verbatim
against the repository original. New node Lean statements match their declarations,
all dependency IDs exist, and no profiling options or overlong Lean lines remain.

## Proved and sorry left

The original module had one hole, in
`WeilConjectures.compactSupportSystemNormalizedPresentation`. Its proof is now complete
from the two named intermediate statements and the existing library results. This is a
decomposition, not a completed proof of the mathematical obligation: one original hole
is closed and two holes are added.

`WeilConjectures.compactSupportOpenOrdinaryMate` has a complete proof. The private
K-injective instance and derived open-normalization helpers have complete proofs.

The two remaining holes are exactly:

- `WeilConjectures.compactSupportFiniteCoefficientPresentation`, node
  `lem-trf-compact-support-finite-coefficient-presentation`: finite levels only,
  coefficient restriction against direct image, including its resolution normalization.
- `WeilConjectures.compactSupportDirectImageEvaluation`, node
  `lem-trf-compact-support-direct-image-evaluation`: strict-system direct-image
  evaluation, its arbitrary-resolution normalization, and its adjunction mate equations.

Each remaining proof is exactly `by sorry`, in a public named theorem with its source
and complete proof in words. No definition contains a hole.

## No longer needed

The new ordinary-open module imports only
`Sheaf.SixFunctors.IntegralOpenReductionDefinitions`, removing its provisional broader
import of the full compact-support diagram.

No original import was removed: the original file imported only the data module, which
its statement still needs. No module or declaration is withdrawn, and no global pruning
is claimed. The parent proof no longer directly applies the full geometric semilinear
calculus: the open part uses the already constructed normalized open presentation and
the explicit ordinary mate proof. The actual finite coefficient and direct-image
specializations remain needed and are stated separately; their nodes retain the general
semilinear and constant-coefficient dependencies of those steps.

The original direct proof dependencies have the following disposition:

- `def-coef-ringed-sequence-site` (`Sheaf.Paper.CoefficientRingedSequenceSite`)
  remains a statement dependency and is needed by the new direct-image step.
- `lem-coef-semilinear-derived-sections` (`Sheaf.Paper.SemilinearDerivedSections`)
  remains needed by the existing normalized open construction and the two new plans.
- `def-weil-proetale-inverse-image` (`Sheaf.AlgebraicGeometry.ProEtaleInverseImage`)
  and `prop-weil-pbc-proetale-constant-ring-map`
  (`Sheaf.AlgebraicGeometry.ProEtaleConstantRingMap`) remain in the new specialization
  plans; they are not globally obsolete.
- `lem-weil-proetale-weakly-etale-localization`
  (`Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization`) is already used by the
  existing open coefficient transport, instead of being specialized again here.
- `lem-pur-site-restriction-module-adjunction-exact`
  (`Sheaf.CategoryTheory.LocalizedModuleExactForSystems`) supplies the actual localized
  adjunction used in the ordinary open mate. Its work remains necessary.

The unit route and the target signatures are preserved.

## Where the brief, the DAG or earlier work was wrong

The parent node described specialization of a general semilinear calculus, rather than
an immediately applicable declaration with the actual pro-etale coefficient functors.
Existing completed direct-image evaluation presentations use a single shared universe;
this item retains independent scheme and coefficient universes. A direct application
therefore does not close the actual finite-coefficient or system comparison. Those two
separate specializations remain as the explicitly stated obligations above.

The open part does have a shorter route: `normalizedOpenSections` and
`openCoefficientOperationsExistence` construct its normalized data already. The ordinary
unit equation identifies the inverse mate, the equivalence adjunctions make its pasted
right square invertible, and exact localization preserves it. There is no statement
correction. The K-injective existence theorem is used as an already proved tool from
`prop-pur-kinjective-resolutions-exist`, to construct actual operation instances.

## New nodes

`lem-trf-compact-support-finite-coefficient-presentation` separates the finite quotient
restriction/direct-image square from every system and open operation. The ordinary
comparison is forced by the identity on sections; the derived one is normalized on
arbitrary restricted K-injective resolutions, including identity quotient indices.

`lem-trf-compact-support-direct-image-evaluation` separates evaluation of the actual
system direct-image adjunction. Its comparisons are normalized on ordinary sections,
arbitrary evaluated resolutions, units and counits; it asserts no coefficient-transition
comparison and no open operation. Empty schemes and level zero are included.

`lem-trf-compact-support-open-ordinary-mate` is proved, not left as a new obligation.
It gives one ordinary evaluation square and its inverse-mate identification, using the
existing open-slice unit identity and the horizontal-pasting law for mates.

All three nodes serve Step 1 (Global powers) of the current blueprint's
`thm-trf-l-function-euler-product` through the existing coherence/presentation chain.
Blueprint searches for coefficient restriction/direct image, evaluation/adjunction,
and open/mates found no duplicate exact statement. Mathlib searches used LeanSearch,
LeanFinder, Loogle and grep; they found general mate and derived-adjunction lemmas,
which are used where applicable, but no complete actual-functor specialization.
There are no change records because no existing interface or other module was changed.

## Second reading by E6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
