## What changed

Filled the seven proof bodies in `Sheaf.Paper.SfPackageCoefficientDomains`, preserving every
existing statement and definition. All seven Lean signatures were compared verbatim
after whitespace normalization and are unchanged. The finite-domain conjunction uses `finiteTor_stability`;
finite quotient Hom uses `finiteCoefficient_derivedHom_change`. Integral domains and both
field Hom predicates use the existing integral-preservation and integral-Hom theorems.
Direct-image preservation also follows from the operation datum's constructible-valued
functor and its specified comparison to the ambient direct image. Field values use the
published unique-construction object formulas, localized evaluation, unary descent, and the
operation datum's normalized support constructions. Common-stage descent uses the existing
scalar-compatible SF/PBC comparison and transport theorem. Its auxiliary identity families
include explicit shift compatibility.

The single finite site-perfect evaluation comparison is isolated in the new module
`Sheaf.Paper.FiniteSitePerfectEvaluation`. This is only the evaluation component of the
finite-domain theorem, with arbitrary derived target; it does not restate the conjunction
of operation preservation, Hom bounds, and direct images. The existing site-perfect theorem
uses `SixFunctorDatum`, its chosen closed structures and restricted finite-Tor objects;
our item assumes only `SixFunctorOperationDatum` and asks about the independently fixed
intrinsic ambient closed structure. That presentation comparison is the remaining step.

Validation: the final item module compiled cleanly through `lcompile.py` in 21.9 seconds;
the new evaluation module compiled earlier in 54.2 seconds.

All added imports are proof imports. No source-library module, target signature, or public
import was changed. Updated the existing node's proof and dependency list to the actual
Lean argument. The extra coefficient-category comparison is obtained by eliminating an
existence theorem within a proof; no new data definition chooses a witness.

## Proved and sorry left

Closed the original seven holes, by name:

- `WeilConjectures.sfPackageFiniteDomains`: reduced to existing stability and the one new
  intrinsic evaluation obligation; this part is a decomposition, not a completed proof of
  perfect evaluation.
- `WeilConjectures.sfPackageFiniteHomReduction`: proved from finite coefficient Hom change.
- `WeilConjectures.sfPackageIntegralDomains`: proved from integral preservation, the operation
  datum, compact-support constructibility, and integral Hom stability.
- `WeilConjectures.sfPackageFieldHomDomains`: proved from integral Hom stability on the actual
  integral representatives, including representatives at the compositum.
- `WeilConjectures.sfPackageFieldValues`: proved from the actual construction and descent APIs.
- `WeilConjectures.sfPackageScalarExtensionExact`: proved from exact intrinsic scalar extension.
- `WeilConjectures.sfPackageCommonStageDomains`: proved from coefficient comparison and transport.

Zero `sorry` remain in the item module. One hole is added:
`WeilConjectures.finiteIntrinsic_sitePerfect_evaluation_isIso`, node
`lem-sf-finite-intrinsic-site-perfect-evaluation`, in the new module
`Sheaf.Paper.FiniteSitePerfectEvaluation`. Its proof is a named public theorem with source
and complete proof plan. Thus the packet closes seven holes and adds one; the raw net is six.
All reused theorems retain their existing proof status; this is not a claim that the targets
are axiom-free already.

## No longer needed

Removed these direct proof imports and direct proof dependencies:

- `Sheaf.Paper.FiniteConstructibleHom` / `cor-weil-finite-constructible-hom`: already assembled
  in the Hom conjunct of `finiteTor_stability`.
- `Sheaf.Paper.SitePerfectDualizableHom` / `prop-sf-dualizable-hom`: its `SixFunctorDatum`
  presentation does not directly match the intrinsic ambient comparison; the smaller
  presentation-specific evaluation obligation replaces this direct use.
- `Sheaf.Paper.SfIntegralDirectImageConstructible` /
  `lem-sf-integral-direct-image-constructible`: the operation datum's specified direct-image
  isomorphism transports membership from its constructible-valued functor.
- `Sheaf.Paper.IntegralResidueTor` / `lem-coef-integral-residue-tor`: already assembled in
  `finiteTor_stability_integral_hom`.

Also removed `cor-coef-integral-internal-hom` as a direct proof dependency because the same
integral stability theorem supplies both membership and reduction. Its existing public
import `Sheaf.Paper.IntegralConstructibleInternalHom` is preserved. Removed obsolete
maintainer tool approvals for these direct dependencies, retaining the other approvals
in order. Also removed the old direct approvals `lem-fix-operation-reduction`,
`lem-coef-rational-operations`, `prop-weil-pbc-descent-functors`, and
`thm-weil-pbc-idempotent-complete-triangulation`: the field-realization and common-stage
transport theorems already assemble them. These are direct-edge reductions; several remain transitively needed through
stability, and no module is withdrawn or claimed globally unreachable. No source-library
declaration was removed or replaced by a hole.

## Where the brief, the DAG or earlier work was wrong

The DAG's step citing `sixFunctor_sitePerfect_dualEvaluation_isIso` as the exact finite
assertion did not account for its stronger `SixFunctorDatum` input, its chosen closed
presentations, its restricted objects, and its left ordering. The item asks about the
ambient intrinsic closed presentation with only an operation datum. The new obligation
records precisely that missing comparison, using the normalized ringed-site duality
model theorem as its starting point.

The field-operation dependency now has several declarations jointly realizing its node.
The proof uses both `sfPackageFieldOperationRealization` and
`sfPackageFieldUnaryDescent`, rather than treating the former as the entire field-stage
statement. The support-construction predicate contains an existential comparison before
its remaining properties; its rational value clause is projected after eliminating that
existential.

Edge cases: all finite exponents are positive by `n + 1`; the quotient theorem includes
`m = n`; scalar exactness includes the identity extension; rational objects are actual
integral objects; common-stage Hom uses the compositum even for repeated stages; stalk
units follow by a ring map without any nonempty-scheme assumption. For the new obligation,
the target can be zero or unbounded, the source zero or the coefficient unit, and the
scheme empty. Local finite-projective tensor-Hom evaluation covers these cases, without
a dimension hypothesis or constructibility requirement on the target. The source is
Stacks Tag 08JJ (`sites-cohomology.tex`, `lemma-dual-perfect-complex`), read locally.
No unit or chapter route was changed.

## New nodes

`lem-sf-finite-intrinsic-site-perfect-evaluation` records the canonical intrinsic finite
coefficient evaluation isomorphism for a site-perfect source and arbitrary derived target.
It carries the exact Lean signature, three kinds of Mathlib search (plus LeanFinder),
source, local-model proof, and dependencies. It is strictly one component of the original
finite-domain conjunction. Existing normalized perfect duality is not duplicated: the
remaining obligation includes transport to the independently specified intrinsic closed
presentation. No definition or statement changed, so no change record is needed.

## Second reading by B4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
