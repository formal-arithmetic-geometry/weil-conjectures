## What changed

Proved `AlgebraicGeometry.Etale.directImageCTFNonproper` with its signature unchanged,
using `torAmplitudeIn_rightDerivedLowerStar` and
`boundedConstructible_rightDerivedLowerStar_of_locallyOfFiniteType` from the source
library. Both are available through the item's existing public imports.

The proof establishes finiteness of the lifted coefficient ring, characteristic p
of the base field, annihilation by ell^n, and invertibility of ell^n over the base
and Y. It converts between the cohomology-vanishing Tor predicate and the canonical
t-structure predicate before and after applying the direct-image theorem. The private, proved API lemma `hasTorAmplitudeIn_iff_torAmplitudeIn` establishes
this equivalence for an arbitrary commutative ring. It explicitly unfolds only
`derivedTensor` and `MonoidalCategory.curriedTensor`. Applying this API avoids the
kernel repeatedly expanding the concrete quotient ring through the tensor structure;
the former inline conversions timed out at kernel checking. The repaired module
compiled in 14.4 seconds. A local irreducibility attribute controls elaboration of
the derived tensor.
The DAG proof, proof dependencies and proof origin follow this route.

Added proof imports `Sheaf.NumberTheory.Padics.ExtensionIntegersDvr` and
`Mathlib.Algebra.CharP.CharAndCard`. No definition, public import, or statement changed. The preflight treats the added
local irreducibility attribute as a command requiring documentation. The change record
`coord/changes/H7-sf-direct-image-local-tensor-attribute.md` documents its lexical scope,
unchanged public interface, and consumer checks; no consumer adaptation is needed.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.Etale.directImageCTFNonproper`
(node `cor-sf-direct-image-ctf-nonproper`).

Holes closed: 1 of 1. Holes added: 0. No sorry remains in the delivered module.
The proof uses the existing library's stated direct-image theorem; its dependencies
remain the responsibility of their existing DAG nodes.

Validation: module compiled without errors or warnings; final delivery preflight follows.

## No longer needed

Removed proof imports:

- `Sheaf.AlgebraicGeometry.EtaleDirectImageVanishing`
- `Sheaf.Paper.DirectImageTorAmplitude`
- `Sheaf.Paper.FiniteCoefficientFlatModel`
- `WeilConjectures.SixFunctors.Etale.Derived.DirectImageVanishing`

The direct dependency `lem-sf-etale-direct-image-vanishing` is subsumed by the source
library's dimension-bound direct-image Tor theorem. The separate flat-model import
is unnecessary at this application site. The flat-model, all-module vanishing,
finite-constant projection formula and residue-test argument remains inside the
library theorem: the unit's route is retained. These are removals from this item's
immediate dependencies, not claims that the underlying theory is globally unused.
`thm-sf-direct-image-tor-amplitude` remains a proof dependency; its specialized
source-library formulation is used instead of its p-adic-extension wrapper.
No module is withdrawn and no new node is created.

## Where the brief, the DAG or earlier work was wrong

`sf_directImage_torAmplitude` takes `E : Type (u + 1)` and its ordinary quotient,
whereas this item takes `E : Type u` and a universe lift of its quotient. Its
additional interval-order hypothesis is also absent from this item. The source
library's dimension-bound direct-image theorem avoids both mismatches and applies
to the lifted coefficient ring directly. The original signature is preserved,
including empty intervals, zero coefficient rings and empty schemes.

The earlier draft's finite-ring theorem lives in a newly added source module whose
compiled artifact was not yet published. The delivery uses the established public
`torAmplitudeIn_rightDerivedLowerStar` interface and supplies its full hypotheses.
The newer source interface and the published interface have the same remaining
arguments; Lean infers the coefficient parameter from K and its hypotheses.

## Second reading by H7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
