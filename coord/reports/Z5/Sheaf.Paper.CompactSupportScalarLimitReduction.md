## What changed

Filled three of the twelve existing theorem holes in
`Sheaf.Paper.CompactSupportScalarLimitReduction` without changing any statement
or public definition. The proofs use ordinary coefficient balancing, initiality
of the arithmetic index and preservation of K-injectives, the explicit Roos
coordinates, and naturality of the fixed tensor comparison. Added two proof-only
imports: CompactSupportCoefficientModels and Limits.Final. Two proved
private generic restriction lemmas avoid repeatedly unfolding the coefficient
sheaves in the existing exactness instances.

Updated the existing node's proof Steps 3–4 to describe these
arguments. No public interface, target, definition data or source-library file
changes. No new nodes or theorem holes.

## Proved and sorry left

Closed 3 of 12 existing holes, all in namespace
`WeilConjectures.PurStrictScalar`:

- `scalarLimitRestriction_isIso`: the arithmetic index is left adjoint to integer
  division on opposite natural numbers, so ordinary restriction is invertible;
  the derived-unit square and K-injective resolutions transport this to the
  specified derived map.
- `scalarCompletionOrdinary_existsUnique`: the exact existing declaration
  `compactSupportCoefficientModels_ordinary`, already a planned dependency.
- `scalarLimitMapAugmentation`: strict coordinate extensionality, followed by
  naturality of the one fixed Roos comparison.

Added holes: none. Split off: zero. The following nine existing named theorem
holes remain unchanged, all attached to node
`lem-pur-compact-support-scalar-limit-reduction`:

- `WeilConjectures.PurStrictScalar.scalarLimitTensor_exact`
- `WeilConjectures.PurStrictScalar.scalarCompletion_existsUnique`
- `WeilConjectures.PurStrictScalar.scalarLimitRestriction_exact`
- `WeilConjectures.PurStrictScalar.scalarRoosComparison_existsUnique`
- `WeilConjectures.PurStrictScalar.scalarRoosNormalization`
- `WeilConjectures.PurStrictScalar.scalarRoosTensorProducts`
- `WeilConjectures.PurStrictScalar.scalarRoosTensorNormalization`
- `WeilConjectures.PurStrictScalar.scalarLimitArrow_augmentation`
- `WeilConjectures.PurStrictScalar.compactSupportScalarLimitReduction`

This is a partial module delivery under the multiple-hole rule. In particular,
using existing named dependency theorems with sorry is not a claim that their
axioms are closed. The original upper theorem and its normalized-tower,
effectivity, projection, adjoint and quotient-coherence argument remain needed.

## No longer needed

None. No existing import, module or DAG dependency is withdrawn. The unfinished
main proof still needs the original plan. The direct proof of the cofinality
helper avoids using Roos coordinates for that helper; those coordinates remain
needed by `scalarRoosNormalization` and the main node.

## Where the brief, the DAG or earlier work was wrong

No false statement or target mismatch found. The ordinary balancing helper
already occurs verbatim in the planned coefficient-model dependency. Arithmetic
restriction invertibility has a shorter direct proof by initiality; its actual
Roos coordinate normalization remains a separate existing obligation.

Edge cases checked in the argument: e=1 gives the identity arithmetic index;
positive e makes division valid and gives an unbounded subsequence. No boundedness
hypothesis on the tower complex is introduced. Augmentation coordinate arguments
also apply to zero complexes and identity maps. The Roos-comparison uniqueness
proof was explored but remains open: its universal property argument currently triggers expensive unfolding in this specialization;
no part of that unfinished proof is included in this packet.

The composite augmentation proof was also attempted, but its rewriting of large
comparison definitions exceeds the fixed compile time. It is restored to its
original named hole for this round. No new axioms, definitions or holes are added.

## Second reading by Z5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
