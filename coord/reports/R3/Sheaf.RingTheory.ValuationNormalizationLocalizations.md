## What changed

Proved `ValuationSubring.integralClosure_maximal_localizations` with its original signature.
The proof constructs the extending valuation subring on the exact canonical localization
subalgebra in the statement, proves its restriction, and proves existence and uniqueness
for every extending valuation subring.

Added `Sheaf.RingTheory.ValuationIntegralMultiplicationCertificate`, with the proved theorem
`ValuationSubring.integralClosure_mul_certificate`. It normalizes a polynomial relation by
its coefficient of maximal valuation, evaluates successive `Polynomial.divX` tails, and
uses valuation separation of the normal integral closure to prove that all tails and their
products with the element are integral. The resulting certificate gives the valuation
criterion in every maximal localization using the local-ring unit test.

Updated the trf node's proof and dependencies to this argument. Corrected the per node's
stale Lean attachment: `normalizationLocalization` and `normalization_localizations` do not
exist in the current module; its unchanged mathematical statement is realized by the
existing `integralClosure_maximal_localizations`, also attached to the trf node. No public
signature, definition, instance, or public import of an existing module changed.

The core algebra inputs were read in Mathlib's `Valuation/LocalSubring.lean`,
`Valuation/ValuationSubring.lean`, `Localization/AsSubring.lean`,
`Localization/AtPrime/Basic.lean`, `Ideal/GoingUp.lean`, and
`IntegralClosure/IntegrallyClosed.lean`; Stacks `algebra.tex` Tags 00IC, 052K, 090P were read.
The polynomial-tail argument is explicitly agent-written, as in the original node.

## Proved and sorry left

Closed the original one hole:
`ValuationSubring.integralClosure_maximal_localizations`
(`lem-trf-valuation-normalization-localizations`).

Added zero holes. The new theorem `ValuationSubring.integralClosure_mul_certificate`
(`lem-trf-valuation-integral-multiplication-certificate`) is proved in full. Every private
helper is proved. There are zero `sorry`s left in either delivered module.

Validation: the certificate compiled cleanly in 3.1 s, and the final classification module
compiled cleanly in 10.1 s through `lcompile.py`, both below the 60 s limit. The existing
theorem signature and public-import list were compared verbatim with the source and match.

Edge cases checked against the construction: `x=0` evaluates each tail at zero to its
constant coefficient; a selected constant or leading coefficient uses the same tail
recurrence and needs no separate division by zero. For `V=K`, the trivial valuation and
maximal ideal zero are allowed; for `L=K` the argument still applies. Only algebraicity
from `FiniteDimensional` is used, with no separability or rank restriction.

## No longer needed

Removed proof imports:
`Mathlib.RingTheory.IntegralClosure.IntegrallyClosed`,
`Mathlib.RingTheory.Ideal.GoingUp`, `Mathlib.RingTheory.Spectrum.Prime.Topology`,
`Mathlib.RingTheory.Valuation.LocalSubring` (available through the retained proved source
API), and `Sheaf.RingTheory.ValuationRingNormal` (replaced by proved Mathlib normality).
The four original public imports remain verbatim.

The item's proof no longer needs these planned nodes:
`lem-weil-pbc-integral-injective-lying-over`, `pqf-lem-going-up`, `pqf-lem-incomparability`,
`lem-weil-pbc-localization-normal-domain`,
`lemma-nagata-local-domain-valuation-dominates`, and
`lem-weil-pbc-valuation-ring-normal` (the holed Sheaf implementation).
Maximal ideal existence is the standard `MaximalSpectrum` instance. The certificate proves
the valuation property directly, so constructing a dominating valuation ring is unnecessary.
Maximal contraction uses the already existing Mathlib leaf
`lem-weil-pbc-integral-maximal-contracts-maximal`.

The integral-closure containment in an extending valuation ring is the easy containment
direction of `lem-trf-integral-closure-valuation-intersection`, supplied by Mathlib's proved
normality instance and `Subring.integralClosure_le_iff`. Removed the obsolete top-level
`tool_uses` entry approving the holed normality theorem; no approvals were added.

These are dependencies unnecessary for this proof, not assertions that their declarations
have no other users. No existing module or source-library declaration is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The per node's Lean attachment was stale, as detailed above; its mathematics is unchanged.
The original plan used going up to prove maximal contraction, although Mathlib already has
the exact maximal-contraction theorem. Its detailed endpoint cases in the tail argument
can be unified by iterated `divX` and the recurrence at the selected coefficient.

The Temkin PDF and Bourbaki volume named by the original node are absent on this machine.
The certificate is not attributed as a statement of those texts: it is a complete agent
reconstruction of the already recorded polynomial-tail plan, using the available Stacks
valuation-separation theorem. No new source availability claim is made.

## New nodes

`lem-trf-valuation-integral-multiplication-certificate`, in
`dag/nodes/sec-trace-formula/`, states only the integral multiplication certificate for one
algebraic element. It has a complete Lean proof, a detailed four-step proof in words,
LeanSearch/LeanFinder/Loogle/grep records, and the inherited blueprint provenance. It does
not restate the localization classification or its restriction and uniqueness clauses.
No definition or statement change record is required.

## Second reading by R3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
