## What changed

Replaced the proof of `AdicCompletion.completion_localizedAlgebra_finite_quotients`
without changing its signature or any public import. The proof now identifies each
image ideal with the localization of pS, proves its containment and cofinal powers
using integral minimal primes and Mathlib's radical-power lemma, handles exponent
zero explicitly, and proves discreteness of the positive quotient spectrum in the
proved private helper `AdicCompletion.finite_local_quotient_discrete`.

For positive exponents, one new intermediate theorem identifies the canonical local
charts. The item constructs the actual product equivalence from
`MaximalSpectrum.toPiLocalizationEquiv`, `RingEquiv.piCongrLeft'`,
`RingEquiv.piCongrRight`, and `IsLocalization.algEquiv`. `AlgEquiv.commutes` identifies
its ring map with the stipulated product of quotient maps. This is a reduction to
local charts, rather than a restatement of the quotient-map bijection.

Added `Sheaf.RingTheory.LocalizedFiniteQuotientCharts`, with one theorem and its
node. Updated the item's proof, proof dependencies, and proof origin to follow the
Lean argument. No definitions, existing statements, or interfaces changed.

Both modules compile together through lcompile.py. The source text was read online
because this checkout does not contain literature/stacks-project/algebra.tex:
[07N9](https://stacks.math.columbia.edu/tag/07N9),
[00E3](https://stacks.math.columbia.edu/tag/00E3),
[00CT](https://stacks.math.columbia.edu/tag/00CT), and
[00JA](https://stacks.math.columbia.edu/tag/00JA).

## Proved and sorry left

Closed the item's only hole:
`AdicCompletion.completion_localizedAlgebra_finite_quotients`
(node `lem-weil-pbc-completion-localized-algebra-finite-quotients`).
The theorem has no sorry in its body. Its cofinal bounds, exponent-zero case,
discrete-spectrum helper, and assembly of the product bijection are proved.

Added one remaining hole:
`AdicCompletion.localized_finite_quotient_charts`
(node `lem-weil-pbc-localized-finite-quotient-charts`), in its own module.
Its proof is exactly `by sorry`; its docstring and node give the complete argument.
It only gives the canonical index correspondence and localization structures,
without asserting product bijectivity or any cofinal ideal bound. The characterizing
contraction formula determines the index equivalence, and the localization structures
uniquely determine the canonical factor equivalences used in the item's proof.

This is a decomposition: one original hole closed, one smaller hole added, net zero
before any pruning. The item still depends on this named hole and is not asserted to
be axiom-free. No other sorry was added or left in delivered files.

Edge cases checked: n=0 is handled by subsingleton quotients in the item, and is
excluded from the chart lemma because J^0 is the unit ideal. For empty Q, the
positive-degree quotient is the zero ring and its maximal spectrum is empty;
the canonical product assembly works for empty indices. Zero S gives this empty
case. For R a field and p=0, the chart statement reduces to the local-factor
correspondence of a finite-dimensional algebra. No reducedness, nonzero prime,
faithful algebra, or finite residue field assumption is used. The chart argument
only needs module-finiteness, not Noetherianness.

## No longer needed

Removed direct proof imports:
- `Mathlib.RingTheory.Localization.BaseChange`
- `Mathlib.RingTheory.Localization.Ideal`
- `Mathlib.RingTheory.Spectrum.Prime.Topology`
- `Mathlib.RingTheory.Localization.Submodule`
- `Mathlib.RingTheory.Finiteness.Ideal`
- `Mathlib.RingTheory.Artinian.Module`
- `Sheaf.RingTheory.LocalizationPrimeResidueFieldIso`

The quotient comparison has no need for these original planned nodes:
- `lem-weil-pbc-artinian-local-unique-prime`
- `lem-weil-pbc-finite-dim-algebra-artinian`

The first is replaced by integral minimal primes and localization of radicals;
the second by the finite-over-zero-dimensional-local discrete-spectrum theorem.
No Sheaf module corresponding to these Mathlib leaves was present.

The following old direct proof dependencies have moved to the chart lemma:
- `lem-weil-pbc-localization-base-change`
- `lem-weil-pbc-localization-at-prime-of-quotient`
- `lem-weil-pbc-localization-prime-residue-field-iso`

These base-change, quotient-localization, and localization-prime-correspondence
nodes remain in the pending chart lemma's proof dependencies. In particular,
removing the direct LocalizationPrimeResidueFieldIso import from the item does
not claim that its node is unnecessary for that pending proof. The product-of-
localizations node stays and is applied directly from Mathlib. No unit statement
or realized unit step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The existing plan passes through Artinian local special fibres to prove radical
bounds; integral incomparability and minimal-prime localization give those bounds
directly from Mathlib. The finite local power-bound module also already proves a
stronger uniform bound. Its compiled module was initially absent from the last
green build, so the present proof uses direct Mathlib ingredients instead of copying
or restating that declaration.

The item's blueprint.from.node points to another created node rather than the
imported ancestor. The ancestor tool returned None. The new node instead follows
the already recorded ancestry of CompletionLocalizedAlgebraProductSurjective to
`thm-weil-pbc-finite-etale-lifting`, preserving its via chain. The item's blueprint
field is outside the worker's permitted fields and was not changed.

## New nodes

`lem-weil-pbc-localized-finite-quotient-charts` in
`dag/nodes/sec-proper-base-change/lem-weil-pbc-localized-finite-quotient-charts.json`:
the canonical prime-index correspondence and local quotient charts for n>0.
Its module is `lean/Sheaf/RingTheory/LocalizedFiniteQuotientCharts.lean`.
The statement drops the unnecessary Noetherian hypothesis and compatibility
hypothesis on psi; any S-algebra map from the localization B is the canonical map.
The proof follows the finite-quotient paragraph of Tag 07N9 and Tags 00E3/00CT.
Searches were run via msearch.py: LeanSearch was unavailable, LeanFinder and Loogle
found localization ingredients and more restrictive Dedekind statements, and grep
found the prime order-isomorphisms and quotient-localization instance. Blueprint
searches for localization quotient and prime correspondence found no exact node.
No change record is required, since no existing interface changes.

## Second reading by X2

1. Compared both delivered modules with the repository. The item is the only
existing module; its existing theorem signature is byte for byte unchanged,
including universes, all hypotheses, the compatibility assumption, and the
quotient-map conclusion. Public imports and visibility are unchanged. There are
no changed definitions or forced adaptations. Verdict: pass.

2. Compiled both modules in import order with lcompile.py, then recompiled after
pruning imports: no errors or warnings. Inspected all bodies: the only sorry is
`AdicCompletion.localized_finite_quotient_charts`, exactly in its named theorem.
There are no forbidden declarations, attributes, or hollow definitions. Scratch
#print axioms checks for both public theorems show only propext, Classical.choice,
Quot.sound and sorryAx. The main theorem remains dependent on the chart hole.
The proved private helper contains no hole; the delivery tool also probes every
declaration. Verdict: pass as a decomposition, not an axiom-free proof.

3. Read the chart statement, docstring and complete node against Stacks Tags
[07N9](https://stacks.math.columbia.edu/tag/07N9),
[00E3](https://stacks.math.columbia.edu/tag/00E3) and
[00CT](https://stacks.math.columbia.edu/tag/00CT). The prime correspondence,
maximality by integrality, localization in stages and quotient localization prove
exactly the statement. Neither Noetherianness nor compatibility of psi is needed:
the localization universal property determines every S-algebra map psi. Checked
n=1, p=0 over a field, nonfaithful finite algebras, zero S and empty Q; n=0 is
correctly excluded and proved separately in the item. The contraction formula
uniquely determines e by the localization and quotient correspondences, so its
use does not choose arbitrary data from unproved mere existence. The hole gives
local charts, not the cofinal bounds or product bijectivity: it is strictly a
part of the original argument. Repeated msearch.py LeanFinder with "local ring
factors of a finite algebra over a localized base modulo a prime ideal power"
and Loogle with "IsLocalization.AtPrime, Ideal.quotientMap"; found restrictive
Dedekind ingredients and no combined theorem. Independently rg-searched Mathlib,
upstream RingTheory and lean/Sheaf/RingTheory using quotient/localization and
primesOver-equivalence terminology. Nearby tensor quotient detection and tensor
factor localization theorems have different conclusions. No duplicate or quick
closure was found. Verdict: pass.

4. Read the main proof downward: proved ideal identification and cofinality,
zero-exponent case, proved discrete-spectrum helper, then actual composition of
product, reindexing and factor equivalences. The use of AlgEquiv.commutes verifies
the specified quotient map. Proof-only imports are plain import. Removed four
redundant proof imports (Localization.Submodule, Spectrum.Prime.Noetherian,
Finiteness.Ideal and Ideal.GoingUp); the remaining imports supply the used
constructions and lemmas. Checked every old proof dependency against the new
list: two are obsolete, three move to the chart lemma, all others remain.
Clarified that distinction under No longer needed. Read sk-thm-p1's realized
statement and steps: this is a below-unit algebraic refinement and bypasses none
of them. Verdict: pass.

5. Compared the changed node proof and dependency union with the Lean argument;
checked the new node's declaration text, source, searches, creation metadata,
blueprint ancestry, chapter and unit. The node agrees with the chart theorem and
the existing node's changed fields are within the allowed proof fields. No
statement change or change record is needed. Verdict: pass.

Second reading changed only redundant proof imports and this report's explicit
account of transferred dependencies; the mathematical proof and statements stay
as submitted. One original hole closed, one smaller hole added, net zero. No
claim of a globally pruned module is made.
