## What changed

Replaced the sorry in `internal_residue_stacks_comparison` by a complete assembly
proof from a natural comparison of the actual first-residue functors. The target's
signature and both public imports are unchanged. Added the proof import
`Sheaf.SixFunctors.ProEtale.InternalFirstResidueReductionComparison`, together with
proof imports for the existing constructible-model and Tor transport APIs.

The new structural comparison has no Noetherian, constructibility, boundedness,
finite-Tor, or completeness hypotheses. It identifies functors into the two actual
residue module categories after a residue ring-object isomorphism. It is not the
original predicate equivalence renamed or repackaged. The item proves the remaining
steps: homology transport, preservation and reflection of constructible local models,
preservation and reflection of every Tor interval, existential quantification of
those intervals, and boundedness from the tensor-unit test.

Updated the item's proof, proof_deps, and proof_origin to this route. No existing
statement or definition was changed, and no consumer needs adaptation.

## Proved and sorry left

Closed: `AlgebraicGeometry.ProEtale.internal_residue_stacks_comparison` (one existing
hole). Its proof is complete relative to the named structural comparison.

Added and left: `AlgebraicGeometry.ProEtale.internal_first_residue_reduction_comparison`
in `Sheaf.SixFunctors.ProEtale.InternalFirstResidueReductionComparison`, node
`lem-sfb-internal-first-residue-reduction-comparison` (one new hole). Its entire proof
is `by sorry`, with a source and full proof in words in its docstring and node.
There are zero holes left in the item module and one hole in the delivery. This is
a decomposition, with net hole change zero, not a claim of a sorry-free comparison.

Validation: both modules compiled through `lcompile.py`; the final assembly compiled
cleanly in 27.2 seconds.

The construction uses no chosen data from an unproved existence statement: both the
ring isomorphism and the natural isomorphism are eliminated inside a proposition proof.
There is no new definition, axiom, or private unfinished helper.

## No longer needed

No existing public imports were removed: both are needed by the unchanged statement.
The new proof uses each of its proof imports.

The item no longer directly uses `det-lem-integral-models-stacks`
(`Sheaf.AlgebraicGeometry.IntegralModelsStacks`): no complete-object Stacks criterion
is needed for a comparison which makes no completeness assumption.
It no longer directly uses `lem-pe-finite-coefficient-model-comparison`
(`Sheaf.Paper.FiniteCoefficientModelComparison`): both sides already use the same
finite constant-model predicate, so conversion through ordinary finite stalks is
unnecessary. It also does not need the well-definedness conjunction from
`det-def-sfb-constructible-tor-amplitude` (`Sheaf.Paper.ConstantModelTorAmplitude`):
the native Tor-isomorphism and exact monoidal-functor lemmas suffice, and
`constantModelConstructible_transport` transports the constructible homology.
These modules were not imported by the original item, and none is withdrawn or
claimed globally unreachable.

The first-quotient part of `det-prop-integral-criterion-constant-coefficients` remains
needed below the new structural node. `def-sfb-integral-constant-model-realization`
remains needed in the statement and in that node. They are not pruned.

## Where the brief, the DAG or earlier work was wrong

The declared dependencies give their comparisons in different coefficient models:
`integral_constant_completion` provides the common-quotient isomorphism on the
coefficient-sized small ringed site, while the item uses internal modules and two
point presentations. Its statement does not directly supply the needed natural
isomorphism of these internal residue functors. The new node records exactly this
remaining transport and its finite constant-to-continuous coefficient comparison.

The constructibility step does not require the full finite-coefficient comparison:
restriction along a condensed ring-object isomorphism already preserves and reflects
finite presentations, covers, and strata. The proof reuses the proved generic private
`constantModel_comap_iff` helper via `import all` of
`Sheaf.Paper.IntegralConstantModelHeartClosure`; it does not use the integral-heart
closure theorem. The native derived-category lemmas prove the Tor and unit-test
steps without any additional holes.

Checked edge cases: arbitrary unbounded input complexes are admitted; finite Tor
amplitude supplies boundedness only for the reduced complex. No a <= b hypothesis
is silently inserted into the native existential Tor predicate. Empty schemes and
zero complexes use the same isomorphism and unit arguments. The finite-discrete
point comparison uses the empty cover for an empty profinite object. No target or
unit route is changed.

## New nodes

`lem-sfb-internal-first-residue-reduction-comparison` states the structural natural
common-quotient comparison, in
`lean/Sheaf/SixFunctors/ProEtale/InternalFirstResidueReductionComparison.lean`.
It isolates steps (1)--(2) of the original node before all constructibility and Tor
arguments. Its proof plan uses the existing flat constant-completion comparison,
normalized integral section squares, flat restriction of K-flat complexes, and
internal-section scalar adjunction. Mathlib searches were run with LeanSearch,
LeanFinder, Loogle, and grep; none supplies this specific internal coefficient
comparison. Sources read: the current integral-models proof (1)--(2), Stacks
`proetale.tex` section-derived-completion-noetherian (099L),
`sites-modules.tex` lemma-completion-flat, and `sites-cohomology.tex`
definition-tor-amplitude (08FZ). There is no change record because no existing
statement or definition is modified.

## Second reading by T6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
