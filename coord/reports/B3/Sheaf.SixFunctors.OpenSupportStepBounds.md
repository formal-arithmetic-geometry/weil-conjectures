## What changed

Proved `WeilConjectures.IntegralSystemRealization.openSupportStep_bounds` from
existing declarations, with its signature unchanged.

The finite open CTF theorem proves preservation of the same cohomological and Tor
intervals. Bounded constructible etale descent and full faithfulness rebuild compatible
origins from the output levels, with both actual transition squares proved in Lean.
The integral clause uses the constructibility component of the already constructed
canonical open-factor coherence data.

Normalization uses a whole-system reconstruction argument. The actual normalized
reconstruction counit identifies the input with reduction of its total limit. The
proved `GeneratorReduction.fixedOpenReduction_isIso` helper in
`Sheaf.SixFunctors.OpenReconstructionEffectivity` identifies the canonical open extension
of that reduction with an actual reduction system. Such systems are normalized.
Uniqueness of left adjoints to the fixed system pullback transports this property to
the specified arbitrary `o.extension`. No compatibility of finite evaluations is used
to detect equality of system morphisms.

Only the item module and its proof route node change. All added imports are private
proof imports (`import all` is used to reuse existing proved private helpers). No
source-library file, public import, definition or statement changes.

## Proved and sorry left

Closed the one original hole:
`WeilConjectures.IntegralSystemRealization.openSupportStep_bounds`
(node `lem-sf-open-support-step-bounds`). There were 1 original holes; 0 remain.
No holes were added or split off. Every private helper is proved.

The proof uses existing project declarations, including declarations whose proofs
still contain sorry; their obligations remain with their existing nodes. This report
claims closure of the assigned hole from those declarations, not axiom-freedom of the
entire imported library.

## No longer needed

No original imports were removed: the original module had only its two public
statement imports, and both remain verbatim.

The proof no longer directly needs these planned dependencies:

- `lem-sf-open-finite-constructibility-interval`, module
  `Sheaf.Paper.OpenFiniteConstructibilityInterval`: the stronger proved finite open CTF
  theorem gives the same cohomology and Tor intervals at once.
- `lem-sf-open-tensor-normalization`, module
  `Sheaf.SixFunctors.OpenTensorNormalization`: normalization is transported from an
  actual reduction system using the invertible canonical open-reduction mate.
- `lem-sf-integral-open-reduction-comparison`, module
  `Sheaf.SixFunctors.IntegralOpenReductionComparison`, and
  `lem-sf-integral-open-extension-complete`, module
  `Sheaf.SixFunctors.IntegralOpenExtensionComplete`: the integral clause reuses the
  constructibility component of the existing canonical open-factor data.
- `lem-weil-pbc-normalized-etale-origin-witnesses`, module
  `Sheaf.Paper.NormalizedEtaleOriginWitnesses`: bounded constructible descent and full
  faithfulness construct the required Origins structure directly from level bounds.

These are removals from this node's direct proof dependencies. Transitive users and
other consumers remain; no whole-library withdrawal or pruning is claimed.

## Where the brief, the DAG or earlier work was wrong

No false statement was found. The planned extension of the retained origin witnesses
is unnecessary. The level bounds suffice to reconstruct them and lift the actual
transition maps by full faithfulness.

The direct quotient-transition coherence calculation is unnecessary: normalized
reconstruction and the existing proved canonical open-reduction mate supply a shorter
whole-system argument. The private `fixedOpenReduction_isIso` helper is stronger than
the exported effectivity statement: its source module proves it for every integral
input, and this proof imports and applies that exact existing declaration.

The finite open CTF and canonical open-factor coherence declarations are reused as
tools; the unit's statement and route are retained. Identity opens, empty opens and
zero inputs are included. No structural separatedness or new input hypothesis is
introduced. No arbitrary witness of an unproved existence theorem is used to define
data: all choices occur inside theorem proofs.

Validation: the complete item compiled cleanly through lcompile.py in 14.9 seconds.
The theorem signature and both public imports match the repository verbatim. The
updated proof dependencies are acyclic, and all Lean lines are at most 100 characters.

## Second reading by B3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
