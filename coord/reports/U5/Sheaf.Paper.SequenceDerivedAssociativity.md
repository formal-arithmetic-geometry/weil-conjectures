## What changed

Proved `WeilConjectures.sequenceDerivedCoherence` in
`Sheaf.Paper.SequenceDerivedAssociativity`, preserving its signature and the
existing public import. No other existing Lean module is changed.

The ordinary argument is reused from the parent module's proved private helpers:
sectionwise fibre-product pasting gives direct-image coherence, and the Mathlib
adjoint-composition associativity law gives ordinary pullback coherence. The existing proved private
`descend_coherence` helper transports that equation through the exact-derived comparison API
using compatibility with composition, both whiskerings, and associativity.
Equality induction handles the scheme-associativity transport. The resulting
natural transformation equation is evaluated at the supplied derived object.

The proof privately imports all of `IntegralComparisonSequenceSystems` for its
existing direct-image comparison and section formula, and all of
`FiniteSystemPullbackCoherence` for the proved generic pasting, mate-transport and
localization helpers. It never imports the parent module, avoiding a cycle.
No extra public import is added. A private wrapper supplies the full site-functor
type to the generic fibre-product comparison so that elaboration chooses the
small pro-etale category structure before projecting a component.

Updated the item's node to describe these steps and its actual proof dependencies.
The Stacks source was read at `sites-cohomology.tex`,
`lemma-derived-pullback-composition` (Tag 0D6D); this sequence coherence refinement
is the stated agent-formulated application of that construction.

## Proved and sorry left

Closed: `WeilConjectures.sequenceDerivedCoherence` (1 of 1 original holes).
Server `lcompile.py` check passed in 18.3 seconds with no errors or warnings.
Added: none. Remaining holes in the delivered Lean file: none.
All added helpers are private and completely proved. Existing dependency holes
are unchanged.

## No longer needed

No modules are withdrawn and no existing public imports are removed.
The proof does not need the scalar associator, scalar unitor, K-flat-model
calculations or finite-bracketing data of
`def-trf-quotient-system-coherence-data` as proof dependencies: the ordinary
sequence construction and the exact-localization coherence API suffice. Its
public import and statement dependency are retained for compatibility.
`lem-trf-adjoint-composition-coherence` remains needed. The existing proved
generic helpers in the module for `lem-pod-finite-system-pullback-coherence`
are reused; its finite-coefficient theorem is not specialized or assumed. No unit route is bypassed.

## Where the brief, the DAG or earlier work was wrong

The original one-step plan was valid. Its equality-transport and derived-whiskering
glue can be proved directly from the existing API, so no second split is needed.
The rework row refers to an earlier quarantined import closure; the current item
source exists and its declaration and attachment are preserved.

## Second reading by U5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
