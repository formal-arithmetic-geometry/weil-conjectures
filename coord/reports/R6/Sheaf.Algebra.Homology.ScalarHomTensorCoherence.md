## What changed

Proved `CategoryTheory.scalarHomTensorCoherence` by comparing the ordinary chain
adjunctions with the normalized derived adjunctions. First extend the unit
normalization from flat K-flat resolutions to every complex by naturality. Use
the resulting transpose formula to identify the composition and identity
comparisons on representatives. Check the chain tensor equations on total pure
generators, paste the specified tensor normalization squares, and descend by
naturality along isomorphisms from K-flat representatives. All auxiliary statements
are proved private helpers in the item module. The public theorem signature is unchanged. The former private
`complexIso_unique`, `tensorIso_unique`, and `comparison_unique` route is replaced;
no active or quarantined consumer refers to those helpers.

The change record
`coord/changes/scalar-hom-tensor-coherence-private-proof-scope-R6.md` documents the
private helper removals and local proof-scope commands, including all textual
consumer matches. No consumer needs adaptation.

The node's proof steps and proof dependencies now describe this argument. Added
the proof-only import `Sheaf.CategoryTheory.DerivedCategory.ExactRestrictionComposition`
for the existing cochain factorization equations for exact restriction. After
proving the representative equations, keep the canonical restriction and extension
comparisons locally irreducible to avoid repeatedly unfolding their localization
and adjunction constructions. Retain the ordinary restriction composition and
identity isomorphisms explicitly in the chain comparisons. The generic exact-functor
factorization equations identify their images under localization. Prove inverse
factorization, cancellation, and adjunction identity calculations for arbitrary
categories before specializing them to scalar restriction. This keeps the sheaf
constructions out of the categorical cancellation proofs. Use the normalized unit
equation directly in transpose comparisons, and compose explicit generator
equalities rather than rewriting across large complex constructions. Exported
definitions and attributes are unchanged.

Validation: the prescribed single-file compiler, including the delivery axiom
probe, and the delivery preflight.

## Proved and sorry left

Closed: `CategoryTheory.scalarHomTensorCoherence` (one existing hole).
Added: none. Remaining holes in the delivered module: none. No statements were
split off. This proof uses existing named dependencies, including dependencies
whose proofs remain unfinished elsewhere in the project.

## No longer needed

Removed the proof import `Sheaf.Paper.ResolvingRepresentativeWhiskering`.
No modules are withdrawn.

The former direct proof dependencies below are unnecessary for this proof:

- `lem-sfb-scalar-tensor-cancellation-independent`
  (`Sheaf.Algebra.Homology.ScalarHomTensorCancellation`): the given generator
  equations suffice; no new tensor-cancellation construction is needed.
- `lem-pur-sheaf-ring-derived-coefficient-adjunction`
  (`Sheaf.Algebra.Homology.SheafRingDerivedCoefficientAdjunction`): this proof uses
  the normalized adjunction fields of the supplied models directly. The module
  remains a transitive statement dependency through `ScalarInternalHomData`.
- `lem-weil-pbc-tensor-comparison-descent-representatives`
  (`Sheaf.Paper.TensorPullbackRepresentativeDescent`): K-flat resolutions and essential
  surjectivity of the quotient give direct naturality descent.
- `lem-weil-pbc-resolving-representative-whiskering`
  (`Sheaf.Paper.ResolvingRepresentativeWhiskering`): equality of natural
  transformations descends directly along the isomorphisms from K-flat
  representatives; full faithfulness of whiskering is unnecessary.
- `lem-pur-cochain-pullback-tensor-coherence`
  (`Sheaf.SecSmoothPurity.CochainPullbackTensorCoherence`): scalar coherence is
  checked directly on total tensor generators.

These are pruned edges of this node's proof, not claims that the corresponding
modules are globally unused. The blueprint unit route is unchanged.

## Where the brief, the DAG or earlier work was wrong

No statement repair is required. Intermediate scalar extensions need not be
termwise flat: naturality of the unit comparison along a flat K-flat resolution
extends normalization to all complexes before composing adjunctions. This avoids
an unnecessary extra flatness requirement in the proof route. No definition,
public signature, or adopted source-library declaration was changed.

## Second reading by R6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
