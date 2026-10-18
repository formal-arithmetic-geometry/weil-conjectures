## What changed

Proved both declarations in `Sheaf.RingTheory.UniformPerfectQuotientBound`, preserving
all existing signatures and public imports. The uniform bound uses the finite set
of maximal ideals containing I, with a common bound for their local ring depths.
Only `hfinite 1` is needed. For each quotient, perfectness supplies finite projective
dimension, localization preserves it, and Auslander–Buchsbaum bounds the local
projective dimension by the local ring depth. The maximal-localization criterion
then gives the global bound. The finite support argument also handles I = top
and the zero ring: the indexing type can be empty. Zero localizations are handled
separately from the nonzero hypothesis in Auslander–Buchsbaum.

Added two fully proved helper modules, each with one public theorem and a DAG node:
`Sheaf.RingTheory.PerfectModuleFiniteProjectiveDimension` proves finite projective
dimension of a perfect single module using K-projective models and Ext vanishing;
`Sheaf.RingTheory.BoundedFiniteProjectiveResolution` constructs a resolution of the
prescribed length by finite projectives through finite free presentations, dimension
shifting, and an explicit augmentation splice. The latter refines the construction
in `Sheaf.RingTheory.ProjectiveResolutionSuccSplice` to retain degreewise finiteness.
Its private splicing helper is fully proved. Bound zero uses the identity resolution.
The new statements hold for the zero module as well.

Updated the original node's proof, proof dependencies and proof origin to match this
route. The unit statement and realized steps are unchanged. The Tor characterization
needs only Noetherianity and cyclicity; the original extra hypotheses are preserved,
with a local unused-variable linter setting documenting their redundancy.

Validation: all three modules compile together without warnings through lcompile.py.
Explicit `#print axioms` checks show only propext, Classical.choice and Quot.sound
for both new helpers and the original Tor equivalence. The uniform-existence theorem
still depends on the existing Auslander–Buchsbaum theorem's sorryAx, as intended for
this stage. No data definitions were added or changed.

## Proved and sorry left

Holes closed: 2 of 2 original holes.

- `ModuleCat.exists_uniform_finite_projective_resolution_quotient_pow`
  (node `lem-weil-pbc-uniform-perfect-quotient-bound`).
- `ModuleCat.uniform_finite_projective_resolution_quotient_pow_iff_tor_vanishing`
  (same node); this theorem now has only the three permitted axioms.

Holes added: zero. Split-offs with sorry: zero. No sorry remains in any delivered
Lean file. Both new helper theorems are fully proved with only permitted axioms.
The imported, unchanged
`IsLocalRing.depth_eq_projectiveDimension_add_depth`
(node `lem-weil-pbc-auslander-buchsbaum`) is the remaining transitive hole used by
the uniform-existence proof; this delivery does not claim to prove it.

## No longer needed

Removed these direct proof imports:

- `Sheaf.RingTheory.ProjectiveResolutionExtCharacterization` and node
  `lem-weil-pbc-projective-dimension-ext-characterization`: the smaller existing
  `BoundedProjectiveResolutionDimension` interface suffices; the Tor converse uses
  the existing Tor-bound criterion directly.
- `Sheaf.RingTheory.ProjectiveResolutionKernelProjective` and node
  `lem-weil-pbc-projective-resolution-kernel-projective`: finite-presentation
  induction constructs the bounded finite resolution directly, with no shortening
  of a separately chosen resolution.
- `Sheaf.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral`: the actual
  unchanged signatures use the source library's `DerivedCategory.IsPerfect`, so
  the separate arbitrary-localization-universe predicate is unused by these proofs.
  Its node `def-pc-perfect-ring-complex` remains a statement dependency: the
  mathematical notion of perfectness is still essential.
- `Sheaf.RingTheory.Depth`: supplied publicly by AuslanderBuchsbaum and
  DepthLeSupportDimension; its declarations and node are still used.
- `Mathlib.Algebra.Module.LocalizedModule.Exact` and
  `Mathlib.RingTheory.LocalProperties.Projective`: supplied by Mathlib's
  LocalProperties.ProjectiveDimension. Their localization exactness/projectivity
  nodes remain relevant to the localization API's proof.

The positive-tail cancellation, the repetition-of-powers depth-zero argument for
(A/I)_m, and the choice r equal to a resolution length of A/I are unnecessary.
Finiteness of the maximal support and finite local ring depth replace those steps.
No module is claimed to be globally unreachable: the removed modules can still
have other users, including transitive users of imported algebraic results.

## Where the brief, the DAG or earlier work was wrong

No false statement was found. The old plan's two long constructions can be replaced:
K-projective Hom comparison gives finite projective dimension without cancelling
positive terms, and finite-presentation induction retains finite resolution terms
without invoking the general kernel-projectivity theorem. The old direct imports
did not provide these precise bridges, so they are supplied and proved here.

## New nodes

`lem-weil-pbc-perfect-module-finite-projective-dimension`:
`lean/Sheaf/RingTheory/PerfectModuleFiniteProjectiveDimension.lean`, declaration
`ModuleCat.finite_projectiveDimension_of_perfect_single`. A bounded projective
model is K-projective. Maps to a sufficiently shifted single module vanish in
all degrees; the K-projective comparison and Ext.homEquiv transfer this to the
Ext definition of projective dimension. Fully proved; no further work remains.

`lem-weil-pbc-bounded-finite-projective-resolution`:
`lean/Sheaf/RingTheory/BoundedFiniteProjectiveResolution.lean`, declaration
`ModuleCat.exists_bounded_finite_projective_resolution`. Dimension shifting and
a finite free presentation reduce the bound inductively. An explicit augmented
complex preserves exactness, finite projective terms and the support bound.
Fully proved; no further work remains. No change record is needed because all
existing statements and definitions remain unchanged.

## Second reading by G4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
