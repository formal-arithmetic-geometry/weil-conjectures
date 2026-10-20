## What changed

The unchanged theorem `AlgebraicGeometry.exists_twoTermPerfectDeterminantData` now has a
complete assembly proof. It combines a proved Tor-window equivalence, proved model/zero
and arbitrary-pullback membership, proved normalized recorded pullback coherence, and two
strict subresults: the affine good-diagram construction and affine descent.

`Sheaf.TraceFormula.TwoTermPerfectTorWindow` contains the full Lean argument for the
characterization. Simultaneous local trivialization gives the forward direction; finite
free residue models and vanishing residue Betti numbers give the converse. The same
models prove preservation under every scheme morphism using the existing localized
strictly-perfect-model pullback comparison. No affine, separatedness, quasi-compactness,
global-rank or nonempty-scheme hypothesis is added.

`Sheaf.TraceFormula.TwoTermDeterminantPullbackCoherence` proves that the section-normalized
ordinary comparison gives exactly the recorded derived composition lift, then applies
the existing coherence theorem with the original K-flat counits. The resulting left unit
law at the identity supplies the original normalization field.

The unchanged definitions are publicly reexported from
`Sheaf.TraceFormula.TwoTermPerfectDeterminantData`, so the two genuine remaining results
can depend on the data without an import cycle. The affine interface includes explicit
compatible exterior-formula, zero and evaluation families on affine test schemes over
arbitrary model schemes. This supplies the precise compatibility needed for descent;
unrelated objectwise model isomorphisms would not be enough.

The duplicate declaration of `schemeDerivedTensorCohomologyVanishes` in the Sheaf module
is replaced by a public reexport of the adopted source definition. A private `rfl` proof
checks equality with the complete old body, including the two K-flat predicates and
independent universes. All eight unchanged consumer modules compile against this repair.
No file under WeilConjectures is modified. The quarantined item and parent are preserved.

All delivery modules and all eight predicate consumers compile without errors or warnings
through lcompile.py. Each individual file took at most 25 seconds in the verification run.
The temporary unchanged consumer copies were removed from the packet after verification.

Change records:
`coord/changes/G2-derived-tensor-vanishing-single-definition.md` and
`coord/changes/G2-two-term-determinant-data-location.md`.

## Proved and sorry left

Original item: one hole, `AlgebraicGeometry.exists_twoTermPerfectDeterminantData`.
That hole is closed by a compiling proof with its original signature and all original
normalization fields. Two holes are added below it, so this is a decomposition, not a
claim that the determinant functor has become axiom-free or a net proof-hole reduction.

Independently proved, with no new holes:

- `AlgebraicGeometry.isTwoTermPerfect_iff_perfect_tor`.
- `AlgebraicGeometry.twoTermPerfect_model`.
- `AlgebraicGeometry.twoTermPerfect_zero`.
- `AlgebraicGeometry.twoTermPerfect_pullback`.
- `AlgebraicGeometry.exists_twoTermDeterminantPullbackCoherence`.

Every remaining sorry in the delivery is exactly the body of one public theorem:

- `AlgebraicGeometry.exists_affineTwoTermDeterminantData`, node
  `lem-trf-affine-two-term-determinant`, module
  `Sheaf.TraceFormula.AffineTwoTermDeterminant`. This is the affine finite-projective
  good-diagram argument, including independence and arbitrary scalar extension (0FJM).
- `AlgebraicGeometry.descend_affineTwoTermDeterminantData`, node
  `lem-trf-two-term-determinant-affine-descent`, module
  `Sheaf.TraceFormula.TwoTermDeterminantAffineDescent`. This is conditional descent of
  a supplied affine cartesian system, including its compatible local normalization
  families. It does not assume a global determinant functor.

There are no sorries in definitions, private declarations, or the item module. The
predicate reexport repair has zero holes. Neither new theorem restates the original:
one constructs only affine data, and the other assumes that data and performs descent.
The assembly additionally supplies the homological characterization, all three source
membership assertions, and the normalized coherent derived comparisons by actual proofs.

## No longer needed

The generic site Tor-window route (`lem-sf-site-perfect-tor-window`, module
`Sheaf.Algebra.Homology.SitePerfectTorWindow`) is not used by this proof. The existing
finite-free residue model and residue-Betti vanishing results give the exact two-term
window directly. No new shortening or free-refinement theorem is introduced.

The bare existence theorem `exists_derivedPullbackComposition`
(`lem-pc-ringed-spaces-derived-pullback-composition`) is not used: the retained original
counits and the proved coherence theorem give the required normalized comparisons.

The item no longer imports any of the following proof modules directly:

- Sheaf.Algebra.Homology.SitePerfectTorWindow.
- Sheaf.Algebra.Homology.BoundedAboveFlatRingedSpaceKFlat.
- WeilConjectures.RingTheory.FiniteProjectiveStandardFreeCover.
- Mathlib.Algebra.Homology.HomotopyCategory.KProjective.
- Mathlib.Algebra.Homology.DerivedCategory.KProjective.
- WeilConjectures.Algebra.Homology.BoundedFlatKFlat.
- WeilConjectures.AlgebraicGeometry.AffineQCohDerivedEquivalence.
- WeilConjectures.AlgebraicGeometry.AffineDerivedPullbackTensorTilde.
- Mathlib.AlgebraicGeometry.Sites.Fpqc.
- Mathlib.RingTheory.Spectrum.Prime.Topology.
- Mathlib.RingTheory.Ideal.Span.
- WeilConjectures.AlgebraicGeometry.Descent.
- WeilConjectures.AlgebraicGeometry.FlatComplexDerivedPullback.
- WeilConjectures.AlgebraicGeometry.DerivedPullbackComposition.
- Sheaf.SecTraceFormula.SurjectiveTwoTermDeterminantCalculus.

The finite-projective, K-projective, affine-equivalence, kernel-calculus and descent
inputs remain necessary in the two new nodes' proof plans. They are not claimed as
mathematically pruned. The new holed modules have only the public imports their statements
need; their future proofs must import the declared inputs they actually use. Redundant
KFlatResolution and KFlatDerivedTensorComparison proof imports were also removed from
the Tor-window module after compilation established that the selected source helper
imports already provide its exact dependencies. No Lean module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The data definitions were in the same module as their existence theorem, preventing
independently stated algebra/descent subresults from using them without a cycle. They
are relocated verbatim, with the original public interface preserved.

Two independently owned definitions had the exact same public name for derived tensor
vanishing. Their bodies are definitionally equal, but Lean rejects importing both
owners. The reexport repair is necessary to combine the existing residue-model and
open-locality arguments.

The affine descent interface needs natural model comparisons, not only a list of
objectwise isomorphisms. The explicit affine-test families and their equations record
what the pure-wedge scalar-extension argument provides and what gluing uses.

The generic exact-functor natural-isomorphism helper in the source defaults to the
category hom universe. The Tor-window proof lifts its local comparison through
localization directly, retaining the statement's independent derived-category universe.

No target statement, mathematical definition, blueprint unit, or adopted source
signature is changed. All new nodes remain below the same determinant auxiliary and
preserve the unit's route.

## New nodes

`def-trf-two-term-determinant-data` records the exact relocated model, local object
condition and full determinant data definitions.

`lem-trf-two-term-perfect-tor-window` records the proved equivalence, membership of
models and zero, and arbitrary derived pullback preservation.

`lem-trf-two-term-determinant-pullback-coherence` records the proved section normalization,
identity laws and associativity with the original K-flat counits.

`def-trf-affine-determinant-interfaces` records the affine cartesian system and the
compatible local exterior, zero and evaluation families, together with the global
functor/comparison record relative to fixed coherence.

`lem-trf-affine-two-term-determinant` isolates the genuine affine good-diagram construction
of Stacks 0FJM. It retains the finite-projective and surjective-calculus dependencies.

`lem-trf-two-term-determinant-affine-descent` isolates the conditional affine descent
argument of 0FJX--0FJY, with its explicit compatibility hypotheses. It retains descent,
affine restriction/tensor and flat-model pullback dependencies.

The original node's proof/dependencies now match the assembly proof; the tensor-vanishing
node points at the identical adopted definition. No DAG node or quarantine archive is
removed. The two change records are listed under What changed.

## Second reading by G2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
