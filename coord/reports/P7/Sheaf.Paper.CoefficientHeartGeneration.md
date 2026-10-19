## What changed

Proved `AlgebraicGeometry.ProEtale.coefficientHeart_generation` with its original signature.
Its forward implication constructs a finite tower from bounded cohomology and substitutes
finite sheaf-filtration witnesses. Its reverse implication uses constructibility of each
lisse extension and induction over the explicit finite witness, with the existing
triangulated coefficient theorem. Private, proved bookkeeping lemmas concatenate lists,
append cones, and substitute witnesses.

All three supporting declarations introduced in this delivery are now proved.
`DerivedCategory.bounded_cohomology_cone_witness` uses successive truncation triangles,
signed inverse rotation and induction on the finite interval between cohomology bounds.
`AlgebraicGeometry.ProEtale.coefficientHeart_lisse_extension_constructible` uses open-closed
recollement and finite constant scalar models, then computes degree-zero cohomology.
`AlgebraicGeometry.ProEtale.coefficientHeart_sheaf_cone_witness` uses the existing common
stratification and counit-image filtration theorems, short exact sequence triangles,
inverse rotation and finite induction. No existing statement or definition was changed.

## Proved and sorry left

Closed the one original direct hole:

- `AlgebraicGeometry.ProEtale.coefficientHeart_generation`
  (`det-cor-coefficient-heart-ii-generation`).

The supporting declarations have no direct holes:

- `DerivedCategory.bounded_cohomology_cone_witness`
  (`lem-sfb-bounded-cohomology-cone-witness`).
- `AlgebraicGeometry.ProEtale.coefficientHeart_lisse_extension_constructible`
  (`lem-sfb-coefficient-heart-lisse-extension-constructible`).
- `AlgebraicGeometry.ProEtale.coefficientHeart_sheaf_cone_witness`
  (`lem-sfb-coefficient-heart-sheaf-cone-witness`).

Holes closed in the original module: 1 of 1. Holes added: zero. Remaining direct holes
in this delivery: zero. These proofs use the existing named stratification, filtration,
recollement, triangulated and truncation declarations; some dependencies remain unproved
in the library. No axiom, hollow definition or arbitrary data chosen from an unproved
existence theorem is introduced.

## No longer needed

Removed these direct proof imports from the assigned module:

- `Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed`
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`
- `Mathlib.AlgebraicGeometry.Noetherian`
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`
- `Sheaf.Paper.CoefficientHeartCommonStratification`
- `Sheaf.Paper.CoefficientHeartFiltration`
- `Mathlib.Algebra.Homology.DerivedCategory.ShortExact`
- `Sheaf.CategoryTheory.TruncationsAndHomotopyColimits`
- `WeilConjectures.CategoryTheory.TruncationTriangle`
- `Sheaf.Paper.CartesianCoefficients`
- `Sheaf.Paper.CondensedConstantConstructibility`

The geometric, filtration and truncation arguments are used through the three proved
supporting declarations. Their node edges have been transferred accordingly. In particular,
the source-library truncation triangle and existing filtration/common-stratification results
remain used. These import removals are not claims of global module pruning. The generator
calculation uses the existing condensed recollement theorem, vanishing pullback lemma and
constructibility under isomorphism. The generic cohomology proof uses the existing successive
truncation triangles directly, so no additional homotopy-colimit construction is needed.

Removed the parent's obsolete three `tool_uses` entries for ringed open-closed,
successive truncation and Noetherian-open tools. The directly used triangulated assertion
remains in `proof_deps`. No blueprint unit statement or step is bypassed.
No globally pruned module is claimed.

## Where the brief, the DAG or earlier work was wrong

The existing `coefficientHeart` theorem assumes a finite-type scheme over a field, whereas
generation is stated for every Noetherian scheme. The proof instead uses the existing
common-stratification and filtration declarations, whose Noetherian interfaces fit.
The existing triangulated assertion uses canonical coefficient presentations; a private
proved helper transports the supplied field hypothesis to those presentations.

Earlier attempts hit definitional-comparison timeouts while reconstructing strata and
specializing the image filtration. A generic predicate on schemes and immersions provides
an efficient forgetful stratification adapter, and proved private helpers keep each
comparison local. The remaining timeout came from unfolding the extension functor for
the zero object in a specialized coefficient context. A generic, proved zero-preservation
lemma avoids that unfolding. No dependency definition change or higher time limit is used.
Profiling and intermediate experiments remain only in the scratch directory.

Edge cases checked: empty schemes and strata, zero lisse modules, empty or non-strict
filtrations, zero successive quotients, acyclic complexes, and crossing cohomology bounds.
The zero-object generator and the same finite induction handle each case. No false
statement was identified.

The continuation on 2026-10-19 checked all four proof files and the recorded DAG steps
against the current sources and blueprint. The original theorem signature is byte-for-byte
unchanged, every delivered proof has zero direct holes, and every node's proof dependency
list equals the union of its steps' uses. The required dry run succeeded at commit
`5758422fd0`: all four modules compiled and the server preflight passed. Earlier compile
service failures are resolved for this verification. No global module pruning is claimed.

## New nodes

`lem-sfb-bounded-cohomology-cone-witness`, in
`Sheaf.CategoryTheory.DerivedCategory.BoundedCohomologyConeWitness`, records the proved
coefficient-independent cohomology tower for the Complexes paragraph.

`lem-sfb-coefficient-heart-sheaf-cone-witness`, in
`Sheaf.Paper.CoefficientHeartSheafConeWitness`, records the proved finite construction for
one shifted constructible sheaf, using the Single sheaves paragraph.

`lem-sfb-coefficient-heart-lisse-extension-constructible`, in
`Sheaf.Paper.CoefficientHeartLisseExtensionConstructible`, records the proved generator
membership calculation in the Converse paragraph.

Each node records its source, proof, actual logged searches and verbatim Lean signature.
All three are needed by the generation proof and have zero direct holes. No change record
is required because no existing signature, definition or public import was changed.

## Second reading by P7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
