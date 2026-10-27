## What changed

Completed `AlgebraicGeometry.ringComplex_cech_cohomology_power_torsion` in
`lean/Sheaf/Paper/RingComplexCechCohomologyPowerTorsion.lean`, with its exact
original signature and public import. Added only private, proved helpers within
that module. No other existing module or node is changed.

The shorter route uses the already proved
`ringComplex_ordered_scalar_iso` and `ringComplex_godement_cech`.
After inverting s, the extended ideal is the unit ideal. Compare the image
list with the unit-ideal Godement object. A second application of the same
comparison, to the singleton list (1), proves that object zero: its ordered
model has only two terms, and its first differential is the isomorphism
B -> B[1/1]. This avoids a new ordered-subset contraction or Koszul comparison.

The remaining transport is proved here. Evaluation at the unique object is
an explicitly constructed equivalence with ordinary modules. The section
isomorphisms for scalar extension commute with differentials, giving the
cochain comparison to the acyclic image-list model. Exact localization commutes
with homology. The given derived isomorphism identifies the homology of the
source model with that of T. The localized-module zero criterion then supplies
the required exponent separately for each class.

The item node's proof, proof dependencies, and proof origin now describe this
argument. Sources read: Stacks dualizing.tex, Tag 0A6R,
lemma-local-cohomology-adjoint, and Tag 0ALZ, lemma-torsion-change-rings;
algebraization.tex, Tag 099D(d), lemma-all-rings. The blueprint unit statement
and route are preserved.

Validation: `lcompile.py` compiled the complete file cleanly in 6.8 seconds.
The argument includes the zero ring, s=0, nilpotent s, I=0 and the empty list,
I=top, and repeated generators. It never assumes nontriviality, a domain, or
that T itself is K-flat. All helpers construct their data explicitly.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.ringComplex_cech_cohomology_power_torsion`
(node `lem-weil-pbc-ring-complex-cech-cohomology-power-torsion`).

Proved 1 of 1 sorries; zero split off; zero holes added; zero sorries remain
in this delivery. The proof uses existing declarations of its imported modules;
it introduces no new unproved input.

## No longer needed

No original import, node, or module is removed. All three original declared
proof dependencies remain used: the ordered-model predicate, the derived-category
API, and flatness of localization. Added only the proof imports actually needed.
The redundant proposed direct import
`Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact` was removed before the
successful compile. Also removed the redundant direct localization-base-change
import, which is already exported by the flat-localization import.

The appended-generator insertion/deletion homotopy from the former proof plan
is unnecessary: the existing Godement comparison for generating lists reduces
the localized problem to the singleton list (1). No new contraction module,
Koszul-colimit comparison, or intermediate sorry is needed. No existing
upstream declaration or dependency is withdrawn.

## Where the brief, the DAG or earlier work was wrong

No false statement or definition was found. The original node and docstring
plan describe a valid direct contraction route, but they overlook the shorter
route through the existing ordered scalar isomorphism and Godement model
theorem. The node now follows the actual Lean proof. Only proof data and private
helpers change; all existing statements and definitions remain intact.

## Second reading by G2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
