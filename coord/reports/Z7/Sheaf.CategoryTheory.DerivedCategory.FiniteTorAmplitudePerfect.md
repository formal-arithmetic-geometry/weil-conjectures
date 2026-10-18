## What changed

Completed the proof of
`DerivedCategory.finiteTorAmplitude_iff_perfect_iff_finiteFree` in
`Sheaf.CategoryTheory.DerivedCategory.FiniteTorAmplitudePerfect`, preserving its complete
signature, universes, hypotheses and both conclusions. No other Lean module changes.

The coefficient ring is finite, hence Noetherian. The recorded DVR witness gives the local
integer ring and its maximal ideal. Since the positive power of that ideal is proper, its
quotient is nontrivial and local. Bounded finite cohomology gives pseudo-coherence through
`isPseudoCoherent_iff_boundedAbove_finite_homology`; the stated
`isPerfect_of_pseudoCoherent_finiteTorAmplitude` then supplies the perfect representative.
Pointwise finite projectivity implies flatness and then freeness over the local ring.
The same complex already satisfies the requested finite-free predicate, so transporting
its differentials to chosen standard modules is unnecessary.

For the converse, projective terms are flat and the existing proved source theorem
`DerivedCategory.torAmplitudeIn_Q_obj_of_flat` gives the Tor interval. Transport it to C
and widen its lower endpoint to `min a b`, ensuring an ordered interval even for an empty
original support interval. This directly handles the zero complex. The testing module is
arbitrary and is never assumed flat. Free terms are projective, giving the other direction
of the second equivalence.

Added a DAG record for the ordinary-module specialization of that already proved generic
source theorem. It introduces no Lean declaration or proof obligation. Updated the item's
proof, proof dependencies and proof origin, and removed obsolete direct tool approvals.
The unit's commutative-algebra route is unchanged. All original public imports remain.
New proof imports are `Mathlib.RingTheory.Noetherian.Basic` and
`WeilConjectures.CategoryTheory.Abelian.Flat.ModuleCat`.

Single-file `lcompile.py` validation passed repeatedly, most recently in 2.7 seconds,
with no warnings or errors. The initial sandbox-wide `--all` attempt encountered a busy
compile server; subsequent single-file compiles completed normally. The delivery gate
performs its own compile and axiom/sorry probe.

## Proved and sorry left

Closed the one original hole in
`DerivedCategory.finiteTorAmplitude_iff_perfect_iff_finiteFree`
(node `lem-trf-finite-tor-amplitude-perfect`). There are zero remaining direct holes in the
item and zero holes added anywhere. No theorem is split off. This is a completed proof
from the existing library interfaces, not a decomposition into new unproved statements.
Dependencies retain their existing proof status; no claim about closing their transitive
holes is made.

## No longer needed

Removed these proof-only imports:

- `Mathlib.Algebra.Module.Projective`: its interface is already available through the
  public perfect-ring definition import.
- `Mathlib.RingTheory.Noetherian.Defs`: replaced by `Mathlib.RingTheory.Noetherian.Basic`,
  which provides the finite-ring Noetherian instance used in the proof.
- `Sheaf.RingTheory.RingPseudoCoherent`: already exported by the imported Noetherian
  cohomology criterion.
- `Sheaf.Algebra.Homology.BoundedFlatKFlat`: its separate acyclicity wrapper is unnecessary;
  the proved source bounded-flat Tor theorem directly supplies the needed consequence.
- `WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat`: the proof no longer manipulates
  the K-flat predicate directly.

The direct proof dependencies `lem-pc-module-bounded-flat-kflat`,
`def-pc-module-kflat-complex`, and `lem-pc-source-kflat-module-tensor-model` are replaced in
the item's route by `lem-trf-source-bounded-flat-tor-amplitude`, recording the proved source
helper. The helper's record explains the underlying K-flat argument and cites the more
specific existing `lem-weil-pbc-source-kflat-tensor-single-model`. Its recorded source
proof is already complete. Other users of these nodes are unaffected; this does not
assert their global unreachability. Removed the item's obsolete tool-use entries for
`lem-pc-module-bounded-flat-kflat` and `lem-pc-source-kflat-module-tensor-model`.

The finite-basis change, transported differentials, and a new complex with standard free
terms in the old proof plan are not needed: the conclusion requests freeness as a property
of the existing terms. No separate node or module for those constructions is introduced.
No library module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

There is no error in the assigned Lean statement or its dependency interfaces. The
existing DAG already corrects the blueprint's insufficient inference of pseudo-coherence
from 0-pseudo-coherent cohomology: the Noetherian cohomology criterion is the interface
actually used. We checked Stacks `lemma-Noetherian-pseudo-coherent`, clause (2),
`lemma-perfect`, `lemma-derived-tor-quasi-isomorphism`, `definition-tor-amplitude`, and
`lemma-tor-amplitude`, as well as the current blueprint's item and unit proofs.

The current blueprint's illustrative residue-field resolution with every differential
multiplication by the uniformizer is not a valid resolution for general n: consecutive
maps multiply by the square of the uniformizer, which need not vanish. For n = 1 the
quotient ring is a field and its residue field is already free. That warning example is
not part of the assigned theorem and is not used. No statement or definition was changed.

The earlier plan's basis transport is redundant for the actual Lean conclusion, and its
separate K-flat/tensor argument is already proved by the existing source helper. The new
node records its ordinary-module use explicitly; the other node already attached to that
same generic declaration, `lem-kun-flat-bounded-tor-amplitude`, states a geometric sheaf
specialization and is not silently applied as an ordinary-module assertion.

`Padic.extension_integers_dvr` is used as a generic coefficient-ring data theorem (node
`lem-weil-l-adic-extension-integers-dvr`); this preserves the unit's stated ring-theoretic
argument and does not replace any geometric step. No forced adaptations or change
records are needed.

## New nodes

`lem-trf-source-bounded-flat-tor-amplitude` records the ordinary-module specialization of
`DerivedCategory.torAmplitudeIn_Q_obj_of_flat` in
`WeilConjectures.CategoryTheory.DerivedCategory.FlatModel`. The source proof is complete;
there is no new Lean file, new declaration, or sorry. Its support interval may be empty,
and neither finite generation nor any flatness of the test module is required. The
blueprint search found the related geometric node
`lem-kun-flat-bounded-tor-amplitude`; its statement concerns sheaves on a scheme, rather
than arbitrary ordinary module complexes. Actual LeanSearch, Loogle and Mathlib grep
queries are recorded, with the existing source result selected. The node is placed under
the assigned item's own chapter and unit and maps to the blueprint's (If) implication.

## Second reading by Z7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
