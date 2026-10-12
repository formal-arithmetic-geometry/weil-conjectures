## What changed

Proved `AlgebraicGeometry.finite_pushforward_derivedHom_qcoherent` without changing its
signature or any definition. The pushforward algebra's underlying module is definitionally
the pushforward of the unit module. The two finite-pushforward coherence declarations
supply coherence; the Noetherian coherence criterion supplies quasi-coherence; coherent
pseudo-coherence and `pseudoCoherentRHomQuasiCoherent` supply the remaining conclusions.
Mathlib's `DerivedCategory.Q_obj_single_obj` identifies the degree-zero presentations.

Added the proof-only import `Sheaf.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian`
and recorded `pqf-lem-coherent-ft-locnoeth` in the node's proof dependencies. Updated the
proof description to match the Lean composition. No new declaration or node was needed.
The unit record `sk-thm-picard-duality` has empty realized lists; this delivery preserves
the existing route through finite coherence and pseudo-coherent derived Hom.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.finite_pushforward_derivedHom_qcoherent`
(`lem-sc-finite-pushforward-derived-hom-qcoherent`). Added zero holes; none remain in the
item's module. This is a proof from existing stated dependencies, not an axiom-free
completion of their proofs: the imported finite-pushforward coherence, coherent
pseudo-coherence, and pseudo-coherent derived Hom declarations still contain their
existing `sorry`s. No dependency module was changed.

## No longer needed

Removed the redundant direct proof import
`Sheaf.AlgebraicGeometry.DerivedCategoryQCoherentAlgebra`: the public import of
`DerivedRHomAlgebraModule` already exposes it. This module remains needed by the statement,
so its node `def-pc-derived-category-qcoh-algebra` is retained. No entire node or module is
pruned from the required route. A separate application of
`derivedRHomAlgebraModule_underlying` and a separate restriction-of-scalars argument are
unnecessary here: `pseudoCoherentRHomQuasiCoherent` already includes both underlying
conclusions. Its module remains needed to define the functor.

## Where the brief, the DAG or earlier work was wrong

The plan's first step omitted the explicit coherence-to-quasi-coherence criterion; added
its existing node `pqf-lem-coherent-ft-locnoeth`. The planned final forgetting argument is
already a conclusion of the existing pseudo-coherent derived Hom lemma and does not need
to be repeated. The algebra/module identification needs no new transport theorem: `rfl`
closes it after substituting the algebra equality.

Searches used the launcher Lean Finder, Loogle and Mathlib grep services, plus local
searches in both library roots. The existing library statements provide the direct route.
The configured local literature source files are absent in this clone; no new sourced
statement was introduced, and the proof uses the existing declarations and their recorded
sources. Compilation through `lcompile.py` passed without warnings.

## Second reading by X3

1. The delivered module was diffed against the repository version. The theorem signature
and all existing declarations are byte-for-byte unchanged; only proof imports, proof text,
and the recorded proof route changed.
2. The module compiles with `lcompile.py`; it contains no `sorry`, definition hole, axiom,
unsafe, opaque, implemented-by, or extern declaration. An axiom probe reports only the
standard axioms and `sorryAx` inherited from already-open dependency theorems.
3. The proof is a genuine reduction through finite-pushforward coherence, the Noetherian
coherence criterion, coherent pseudo-coherence, and the existing derived-Hom theorem. The
new proof-dependency record agrees with these calls; no split-off statement was added.
4. The proof follows the existing unit route (the unit has no realized statement or step
nodes), and the proof-only import of `DerivedCategoryQCoherentAlgebra` was removed as
redundant. No target or definition was changed, and the old node's statement is intact.
5. The DAG proof steps, proof dependencies, and proof origin now match the Lean proof. The
search records and source citations were checked; no duplicate library or Mathlib statement
was introduced. Verdict: pass.

Changed during second reading: no Lean proof changes were needed; this review section and
the delivery checks were added.
