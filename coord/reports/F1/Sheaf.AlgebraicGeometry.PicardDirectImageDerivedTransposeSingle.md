## What changed

Simplified the private transposeFromHomology proof in
lean/Sheaf/AlgebraicGeometry/PicardDirectImageDerivedTransposeSingle.lean.
The derived-adjunction compatibility equation now rewrites directly using the
recovered single-morphism equality, eliminating an intermediate congrArg
calculation and redundant equation chaining. The explicitly typed recovery
of the ordinary morphism is retained to keep elaboration bounded.

The full original theorem remains in the live library. Its signature, proof,
hypotheses, universes, canonical morphisms, imports and documentation are
unchanged. Updated only lean.by, lean.date and lean.note on the existing node
lem-sc-picard-direct-image-derived-transpose-single; its proof route, dependencies,
source and unit route are retained. Change record:
coord/changes/F1-picard-derived-transpose-single-restoration.md.

Searches found Mathlib's singleFunctorCompHomologyFunctorIso and
Functor.map_preimage, already used by the proof, and no replacement for this
pinned Picard comparison. The original complete proof compiled in 34.0 seconds,
then in 46.0 seconds with #print axioms, which reported exactly propext,
Classical.choice and Quot.sound. The consumer inventory includes quarantined
sources: one direct importer and sixteen consumers in total. No consumer is
adapted. The final proof compiled cleanly in 57.1 seconds through lcompile; the delivery
probe checks the final declarations again.

## Proved and sorry left

The original source was already fully proved; this is a zero-hole repair and
proof simplification. The complete theorem
AlgebraicGeometry.Scheme.picardDirectImageDerivedTranspose_single realizes
lem-sc-picard-direct-image-derived-transpose-single. Its private helper
AlgebraicGeometry.Scheme.transposeFromHomology is also fully proved.

Original holes: 0. Holes closed: 0. Holes added: 0. Sorries left: none.
No statement is split off; the net hole count change is zero.

## No longer needed

None. The public PicardDirectImageDerivedTranspose import, private
CanonicalSingleAdjunctionTranspose and CanonicalDirectImageH0Unit proof imports,
and all recorded statement and proof dependencies remain necessary. The sole
parent still uses the theorem in its quarantined proof. No module, declaration,
node or dependency is withdrawn or pruned.

## Where the brief, the DAG or earlier work was wrong

The item began absent from lean/, with a fully proved quarantine archive. The
shared library independently restored the identical source during this session;
the first delivery therefore correctly failed preflight as unchanged. The final
packet retains that complete source and makes the private proof simplification
above. No new hole closure or mathematical statement correction is claimed.

The original quarantined direct consumer PicardDirectImageUnitMorphismPullback
has a separate upstream-sync name-resolution failure at line 35: inside
namespace Modules, unqualified derivedPullback resolves to
Scheme.Modules.derivedPullback, whereas canonicalSinglePullbackMap uses
AlgebraicGeometry.derivedPullback. This produces a Type v versus Type (v + 1)
morphism mismatch before either use of this theorem. A scratch-only copy
explicitly qualifies AlgebraicGeometry.derivedPullback in this private helper,
and then compiles in 42.8 seconds with both original theorem applications.
Its original factorization and pasting dependencies also compile. This consumer
is not adapted or restored by this delivery; its own quarantined rework remains
necessary. The quarantine archive is preserved.

## Second reading by F1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
