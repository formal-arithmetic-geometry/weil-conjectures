## What changed

Proved `AlgebraicGeometry.exists_projective_modification_of_isAffine_isNoetherian`
in `Sheaf.AlgebraicGeometry.NoetherianChowModification` with its signature unchanged.
The proof follows all three existing DAG steps: eliminate
`ChowModification.nonempty_data f`, prove the supplied immersion proper using
`IsProper.of_comp`, make it closed using
`IsClosedImmersion.of_isPreimmersion`, and package the embedding as
`IsHProjective`, then `IsProjective`. The dense open and its isomorphism are
retained from the same Chow datum. No definition or statement was changed,
and no new choice of data was defined.

The final pruned-import version compiled successfully through `lcompile.py`.
A temporary `#print axioms` check reports exactly `propext`, `Classical.choice`,
and `Quot.sound`; the check command was removed from the delivered source.
The original DAG proof, proof dependencies, and unit route remain accurate,
so no node change is needed. The proof also covers empty schemes without
requiring a nonempty dense open or a nonempty homogeneous-coordinate type.

## Proved and sorry left

Closed one original hole:
`AlgebraicGeometry.exists_projective_modification_of_isAffine_isNoetherian`
(node `lem-fin-noetherian-chow-modification`).

Holes left in the item: zero. Holes added: zero. Split-offs: zero.
The theorem has only the three permitted axioms, including its dependencies.

## No longer needed

Removed these redundant proof imports:

- `WeilConjectures.AlgebraicGeometry.ProjectiveSpace`
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`

Their required declarations and instances are already available through the
retained public statement imports and the proof import
`WeilConjectures.AlgebraicGeometry.ChowLemma`. All declared DAG proof
dependencies are still used, directly or through the projectivity/properness
API. No DAG node or module becomes unnecessary in the mathematical argument;
no unit statement or proof step is bypassed.

## Where the brief, the DAG or earlier work was wrong

No mathematical defect was found. The library also contains the stronger
`AlgebraicGeometry.exists_projective_modification` in
`WeilConjectures.AlgebraicGeometry.ChowLemma.ProjectiveModification`, which
returns a closed embedding explicitly. No additional import of that theorem
was necessary: the existing declared Chow datum and the planned properness
argument already give a short complete proof. The finite homogeneous
coordinate type in the actual Chow interface replaces the natural-number
index in the prose; this is the canonical projective-space convention used
by `IsHProjective`.

## Second reading by N3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
