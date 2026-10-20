## What changed

Proved `AlgebraicGeometry.Scheme.closedPointSheaf_filteredColimit_finiteSupport`
with its original signature unchanged. Two new, fully proved supporting modules separate
the filtered-colimit argument from the finite-support and closed-immersion argument.
All proof-only imports are private imports; existing public imports and definitions stay
unchanged. The parent node now records the two actual proof dependencies.

The filtered-colimit proof constructs free sheaf generators using adjunctions, proves
closure under finite joins, and identifies the colimit by a monomorphism and local
surjectivity. The finite-support proof uses generic points of the closed nonvanishing
loci upstairs, then the kernel of restriction to an open complement. The reduced
support is constructed with `IdealSheafData.vanishingIdeal`.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Scheme.closedPointSheaf_filteredColimit_finiteSupport`: 1 of 1.
Added zero holes. Also proved both new supporting declarations:

- `AlgebraicGeometry.Scheme.closedPointSheaf_finitelyGenerated_filteredColimit`
  (`lem-kun-cp-filtered-colimit`);
- `AlgebraicGeometry.Scheme.closedPointSheaf_finitelyGenerated_finiteSupport`
  (`lem-kun-cp-finite-support`).

No `sorry` remains in any of the three delivered modules. No unfinished result is split
off. All three compile cleanly through `lcompile.py --all`. The existing
closed-immersion essential-image declaration is used as allowed by stage 3; this does
not claim that every imported proof in the library is already free of holes.

## No longer needed

Removed these direct proof imports from the parent module:

- `Sheaf.AlgebraicGeometry.ClosedPointField`;
- `Sheaf.AlgebraicGeometry.EtaleLfpAndFiniteType`;
- `Sheaf.AlgebraicGeometry.EtaleSupport`;
- `Sheaf.AlgebraicGeometry.FiniteClosedPoints`;
- `WeilConjectures.AlgebraicGeometry.GeometricStalkSupport`.

The support definition remains needed through the existing public interfaces and the
new modules. Removing its redundant direct proof import does not prune its node.
The proof no longer uses these former proof-dependency nodes:

- `lem-kun-support-geometric-point-independent`: direct stalk comparison and joint
  detection of zero objects suffice;
- `lem-kun-finite-closed-subscheme` (`Sheaf.AlgebraicGeometry.FiniteClosedPoints`):
  finite generic points upstairs already give finite image downstairs;
- `lem-kun-etale-lfp` (`Sheaf.AlgebraicGeometry.EtaleLfpAndFiniteType`);
- `lem-kun-closed-point-field` (`Sheaf.AlgebraicGeometry.ClosedPointField`);
- `lem-weil-pbc-etale-residue-field-extension-separable`:
  no residue-field calculation is needed in the generic-point argument.

These are removals from this proof route; other parents may still need these nodes.
`def-kun-support` and `lem-kun-04ca` remain needed through the new finite-support node.
No unit statement or realized proof step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The current blueprint's step 2 asserts closedness of a cyclic subsheaf's support
downstairs from a local vanishing description without establishing that implication.
The formal proof works with the closed nonvanishing locus upstairs instead. Noetherian
finite generic points and closedness of their images give the needed finiteness;
the kernel argument then bounds the generated subsheaf's support. This also avoids the
older node's longer residue-field route. No statement or definition repair was needed.

## New nodes

`lem-kun-cp-filtered-colimit` records the fully proved filtered-colimit clause in
`Sheaf.AlgebraicGeometry.ClosedPointSheafFilteredColimit`, sourced from step 1 of the
approximation lemma (Stacks Tag 0F0N). The empty family and finite unions provide the
filtered category; all sections are locally covered by its generators.

`lem-kun-cp-finite-support` records the fully proved finite-support and reduced
closed-immersion clause in `Sheaf.AlgebraicGeometry.ClosedPointSheafFiniteSupport`,
sourced from steps 2-3 of the approximation lemma (Stacks Tags 03SA and 04CA).
The new statements are strict parts of the parent conclusion, and both have complete
Lean proofs. There are no change records because no existing signature or definition
changed.

## Second reading by C9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
