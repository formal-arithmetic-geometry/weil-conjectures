## What changed

Reduced `AlgebraicGeometry.mixedSections_square_comparison_coherence`, with its signature
unchanged, to two distinct normalization steps. Added `DerivedDirectImageSquareMate`,
which identifies the pinned pullback mate with the normalized direct-image square,
and `MixedSectionsCompositionCoherence`, which gives composition of normalized mixed
Leray comparisons for a single composable path. The target proof applies the second
statement twice and combines it with the first by functoriality, inverse cancellation,
equality transport, and the definition of `schemeGlobalScalarSquareIso`.
Three proved private helpers handle categorical inverse cancellation and equality
transport of the mixed sections comparison, and composition of the two paths from a
supplied direct-image-square identity. All three helpers have complete Lean proofs. Scoped elaboration settings and explicit
comparison types avoid repeated unfolding of the derived constructions.
No existing definition, signature, or public import was changed. The new mate module
also defines `schemeNormalizedDirectImageCompIso`, the existing normalized comparison
with an explicit scheme-level type. The defining theorem determines it uniquely through
its right-derived-unit equation; it is a typed wrapper, with no postponed data.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.mixedSections_square_comparison_coherence`
(`lem-sc-mixed-sections-square-comparison-coherence`). This is a decomposition,
not a sorry-free proof of the transitive dependency closure: one upper hole closed,
two lower holes added, net minus one.

The only new holes are:

- `AlgebraicGeometry.derivedDirectImage_square_mate`
  (`lem-sc-derived-direct-image-square-mate`), in `DerivedDirectImageSquareMate`.
  It contains no sections or scalar comparison; it isolates the mate-normalization step.
- `AlgebraicGeometry.mixedSections_composition_coherence`
  (`lem-sc-mixed-sections-composition-coherence`), in `MixedSectionsCompositionCoherence`.
  It concerns one composable path and contains no square or pullback mate.

Each has its complete normalization proof in its docstring and its own DAG node.
The target module has no remaining `sorry`.

## No longer needed

Removed the original direct proof import
`Sheaf.AlgebraicGeometry.RingedSpaceDerivedDirectImageComposition`: the typed comparison
is supplied by `DerivedDirectImageSquareMate`. Its module and node remain transitively
needed, so no globally pruned module is claimed. All original mathematical dependencies
remain needed by the two normalization steps. The original public imports are preserved.

## Where the brief, the DAG or earlier work was wrong

The recorded dependencies give existence and normalization of comparisons but no
stated compatibility between the pinned pullback mate and the right-derived-unit
comparison, or composition law for the mixed Leray comparisons. Those are the two
substantive steps now separately stated. The local `literature/stacks-project` tree
is absent; the source was read at https://stacks.math.columbia.edu/tag/0D5T,
https://stacks.math.columbia.edu/tag/0D5W, and https://stacks.math.columbia.edu/tag/08HY.
The source supplies the composition and mate constructions; the explicit normalization
calculations in the new docstrings are written by this worker.

LeanFinder found generic derived-adjunction factorization lemmas, and Loogle found
`conjugateEquiv` and its structural laws; none supplies the scheme-specific normalized
comparison. Mathlib grep found no Leray/composition or derived/conjugate match.
LeanSearch returned HTTP Internal Server Error and is recorded as unavailable.
Blueprint and project searches found no duplicate of either intermediate statement.
The current unit's `realized` arrays are empty; the two original node-level proof
steps are retained as the two normalization obligations, with no unit-route bypass.

Edge cases checked mathematically: identity squares give the identity mate; zero
objects give zero component morphisms; empty schemes cause no failure. Both new
statements allow arbitrary morphisms, including nonflat ones, since they concern
composition rather than invertibility of base change. The composition theorem keeps
sheaf and module localization universes independent; the mate theorem only needs the
sheaf localization universe.

## New nodes

`lem-sc-derived-direct-image-square-mate`: the direct-image normalization of the
pinned pullback conjugate, for a commutative scheme square. Its module is
`lean/Sheaf/AlgebraicGeometry/DerivedDirectImageSquareMate.lean`.

`lem-sc-mixed-sections-composition-coherence`: the normalized mixed Leray composition
law for two successive scheme morphisms. Its module is
`lean/Sheaf/AlgebraicGeometry/MixedSectionsCompositionCoherence.lean`.
Both inherit the item's chapter and unit. No change record or forced adaptation is needed.

## Second reading by H3

1. I compared the delivered item module with the repository version. The target
   statement and all existing declaration signatures are unchanged; only the proof
   and its proof-only imports changed. The two added modules contain the split
   declarations recorded by their nodes.
2. I compiled all three delivered modules with `lcompile.py --all`. The build is
   clean. The only remaining `sorry`s are the two named split theorems, each with a
   docstring proof and a matching DAG node; no definitions contain `sorry` and no
   forbidden declarations occur.
3. I checked both split statements against their edge cases (identity and zero
   morphisms/objects, empty schemes, and nonflat maps). They are true normalization
   statements and are strictly smaller than the target: one concerns only a direct
   image mate, and the other only one composable path. Searches found no duplicate
   declaration in Mathlib or the upstream Sheaf library.
4. The target proof follows the shortest available route through the two split
   normalization steps and uses the categorical cancellation helper. The removed
   direct-image-composition import is still transitively available through the mate
   module; no unused public import remains. The DAG proof and `proof_deps` match the
   imports and declarations used by the Lean proof.
5. The unit route is preserved: the target's two normalization obligations remain
   its proof steps, and the unit's realized data is not bypassed. No statement or
   definition was changed, so no change record or forced adaptation is required.

I changed only this report section after the first reading: it records the checks
   above and the clean local compilation result.
