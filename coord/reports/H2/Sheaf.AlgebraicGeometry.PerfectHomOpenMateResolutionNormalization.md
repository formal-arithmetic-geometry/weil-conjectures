## What changed

Completed the proof of AlgebraicGeometry.perfectHomOpenComparison_counit_resolution
from two strictly separate intermediate obligations in new modules:
Sheaf.CategoryTheory.DerivedExactMateCompatibility and
Sheaf.AlgebraicGeometry.NormalizedDirectImageSquareUnit.
The first concerns right derivation of an ordinary mate with exact left adjoints;
the second concerns pasted units of the normalized direct-image square, with no
pullbacks, open restriction, or projection counits in its assertion.

The item proves the adjunction transport and counit assembly in Lean using three
private, sorry-free categorical helpers. It applies the existing
perfectHomOpenModuleMate_isIso and derivedDirectImage_square_mate, then combines
the new obligations using iterated_mateEquiv_conjugateEquiv and mateEquiv_counit.
The explicit comparison definitions and all existing declaration signatures are
unchanged. The new imports are proof-only. Private local instances specialize the already
shared sheaf-module derived-category and resolution instances; no new data is chosen.

Compilation keeps right-derived functors and Qh locally irreducible. The final
theorem also avoids repeated lint traversal of the large fixed adjunction data,
following the existing DerivedPushforwardSquareMateUnit module; the compiler
still checks the complete proof. The 60-second limit was not changed.

## Proved and sorry left

Closed the item's one hole:
AlgebraicGeometry.perfectHomOpenComparison_counit_resolution
(node lem-pc-perfect-hom-open-mate-resolution-normalization).
There is no sorry left in the item module.

Added two holes, each in its own module, with source and complete proof in words:

- CategoryTheory.Functor.exactMateComparison_eq
  (lem-pc-exact-left-adjoint-derived-mate-compatibility).
- AlgebraicGeometry.normalizedDirectImageSquare_unit
  (lem-pc-normalized-direct-image-square-unit).

This is a decomposition: one upper hole closed, two lower holes added, not a
sorry-free proof of the import closure. Both obligations were tested against
identity squares, zero objects and empty schemes/categories in the mathematical
argument; none requires nonemptiness or cancellation of an arbitrary unit.
The unchanged K-injective binder is retained in the original theorem.

## No longer needed

No existing public import was removed. No existing module or node is claimed
pruned from the targets' import closure. The direct representative calculation
in the old plan is replaced by the existing normalized square-mate theorem and
generic categorical transport, but its underlying pullback-composition and
K-injective-restriction nodes remain needed through those APIs. No unused
proof-only module is imported.

## Where the brief, the DAG or earlier work was wrong

The previous missing-olean failure is resolved: PerfectHomOpenModuleMate is now
published and the original item compiled before editing. Earlier scratch files
were not deliveries and contained unfinished compatibility calculations.
They are retained only under scratchpad/, outside the delivered Lean tree.

The old plan did not provide a directly usable declaration for compatibility of
right derivation with the ordinary mate, or for the pasted unit of the particular
normalized square. These are now explicit obligations. The existing
DirectImageSquareUnitTransport supplies transport of a single unit, not the
pasted-unit statement; it is a dependency of the latter, not a duplicate.
The unit's statement and route were preserved; no chapter or unit file changed.

Sources were read from Mathlib's derived-adjunction and mates files and the
Stacks Project tags https://stacks.math.columbia.edu/tag/079W,
https://stacks.math.columbia.edu/tag/0D5T and
https://stacks.math.columbia.edu/tag/08FE. LeanSearch was unavailable; LeanFinder,
Loogle and local source searches are recorded in the new nodes.

## New nodes

lem-pc-exact-left-adjoint-derived-mate-compatibility formalizes the derived
inverse-mate identity for six additive functors between four abelian categories.
Its comparison is a real construction from the existing right-derived APIs;
only its compatibility property is postponed.

lem-pc-normalized-direct-image-square-unit formalizes the pasted-unit equation
for any commuting square of schemes, using the fixed direct-image composition
comparisons. It is independent of the open restriction and projection adjunction
counits in the item's conclusion. There are no forced adaptations.

The file-local elaboration controls are recorded in
`coord/changes/perfect-hom-open-proof-elaboration.md`; they require no downstream
adaptations.

## Second reading by H2

1. I compared the delivered item module with the repository version. The target
   declaration and all existing signatures are unchanged; only proof-only imports,
   private helpers, and the target proof were added.

2. I compiled all three delivered modules with `lcompile.py --all`. They compile
   successfully. The only remaining `sorry`s are the two named split-off theorem
   declarations listed above; there are no axioms, unsafe declarations, or hollow
   definitions in the delivered files.

3. I checked both split-off statements against their Lean declarations and source
   equations. Each is a genuine intermediate obligation, strictly narrower than the
   item, with a proof description, source, and matching DAG node. The edge cases
   described in the proof comments (identity squares, zero objects, and empty
   schemes/categories) do not add hypotheses or weaken the claims.

4. I checked the proof route and imports. The item uses the two split-off results,
   the existing normalized square-mate and open-module-mate results, and the generic
   mate transport helpers. No old proof dependency or public import was removed, and
   the report records that no node was pruned.

5. The unit route remains the normalized direct-image square followed by exact mate
   compatibility and categorical counit transport; the unit and chapter records were
   not changed. The DAG proof, `proof_deps`, and `proof_origin` agree with the Lean
   proof and the new nodes carry the required metadata.

I changed only this second-reading report section after review; no Lean statement or
definition was changed.
