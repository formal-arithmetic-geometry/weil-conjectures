## What changed

Implemented `SheafOfModules.ringedSitePerfectProjectionFormula` with its original signature.
The proof works on the covering sieves in the recorded perfectness predicate, handles
finite-free retracts (including rank zero), applies the existing proved bounded-complex
triangulated devissage, and detects arbitrary derived isomorphisms through K-injective
representatives and local homology. All helpers for these steps are proved private lemmas
in the item module. The unit calculation is derived from `ringedProjectionMateExact`;
it is not part of the remaining local comparison assumption.

Added the proved module `Sheaf.Paper.RingedTensorEdgeInducedAdjunction`. It constructs
the ring datum from the edge, obtains the induced module direct image, and compares it
with the supplied right adjoint, including the normalized Hom equation and both unit
and counit identities. Two additional proved private helpers in the slice module compare
total left derived functors across an ordinary pullback isomorphism, with the comparison
fixed on every cochain representative, and preserve the
counit under the induced comparison of right adjoints. This implements the ordinary adapter at the start of locality.

Added `Sheaf.Paper.ProjectionMateSlicePresentation`, with transparent abbreviations for
ordinary slice modules and exact derived restriction, a local comparison record, and a
separate locality theorem. This theorem concerns arbitrary coefficients and does not
assume perfectness or assert a projection-formula isomorphism. Its equation compares the
actual specified counit mate, not an arbitrarily chosen map. The item uses the comparison
equation, local exactness and shift compatibility to finish the finite and covering
arguments. Existing public imports and signatures remain unchanged.

## Proved and sorry left

Closed the original hole in `SheafOfModules.ringedSitePerfectProjectionFormula`
(node `lem-sbc-ringed-site-perfect-projection-formula`). Its proof is complete Lean from
the imported statements, with no internal holes. The new helpers `map_to_kInjective`,
`quasiIso_local`, `derived_iso_local`, `projection_unit_iso`, `restriction_unit_iso`, and
`strictPerfect_iso` have complete proofs.

Also proved `SheafOfModules.RingedTensorEdge.inducedModuleAdjunction`
(node `lem-sbc-ringed-tensor-edge-induced-adjunction`), with no added hole. The private helpers `edge_left_derived_comparison` and
`derived_counit_comparison` in the slice module also have complete proofs.

Added one hole, `SheafOfModules.projectionMateSlicePresentation`
(node `lem-sbc-projection-mate-slice-presentation`). This is precisely the adapter from
the existing arbitrary ringed-topos sheaf-slice comparisons to the `RingedTensorEdge`
projection interface, including independently chosen derived Hom universes. Its source
and complete proof in words are in its docstring and node. The finite devissage, unit
normalization, perfectness covering argument and local detection are outside this lemma
and are implemented in the item.

Thus: one original hole closed, one strictly separate hole added, zero holes left in the
item, one hole in the delivery. Among the changed declarations this is a decomposition with net hole reduction zero,
not a claim that the whole target import closure is now sorry-free.

Validation: `lcompile.py --all` compiled all three sandbox modules in import order.
The final slice module took 8.5 seconds and the item 12.8 seconds; no compiler errors
remain. The original signature and public imports are unchanged, the import-direction
checks pass, and every proof-dependency list equals the union of its steps.

## No longer needed

Removed these direct proof imports from the item:

- `Mathlib.Algebra.Homology.HomotopyCategory.DegreewiseSplit`
- `Mathlib.CategoryTheory.Triangulated.Pretriangulated`
- `Sheaf.CategoryTheory.ElementRestrictionHom`
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`
- `Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`

`ElementRestrictionHom` and `RingedTopoiCanonicalTensorPullbackOfUniverses` are now
imports of the local presentation lemma, so they remain needed transitively. The generic
bounded-complex theorem replaces a fresh stupid-tail induction: the item has no direct
proof dependency on `lem-weil-pbc-degreewise-split-derived-triangle` or
`lem-sf-triangle-morphism-iso`. Its local detection proof uses short-complex homology and
the quasi-isomorphism criterion for Q, rather than the original nodes
`lem-weil-pbc-exact-functor-complex-cohomology` and
`lem-weil-pbc-unbounded-derived-iso-cohomology`. These are removals of direct dependency
edges, not assertions that all those modules are globally unused. No module is withdrawn.
All four original approved tool uses remain relevant, directly or through the slice
presentation theorem, and their order and metadata are preserved.

## Where the brief, the DAG or earlier work was wrong

The planned slice argument uses two different presentation APIs. The stated sheaf-slice
comparison takes a `RingedToposMorphism` with normalized induced module direct image;
the assigned theorem uses `RingedTensorEdge` with an algebraic inverse-image lift and a
chosen total-derived model. It also permits a global derived Hom universe unrelated to
the standard universe of the ordinary slices. The supplied comparisons therefore cannot
be applied by a direct specialization. The new local presentation statement makes this
adapter and its precise arrow equation explicit. This is an interface gap, not a claim
that the original mathematics is false.

The existing proved `bounded_complex_mem_triangulated` already supplies the planned
bounded induction, as the item's earlier review suggested. Reusing it avoids proving
its triangle argument again. The unit `sk-rem-rest` has no prescribed realized steps to
bypass, and no target statement or existing definition is changed.

Edge cases checked in the proof: zero ranks use the empty finite product; reversed or
empty bounds are handled by bounded devissage; bounds and ranks are chosen independently
on each cover member; the indexing family covers each original object; the source object
is unbounded; and local detection applies to arbitrary derived arrows after a
K-injective replacement. The new comparison lemma has no boundedness, flat structural
map, representability of inverse images, or site-functor hypothesis. Empty slices and
zero rings are allowed.

## New nodes

`lem-sbc-projection-mate-slice-presentation` records the local exact presentation and
actual counit-mate restriction equation from Stacks 0944 and 04IF. Its statement,
source, proof steps, existing dependencies, three logged search kinds, blueprint
ancestry and Lean declarations are recorded. It is a separate result with no
perfectness hypothesis; it does not rename or repackage the assigned conclusion.
The assigned node's proof, proof dependencies and proof origin now describe the Lean
argument. No existing statement or definition changes, hence no change record or forced
consumer adaptation is needed.

`lem-sbc-ringed-tensor-edge-induced-adjunction` records the fully proved ordinary
adapter used in the locality argument: induced direct image, normalized scalar-extension
adjunction, and its comparison with the supplied adjunction. Its ring datum is a real
construction; no object is chosen from a holed existence theorem.

## Second reading by M2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
