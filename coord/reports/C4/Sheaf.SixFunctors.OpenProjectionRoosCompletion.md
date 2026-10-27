## What changed

Replaced the single hole of `WeilConjectures.OpenProjectionRoos.openProjectionRoosCompletion`
by an assembly of three separate construction steps. The original public interfaces are
moved to `Sheaf.SixFunctors.OpenProjectionRoosCompletionData`, publicly reexported
by the original module. This avoids an interface/proof import cycle. Three representative
clauses are named `OrdinaryRepresentative`, `CompletedRepresentative` and
`RestrictionRepresentative` to bound elaboration. Expanding these three names restores
the original CompletionData body byte for byte. Existing signatures, universes and
mathematical statements are unchanged. The change record is
`coord/changes/C4-open-projection-roos-interface-extraction.md`.

The assembly proves exactness of ordinary restriction using exact slice restriction and the
coefficient equivalence. Good-to-flat conversion uses the existing K-flat equivalence;
extension preservation uses `m.kflat` and `m.preservesFlatTerms`. After applying the ordinary
and completed comparison construction steps, the proof constructs the completed restriction
isomorphism explicitly by whiskering Gamma with restriction and composing with the inverse
actual open unit, including the functor associator and right unitor. Its component equation
is verified by the natural-isomorphism component formulas. The third step supplies its
strict finite representative normalization. The proof packages every original witness and
every original equation, without discarding any CompletionData clause.

## Proved and sorry left

Original holes: one, `WeilConjectures.OpenProjectionRoos.openProjectionRoosCompletion`.
Its body is replaced by complete Lean assembly. Three strictly smaller construction holes
are added, so this is a decomposition, not a net proof of the target closure:

- `WeilConjectures.OpenProjectionRoos.openProjectionOrdinaryRoos`
  (`lem-sf-open-projection-ordinary-roos`): transport the existing normalized Roos comparisons
  to the global coefficient presentation, invert the actual units, preserve good complexes
  under restriction, and descend the ordinary tensor projection. This concludes no completed
  tensor comparison, chi square, or completed restriction normalization.
- `WeilConjectures.OpenProjectionRoos.openProjectionCompletedSquare`
  (`lem-sf-open-projection-completed-square`): construct Gamma and descend the strict
  augmentation limit square, including invertibility of both actual chi maps. Ordinary
  descent and the extension Roos comparison are inputs. This concludes no restriction
  Roos comparison, open-unit comparison or restriction identity.
- `WeilConjectures.OpenProjectionRoos.openProjectionRestrictionNormalization`
  (`lem-sf-open-projection-restriction-normalization`): given Gamma's strict representative
  equation and both actual open units, identify the canonical restriction comparison with
  the restriction Roos comparison of the same strict quotient towers. This neither constructs
  Gamma nor proves its chi square or chi invertibility.

There is no other sorry in the five delivered Lean files; in particular none in a definition
or private declaration. One upper hole is closed and three lower holes are added (net -2).
The three statements have complete proof plans, sources and their own modules and nodes.
The final lcompile.py --all batch compiled all five files successfully with no diagnostics.

Edge cases checked: empty and identity open immersions, zero factors, unbounded complexes,
negative and odd complex degrees, and index zero representing exponent one. The restriction
step is independent of finite-field hypotheses. Its comparisons are fixed by both signed
coordinates, so their unit compatibility does not assert uniqueness of arbitrary maps out
of a derived limit. The completed-square step uses the actual augmented strict square and
its representative equation, including all quotient transitions; it does not detect equality
by finite evaluation alone. No Tor condition over a finite quotient is added.

## No longer needed

No module is withdrawn and no adopted source-library declaration is changed. No whole-library
module pruning is claimed. The public imports are retained through the extracted data module.

The item no longer directly imports these former proof imports:
`Sheaf.AlgebraicGeometry.ProEtaleRingedOpenExtensionProducts`,
`Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact`,
`Sheaf.CategoryTheory.StrictRoosComparison`,
`Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous`,
`Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits`,
`Sheaf.SixFunctors.OpenFactorTensorModel`,
`Mathlib.AlgebraicGeometry.Noetherian`, and
`Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`.

The exact-product, quotient augmentation, ordinary normalization and restriction-unit
arguments remain necessary below the new construction steps, not pruned from the mathematical
argument. Their original dependency nodes are recorded in the new nodes. The original item
now cites those construction steps and the semilinear comparison used directly for extension
preservation. `def-exchange-projection` is not needed as a proof step: the statement asserts
only the completed open tensor component, with no independent proper-operation data.
Its existing public import and original statement dependency remain available unchanged.

## Where the brief, the DAG or earlier work was wrong

The DAG's three existing construction packages use interfaces that do not directly assemble
into CompletionData. `SfOpenRoos.comparison` and `restriction_unit` use the ringed slice at
U and arbitrary derived-limit localization functors, whereas the consumer specifies the
global U coefficient category and the explicit integralOperationsRoosFunctor chain model.
`openTensorAugmentationLimitSquare` is a statement on a good representative pair and a
supplied normalized lambda; the consumer additionally needs natural descent on all
constructible pairs. These transports and descents are isolated as genuine construction
steps, rather than silently inferred from the old signatures.

The public CompletionData interface and existence theorem originally occupied one module.
The interface must precede the new statement modules to avoid an import cycle; its extraction
preserves the original declarations, with the three definitionally identical representative
clause names described above. A source search and downstream.py found no current
Lean importers or external uses of these declarations. This is not a withdrawal: the original
module and original theorem remain, and parent DAG dependencies remain valid.

The first assembly drafts exposed a restriction-universe inference ambiguity and expensive
unfolding during elaboration. Explicit universes and bounded local transparency are used in
the proof environment; there is no raised compile time limit or split to evade that limit.

## New nodes

`def-sf-open-projection-roos-completion-data` records the unchanged public interface extracted
from the item: signed Roos comparison specification, pair functors, CompletionData and Completion.
It also records the three named representative predicates; each is exactly the original
clause. It introduces no replacement construction and has zero holes.

`lem-sf-open-projection-ordinary-roos` isolates ordinary tensor descent and global/slice
transport of the two signed Roos comparisons and actual units. Its source is Stacks 09BP,
03DI and 0GL1 and the existing ordinary normalization dependencies.

`lem-sf-open-projection-completed-square` isolates descent of the actual augmented square
through the completed tensor presentations. Its sources are Bhatt--Scholze 6.5.5 and 6.5.8,
Stacks 0940, and the existing openTensorAugmentationLimitSquare statement.

`lem-sf-open-projection-restriction-normalization` is the remaining strict tower/open-unit
calculation. Its sources are Stacks 09BP and 0941 and the existing restriction_unit statement.

Searches used LeanFinder, Loogle, LeanSearch, and grep in Mathlib, WeilConjectures and Sheaf.
They found ordinary exactness and product APIs, but no declaration giving the simultaneous
normalized construction. Stacks proetale.tex, the current blueprint open-factor paragraph,
and Bhatt--Scholze PDF pages 49--50 were read. The change-record path is given above.

## Second reading by C4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
