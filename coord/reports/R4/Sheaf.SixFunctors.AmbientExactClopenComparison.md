## What changed

Replaced the hole in `AlgebraicGeometry.ProEtale.AmbientClopen.ambientExactClopenComparisonLocalizes`
by an assembly of ordinary and simultaneous-system normalization, uniqueness, exact
adjunction normalization, localized comparison identification, and proper mate formulas.
The realization formula is proved by naturality of the mate bijection under the four
canonical bridge isomorphisms. All system arguments take place before evaluation.

Moved the comparison constructions to the publicly re-exported
`Sheaf.SixFunctors.AmbientExactClopenData` so independent localization statements can
refer to them without an import cycle. Factored restriction predicates and realization
transport through generic categorical definitions. The ordinary constructions now
operate over an abstract Grothendieck abelian coefficient category; the original
finite-ring definitions specialize these constructions to ModuleCat. Represented ordinary alpha by
`clopenMateComposite`; a proved generic calculation identifies its components with the
original associator-expanded word. No source-library file or target signature changes.
Added proved `squareLift_fst` and `squareLift_snd` equations so the sheaf compositor
identities retain the named lift instead of unfolding the scheme pullback.
The change record is `coord/changes/R4-ambient-clopen-data-normalization.md`.

Normalized the intermediate assembly theorem's realization clause to the public
`properMateFormula` predicate. Its definition is exactly the original
unit--comparison--counit equation with the same arguments. This avoids expanding the
native coefficient categories in the theorem's conclusion. All binders, the mathematical
assertion and every `Challenge.lean` target remain fixed. The interface record is
`coord/changes/R4-ambient-realization-formula-normal-form.md`.

Repair of returned head `b5a40dded7df` (reviewer C-b5a40): incorporated all four
reviewer-fixed files directly into the sandbox. `sheafNormalized` now takes the square
equation as `r ≫ i = k ≫ p`, and `Normalized` passes `h.symm`. This preserves the
published auxiliary declaration `Normalized._proof_1`, which
`AmbientUnderivedClopenPasting` names explicitly. The three generic proof uses pass
`h.symm` as well. The mathematical predicate and all existing public signatures stay
the same. The reviewer recorded this fix in the data-normalization change record.

The previous landing failed because its reviewer-fix directory named that record
`R4-ambient-clopen-data-normalization.md`, whereas the landing tool expects reviewer
record patches under a `.change.md` filename. The corrected record is now included
directly at `coord/changes/R4-ambient-clopen-data-normalization.md`, so the new delivery
requires no landing-time patch. The underived node keeps the current source's
`proof_origin: null`: the sandbox omits that update field, since an explicit null
would instruct deliver3.py to delete it. All other unowned fields match current source.

Fresh server validation accepted the fixed five modules and both unchanged current
consumers together (receipt `baf80c4ece52f1ea4698b4b8`, exit code 0: all seven compiled).
The two validation copies are omitted from the delivery. No coefficient-module
adaptation or additional ring constructor is needed. The candidate modules have zero
remaining sorry. This repair preserves the original result: one original hole closed,
zero holes added.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.ProEtale.AmbientClopen.ambientExactClopenComparisonLocalizes`
(node `lem-sf-ambient-exact-clopen-comparison-localization`). Its assembly proof and
all private helpers contain no sorry.

Proved all three geometric localization results:

- `AlgebraicGeometry.ProEtale.AmbientClopen.ordinary_alpha_localized`
  (`lem-sf-ambient-ordinary-clopen-localization`).
- `AlgebraicGeometry.ProEtale.AmbientClopen.system_alpha_localized`
  (`lem-sf-ambient-system-clopen-localization`).
- `AlgebraicGeometry.ProEtale.AmbientClopen.system_beta_localized`
  (`lem-sf-ambient-system-beta-localization`).

The delivery closes one original hole and adds zero holes. There is no retained
split-off hole, no sorry in a private helper, and no sorry in data. The three new
geometric theorems have complete proofs from the stated localization, adjunction
and compositor APIs.

## No longer needed

Removed the original private proof import `Sheaf.CategoryTheory.ExactDerivedComposition`
(node `lem-sfb-exact-derived-composition`). Its general comparison theorem is not used;
the proof uses the specified exact-functor localization and compositor APIs instead.

The route does not use `lem-sf-ambient-clopen-restriction-uniqueness` or import
`Sheaf.SixFunctors.AmbientClopenRestrictionUniqueness`. Ordinary uniqueness follows
from the mono direct-image unit on an open extension and the invertible open unit;
system uniqueness follows from the already proved clopen-factor Hom detection helper
in `Sheaf.AlgebraicGeometry.SemilinearAlphaPullback`.

`Sheaf.AlgebraicGeometry.EtaleClopenMateNormalization` is not imported: its small
abstract naturality calculation is proved here, without the unrelated étale geometry
and bounded-derived interfaces. This does not remove any of that module's declarations.

The assembly no longer cites these original planned proof dependencies:

- `def-weil-pbc-composite-adjunction`: ordinary categorical composition is used directly.
- `lem-coef-semilinear-derived-sections` (`Sheaf.Paper.SemilinearDerivedSections`):
  the proof works on the recorded single sequence-site category without evaluation.
- `lem-pur-site-restriction-module-adjunction-exact`
  (`Sheaf.CategoryTheory.LocalizedModuleExactForSystems`): the existing exact
  adjunction localization API supplies the cochain unit and counit equations.
- `lem-sf-open-tensor-normalization` (`Sheaf.SixFunctors.OpenTensorNormalization`):
  the open adjunctions are compared using their specified inverse-image functors.
- `lem-sf-proper-open-projection-mate` (`Sheaf.SixFunctors.ProperOpenProjectionMate`):
  the mate formulas follow directly from the recorded adjunctions and alpha.
- `lem-weil-pbc-exact-functor-derived-factorization` and
  `lem-weil-pbc-localization-universal-property`: the exact localization and
  compositor APIs already give the necessary identifications.

The listed removals concern theorem-level proof dependencies. Their statement-level
dependencies and public definition APIs remain where the statements require them;
in particular, the ordinary `ProperOpen` definitions remain imported.
The geometric localization results retain the localization and composition theory
used in their own proofs. No existing declaration or module is withdrawn; no global
pruning is claimed for dependencies still needed elsewhere.

## Where the brief, the DAG or earlier work was wrong

The earlier consumer-check claim was incorrect for returned head `b5a40dded7df`:
`Normalized._proof_1` was absent. The independent reader found this real interface
regression, repaired it and compiled both original consumers. This repair retains
those edits and repeats the consumer check against current sources. The proof itself
was passed by the reader; no theorem statement or proof route is changed by this repair.

The original restriction-normalization plan can be implemented through existing
adjunction and compositor formulas rather than constructing a new product equivalence.
The two systems use the same coefficient category, but their chosen operation
presentations and section-normalized compositors must be compared propositionally
before localizing. An equality inferred merely from finite evaluation would not suffice.

Expanding chosen adjunctions at geometric coefficient categories caused kernel
checking to exceed the file limit. Generic predicates, the coefficient-general constructions, and categorical transport
retain the same formulas while allowing the functors and their category instances to
stay abstract. Systems.Normalized uses the same restriction predicate as the ordinary
version; this is a definitionally equal refactoring. The definition change
record records these refactorings and their consumers. The realization clause additionally
requires its public, definitionally equal formula predicate: a private predicate still
forced the final theorem to re-expand the native category data.

## New nodes

`def-sf-ambient-exact-clopen-data` records the extracted exact-localization and
normalization constructions and their generic categorical interfaces, including
the public `properMateFormula` predicate. The existing
underived-comparison definition node keeps its declarations and attaches them to the
data module.

`lem-sf-ambient-ordinary-clopen-localization` is the identification of the localized
ordinary beta-projector-compositor word with the intrinsic ordinary derived word.

`lem-sf-ambient-system-clopen-localization` is the corresponding identification on the
single simultaneous ringed sequence-site derived category, including the prescribed
projection and outgoing compositors.

`lem-sf-ambient-system-beta-localization` isolates the localization of the cartesian
open comparison with its open-unit normalization. Each theorem has a source and a
complete proof in words, and its node records its exact Lean statement.

Change records:

- `coord/changes/R4-ambient-clopen-data-normalization.md`.
- `coord/changes/R4-ambient-realization-formula-normal-form.md`.

## Second reading by R4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
