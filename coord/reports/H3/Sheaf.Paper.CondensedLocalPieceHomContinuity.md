## What changed

Replaced the inherited fixed-degree restatement with the actual local-piece argument.
The original theorem is reduced to two distinct steps: a natural derived evaluation
isomorphism for a locally finite free module, and a compatible strict bounded-below
costalk model. The algebraic functor is explicitly chosen as `Mod.ihom P`; its preservation
of all small colimits is proved by finite free trivializations and joint conservativity
of pro-etale covering restrictions. Its right adjunction then gives exactness.
The canonical colimit comparison is transported through their natural isomorphisms using
a proved equation on every cocone leg. The target statement and all existing signatures are unchanged. The existing generator
predicate is factored through an identical predicate over an abstract coefficient ring;
its meaning and its unfolding witnesses are unchanged. This factors a concrete coefficient
expression out of the existential telescope and avoids costly repeated kernel conversions.

Added seven modules: `CondensedFiniteFreeDerivedHom`, `CondensedFiniteFreeHomContinuity`,
`CondensedLfpHomContinuity`, `CondensedLocalPieceCostalkModel`,
`CondensedFiniteFreeInternalHomColimits`, `CondensedFiniteFreeHomEvaluation`, and
`CondensedLocallyClosedPiece`, all under
`Sheaf.Paper`. The continuity theorems are proved: the first combines exact internal Hom with existing
qcqs global-sections continuity declaration, and the second transports finite coefficient
fields through `ULift` and applies the existing local-triviality declaration. The good
truncation at a common termwise bound is an actual isomorphism, so the proof compares the
specified continuity cocone with the original canonical colimit cocone without an extra
quasi-isomorphism assumption.

Current returned-delivery repair (2026-10-16): `CondensedLfpHomContinuity` now
uses `import all Sheaf.AlgebraicGeometry.CondensedConstructibleSerre` and its existing
private `finite_lf` theorem directly. Removed the three flagged duplicate helpers
`free_of_iso`, `locally_free_comap`, and `locally_free_of_iso`, together with the redundant
`liftCoefficientIso` construction and `finite_lf` wrapper. The previous direct
local-triviality import and `Mathlib.Algebra.Field.ULift` import are also removed.
The existing continuity theorem signature and its final proof are unchanged. The LFP
node records the actual imported specialization. No new admitted statement was added
by this repair. Earlier independent reviews are archived in the sandbox scratchpad;
the repaired delivery requires a fresh second reading.

The previous internal-Hom duplicate-helper repair is retained: the four upstream
localization/internal-Hom calculations are local proof steps, without duplicate
module-level declarations. Those upstream modules still have the separately documented
legacy inverse-image import conflict. This does not affect the Serre import used by
the current repair, which compiles with the finite-coefficient API.

## Proved and sorry left

Original hole closed: `AlgebraicGeometry.ProEtale.condensed_local_piece_hom_continuity`.
Original holes closed: 1 of 1. New holes: 2. This is a decomposition, not a net reduction
in the number of admitted declarations.

Added and proved:

- `AlgebraicGeometry.ProEtale.condensed_finite_free_hom_continuity`;
- `AlgebraicGeometry.ProEtale.condensed_lfp_hom_continuity`;
- `AlgebraicGeometry.ProEtale.condensed_locally_free_ihom_preservesColimits`;
- `AlgebraicGeometry.ProEtale.condensed_finite_free_derived_hom`.

Every remaining admitted declaration in this delivery:

- `AlgebraicGeometry.ProEtale.condensed_finite_free_hom_evaluation`, node
  `lem-weil-pbc-condensed-finite-free-hom-evaluation`. It still needs the natural
  evaluation-normalized derived-Hom/derived-sections identification for internal
  module objects, including integer shifts. The internal-Hom functor is fixed, and
  the conclusion has no filtered diagram or colimit comparison. Its exactness and
  small-colimit preservation are already proved separately in this delivery.
- `AlgebraicGeometry.ProEtale.condensed_local_piece_costalk_model`, node
  `lem-weil-pbc-condensed-local-piece-costalk-model`. It still needs the functorial
  common-bound injective model, the derived adjunctions, and the cone computation proving
  the compatible colimit vertex isomorphism. It imposes no finite-presentation hypothesis
  and asserts no Hom-continuity conclusion.

There is no sorry inside a definition, private helper, or the proof combining these steps.
The existential functors and diagrams are used only in proofs of propositions; no data
is defined by choosing an arbitrary witness from an admitted existence theorem.

## No longer needed

Discarded the unlanded inherited proposal `CondensedLocalPieceHomContinuityDegree` and its
node: this was the original theorem with K and n exposed, so it was not a reduction.
Neither proposal was part of the read-only repository and neither is delivered.

Removed direct proof imports from the item module:
`Sheaf.AlgebraicGeometry.CondensedFieldLfpLocalTriviality`,
`Sheaf.Algebra.Homology.LocallyFreeDerivedHom`,
`Sheaf.Paper.CondensedQcqsPushforwardContinuity`,
`Sheaf.Paper.CondensedOpenClosedRecollement`,
`Sheaf.CategoryTheory.RingedSiteGrothendieckAbelian`, and
`Sheaf.CategoryTheory.RingedSiteKInjectiveResolutions`.
These remain needed through the respective algebraic or geometric subargument and are
not claimed as pruned from the targets' total import closure. Their original dependency
nodes are relocated below the relevant new statements. No established geometric module
is claimed unnecessary.

Pruned five redundant local declarations from `CondensedLfpHomContinuity`:
`free_of_iso`, `locally_free_of_iso`, `locally_free_comap`, `liftCoefficientIso`, and
`finite_lf`. The proof imports and uses the already-existing Serre module's `finite_lf`
instead. Removed its direct imports of
`Sheaf.AlgebraicGeometry.CondensedFieldLfpLocalTriviality` and
`Mathlib.Algebra.Field.ULift`; their needed API is supplied by the existing module.
No Serre-closure conclusion is used, but its module is retained for this specialization.
No established DAG node or module is claimed globally pruned by this repair.

The six old direct proof dependencies now used below the new lemmas are explicitly:
`lem-pur-ringed-site-grothendieck-abelian`,
`lem-weil-pbc-condensed-lfp-local-triviality`,
`lem-weil-pbc-condensed-open-closed-recollement`,
`lem-weil-pbc-condensed-qcqs-pushforward-continuity`,
`lem-weil-pbc-ringed-site-locally-free-derived-hom`, and
`prop-pur-kinjective-resolutions-exist`. All remain dependencies of the argument;
none is claimed pruned from the target import closure.

Second-reading import cleanup: the general algebraic modules no longer import
`CondensedConstructiblePiece`. They import the free-module and ordinary pullback APIs
needed by their signatures. `CondensedFiniteFreeDerivedHom` no longer imports
`HomColimitExtension` or `HomologicalComplexLimits`; it imports the additive Yoneda API
used in its signature. `TensorRegular` is a plain proof import in the internal-Hom
colimit module and is removed from the evaluation module. The costalk-model module
imports the derived-Hom notation and lower-shriek API instead of the finite-free
continuity theorem. The locally finitely presented continuity module exposes its
coefficient and finite-presentation types explicitly and imports the finite-free
continuity theorem only for its proof. These are import reductions, not claims that
an established module leaves the target closure.

## Where the brief, the DAG or earlier work was wrong

The earlier attempt's fixed-degree theorem repeated the whole obligation and its report
mistook that repackaging for a reduction. It has been replaced by the two genuinely
separate algebraic and geometric statements above. No mathematical statement is disputed.

The planned ringed-site derived-Hom lemma is stated for `SheafOfModules`, whereas this item
uses internal `Mod` objects. That transport is substantive and is explicitly included in
the algebraic obligation; the proof does not apply the ringed-site lemma to incompatible
categories. The ordinary derived category is also distinguished from its bounded-below
full subcategory in the costalk obligation.

The current return correctly identified three duplicate finite-free transport
helpers in `CondensedLfpHomContinuity`. Its existing private coefficient isomorphism
and finite-field local-freeness theorem were redundant too. Importing the existing
Serre module succeeds; this repair reuses its theorem rather than inlining or
renaming the rejected duplicate proofs. No target, public theorem, or node statement
changes.

## New nodes

`lem-weil-pbc-condensed-finite-free-derived-hom` matches
`Sheaf.Paper.CondensedFiniteFreeDerivedHom`: the proved combination of exact internal Hom and the evaluation formula.

`lem-weil-pbc-condensed-finite-free-hom-continuity` matches
`Sheaf.Paper.CondensedFiniteFreeHomContinuity`: proved from that formula and existing qcqs
continuity, with the canonical cocone comparison verified by colimit universal properties.

`lem-weil-pbc-condensed-lfp-hom-continuity` matches
`Sheaf.Paper.CondensedLfpHomContinuity`: proved using local triviality and coefficient
transport, then the preceding theorem.

`lem-weil-pbc-condensed-local-piece-costalk-model` matches
`Sheaf.Paper.CondensedLocalPieceCostalkModel`: the geometric strict diagram and compatible
vertex, separated from every local-finiteness and Hom-colimit assertion.

The existing local-piece node's `proof`, `proof_deps`, and `proof_origin` are updated to
match the Lean argument. No existing statement or unit route changes. The coefficient
abstraction of the generator predicate is recorded in
`coord/changes/condensed-constructible-piece-coefficient-abstraction.md`. There are no forced
adaptations: its other users keep the identical definitionally equal predicate.

`lem-weil-pbc-condensed-finite-free-internal-hom-colimits` matches
`Sheaf.Paper.CondensedFiniteFreeInternalHomColimits`: the fully proved preservation of
small colimits by the actual internal-Hom functor. Its private helpers prove local
pullback compatibility, the finite power formula, joint conservativity, and the
canonical comparison calculation.

`lem-weil-pbc-condensed-finite-free-hom-evaluation` matches
`Sheaf.Paper.CondensedFiniteFreeHomEvaluation`: only the natural derived evaluation
identification remains admitted. This is strictly one part of the algebraic formula;
all functorial preservation properties are supplied by the proved internal-Hom module.

`def-weil-pbc-condensed-locally-closed-piece` matches
`Sheaf.Paper.CondensedLocallyClosedPiece`: the original generator predicate abstracted
over the coefficient ring. The existing `CondensedConstructiblePiece` module specializes
this definition, avoiding repeated kernel expansion of the concrete coefficient ring.
See `coord/changes/condensed-constructible-piece-coefficient-abstraction.md` for the old
and new definitions and all direct users.


## Second reading by H3

Independent second reading of the repaired delivery, 2026-10-16:

1. **Interfaces: pass.** Compared all nine delivered modules with the read-only
   repository. Seven are new. The existing theorem
   `AlgebraicGeometry.ProEtale.condensed_local_piece_hom_continuity` and the existing
   definition `AlgebraicGeometry.ProEtale.condensedConstructiblePiece` retain their
   byte-identical declaration statements and visibility. The sole existing definition
   body change is declared in the coefficient-abstraction change record: substituting
   the concrete coefficient into the new predicate reproduces every original witness
   and conjunct. The direct users listed there remain definitionally unchanged; both
   old public imports are still publicly reachable through the new predicate module.
   Also compiled a scratch copy of the repository-original predicate module against
   the current dependencies: it succeeds (4.8 s), as does the adapted module. This is
   an explicitly recorded definition factoring in an unclaimed module, not a claimed
   forced adaptation of another group's module. No target signature or mathematical
   meaning changes.
2. **Proofs and axioms: pass as a decomposition.** Compiled all nine files, in import
   order, using the prescribed `lcompile.py --all`; all compiled without diagnostics.
   Independently compiled the scratch axiom-check module for all public declarations.
   The internal-Hom colimit theorem and both predicates use only `propext`,
   `Classical.choice`, and `Quot.sound`. The other theorems additionally use `sorryAx`,
   consistently with the two split obligations and open upstream inputs. There are
   exactly two source admissions, each the entire proof of its reported named theorem;
   no forbidden declaration or hollow definition occurs. Existential diagrams and
   natural isomorphisms are eliminated only inside proofs. The functor used for the
   internal-Hom construction is explicitly `Mod.ihom P`.
3. **Split statements: pass.** Read both complete signatures, docstring arguments and
   nodes. Evaluation is an isomorphism of functors on complexes for fixed locally
   finite free P, with no filtered diagram. The costalk statement has arbitrary P and
   gives a compatible diagram/vertex, with no Hom-colimit assertion. Neither restates
   the item. Checked zero P, zero rank, empty schemes, identity immersions, singleton
   filtered diagrams and integer shifts: none requires an omitted nonemptiness or
   finiteness hypothesis. Repeated searches with different wording using LeanFinder,
   Loogle, Mathlib grep and repository rg found no directly applicable replacement.
   The existing ringed-site derived-Hom theorem has different module categories; its
   transport is part of the remaining evaluation obligation, not silently assumed.
   Neither remaining obligation can be closed by a short application of that API.
4. **Route and pruning: pass.** Traced the top proof through the costalk leg equation,
   the colimit universal property, the locally free continuity proof and the imported
   Serre `finite_lf` specialization. The return's duplicate LFP helpers have all been
   removed, including their redundant coefficient transport. Reviewed the internal-Hom
   finite-power, pullback and joint-conservativity calculations. Independently tested
   importing the original upstream internal-Hom/conservativity modules: Lean rejects
   the legacy inverse-image API because its notation declaration already exists from
   `FiniteCoefficient.UpperLowerStar.Defs`. Thus these current-API adaptations cannot
   simply be replaced by those imports. Public imports supply types or instance data
   in signatures; proof imports remain plain, including `import all` for `finite_lf`.
   The old six proof-dependency nodes remain below the separated arguments and are
   fully listed under No longer needed; none is claimed globally pruned. Inspected
   `dag/units/sk-thm-properbasechange.json`: its realized statement and three steps are
   untouched, and this reduction changes no unit-level route.
5. **DAG: pass.** Read all nine delivered node records against the Lean. The two old
   nodes retain their statements; their proof routes record the specialization and
   actual reduction. New node signatures agree with the corresponding declarations;
   proof dependencies are the unions of the proof steps' uses. The LFP node correctly
   records the imported Serre specialization and its local-triviality input. Each
   remaining admission has a matching sourced node, explicit proof argument, creation
   record, blueprint link, chapter/unit and recorded searches.

Source check: [Hemo--Richarz--Scholbach, Lemma 5.3 and its proof](https://arxiv.org/pdf/2305.18131),
p. 14 of the PDF, supplies the bounded-below colimit, duality and
open/closed exceptional-pullback route used here. The strict model and internal-module
transport are explicitly left as formal obligations, not claimed proved by the paper
citation alone.

Changes made in this second reading: added this independent review and fresh search
and axiom-check evidence. No Lean statement, definition, proof or DAG route needed a
further change. The delivery remains one original hole closed and two new named holes
added, a decomposition rather than an axiom-free proof of the target. No positive
ledger net is claimed; the ledger also accounts for previously existing admissions
reached through the new imports.
