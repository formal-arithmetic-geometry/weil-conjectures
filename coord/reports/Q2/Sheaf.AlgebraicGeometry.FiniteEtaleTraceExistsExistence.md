## What changed

Replaced the sole proof hole in `Sheaf.AlgebraicGeometry.FiniteEtaleTraceExistsExistence`
without changing its signature or public imports. The proof chooses a natural
transformation separately for each finite étale morphism, obtains naturality from its
`naturality` field, and proves the localization and split clauses using its local sum
characterization. Three proof-only imports carry those results.

Added a concrete predicate `FiniteEtaleTraceLocalSums`, which quantifies over all finite
clopen splittings of each pulled-back site object, including empty splittings. It neither
chooses a trace nor assumes localization. Added four theorem modules; two have complete
Lean proofs:

- `finiteEtaleTrace_descent` constructs additive component maps from unique characterized
  sections, proves compatibility with restrictions and naturality in the sheaf, assembles
  a natural transformation, and transports it through the restriction isomorphism.
- `finiteEtaleTrace_sum_of_localSums` constructs the pulled-back pieces and their inverses,
  proves their coverage and disjointness using the scheme coproduct's underlying disjoint
  union, and specializes the local sum formula to the explicit pullback lifts.

The other two modules isolate section gluing and comparison under localization. Neither
restates the original family-existence theorem: one supplies a unique section for one
input on one site object, and the other compares two already given sheaf morphisms.
Updated the original node's proof route and added a matching node for each new declaration.
All six Lean modules compile locally without warnings. This is a decomposition,
not a completed proof: one original hole is closed and two lower holes are added
(net -1 before any import-closure effects). The final dry run checks compilation
on the server, declaration signatures, and the project's axiom probes.

## Proved and sorry left

`AlgebraicGeometry.Etale.finiteEtaleTrace_exists`: its original `sorry` is removed;
the complete Lean proof uses the two remaining lemmas below transitively.

Also proved, without a direct `sorry`:
`AlgebraicGeometry.Etale.finiteEtaleTrace_descent` and
`AlgebraicGeometry.Etale.finiteEtaleTrace_sum_of_localSums`.
The latter has no proof holes in its geometric argument. The local sum predicate is a
fully defined proposition; there is no `sorry` in any definition or private helper.

Exactly two `sorry`s remain in the delivery:

- `AlgebraicGeometry.Etale.finiteEtaleTrace_section_descent`, node
  `lem-weil-pbc-finite-etale-trace-section-descent`, in `FiniteEtaleTraceSectionDescent`:
  gluing and uniqueness of an individual section, characterized on every split refinement.
- `AlgebraicGeometry.Etale.finiteEtaleTrace_localization_of_localSums`, node
  `lem-weil-pbc-finite-etale-trace-localization`, in `FiniteEtaleTraceLocalization`:
  component comparison for arbitrary given trace morphisms satisfying the local sum predicate.

Each is the whole proof of a public named theorem, with source and detailed proof in its
docstring. Empty index sets, empty bases, nonconstant finite degree and arbitrary coefficient
sheaves remain allowed. The pullback-sum proof uses no inhabitedness assumption, and all
inverse identities are checked on both pullback projections. The localization lemma needs
local sums on every split site object; a formula only for a globally split `Y` would not
suffice when `Y` itself is not globally split.

## No longer needed

The three existing public imports remain needed by the unchanged statement.
Two original proof-only imports are removed from the item:
`Sheaf.Paper.FiniteEtaleEtaleLocalSplit` moves to the section-descent and localization
modules whose unfinished proof plans need its theorem; it remains in the import closure.
`WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs` is redundant, because the retained
public `LowerShriek.OpenImmersion.Defs` already imports it publicly; it also remains in
the closure. The item's three new imports are proof-only and all are used.
No existing module is claimed to leave the targets' import closure.

The proof no longer needs `lem-weil-pbc-scheme-coproduct-copies`. The geometric step uses
`lem-weil-pbc-scheme-coproduct-family` for the arbitrary pieces of a given cofan instead.
The original node still mentions the copies reformulation in its statement, so its
statement dependency is preserved; this is pruning from the proof, not deletion of the node.
At the item's node the old dependencies other than finite-morphism permanence and
étale base-change finite limits have been replaced by the three helper theorem nodes.
The following remain transitive dependencies of those helpers and are not mathematically
pruned: `def-pc-fibre-product`, `def-weil-open-immersion`,
`def-weil-pbc-abelian-etale-sheaves`, `def-weil-pbc-direct-image`,
`def-weil-pbc-etale-site`, `lem-weil-pbc-cartesian-square-pasting`,
`lem-weil-pbc-etale-composition-cancellation`, `lem-weil-pbc-etale-covering-base-change`,
`lem-weil-pbc-etale-inverse-image-restriction`,
`lem-weil-pbc-finite-etale-etale-local-split`, and `lem-weil-pbc-open-fibre-product`.
Only the copies-specific coproduct result is replaced mathematically, by the general
family result. No outstanding unit step is bypassed.

Removed the finite-morphism import from the new local-sum definition module: the predicate
only requires an étale map. The three new statements requiring finiteness import that
Mathlib module publicly themselves. No experimental or unused Lean module is delivered.

## Where the brief, the DAG or earlier work was wrong

No target statement or mathematical claim was changed. The existing nine-step descent
plan has been made into a compiling reduction; its section construction and final
localization comparison remain the explicit next tasks. The generic coproduct result
needed for arbitrary splitting pieces is `lem-weil-pbc-scheme-coproduct-family`, rather than
only the copies result recorded in the old proof dependencies.

The local copy does not contain the Stacks TeX sources. The source text was checked at
[Stacks 03SH](https://stacks.math.columbia.edu/tag/03SH) and
[Stacks 04HN](https://stacks.math.columbia.edu/tag/04HN); the detailed descent proof is
written by the worker, following the supplied node and its SGA 4 IX 5.1 citation.
LeanSearch returned HTTP Internal Server Error and is recorded as unavailable, not as a
negative search. LeanFinder and Mathlib grep ran successfully; neither supplied an exact
trace theorem. The existing project `finiteEtaleTrace` chooses the original existence
witness, so it would be circular here. Blueprint searches for `trace`, `local sum`,
`finite etale trace`, and `03SH` produced no duplicate of these intermediate statements.

The ancestry tool on this item returns no ancestor because its `created.item` names a
module. The new nodes follow its already recorded parent `lem-weil-pbc-finite-etale-trace-exists`
to the actual blueprint ancestor `lemma-weil-pbc-curve-locally-constant-reduction`.

## New nodes

`def-weil-pbc-finite-etale-trace-local-sums`: the local splitting-sum predicate;
module `Sheaf.AlgebraicGeometry.FiniteEtaleTraceLocalSums`.

`lem-weil-pbc-finite-etale-trace-section-descent`: the unique characterized section;
module `Sheaf.AlgebraicGeometry.FiniteEtaleTraceSectionDescent`; proof left `sorry`.

`lem-weil-pbc-finite-etale-trace-descent`: the natural transformation constructed from
those sections; module `Sheaf.AlgebraicGeometry.FiniteEtaleTraceDescent`; Lean proof complete.

`lem-weil-pbc-finite-etale-trace-pullback-sum`: the pulled-back global split formula;
module `Sheaf.AlgebraicGeometry.FiniteEtaleTracePullbackSum`; Lean proof complete.

`lem-weil-pbc-finite-etale-trace-localization`: localization comparison from local sums;
module `Sheaf.AlgebraicGeometry.FiniteEtaleTraceLocalization`; proof left `sorry`.

There are no change records: existing signatures and definitions are unchanged.

## Second reading by Q2

1. **Existing interfaces — pass.** Diffed the item against the repository version.
   Its complete declaration signature and existing docstring are byte for byte unchanged;
   only proof-only imports and its proof body differ. The five other delivered modules
   are new. No existing definition, public import, or target statement changed, and no
   change record is needed. The existing node changes only `proof`, `proof_deps`, and
   `proof_origin`.
2. **Lean proof and axioms — pass as a decomposition.** Compiled all six modules locally
   in import order. Searched all delivered sources for forbidden declarations/options,
   and checked each public declaration with `#print axioms` in temporary scratch copies.
   The predicate and `finiteEtaleTrace_sum_of_localSums` use only `propext`,
   `Classical.choice`, and `Quot.sound`. The existence theorem, natural-transformation
   construction, and two open lemmas additionally use `sorryAx`, accounted for by the
   two named theorem holes. There are exactly two direct `sorry`s, both whole named
   theorem proofs; there is none in a definition or private helper. The original
   existence theorem is therefore not yet proved with the project's allowed axioms.
3. **Split statements — pass.** Read both statements and their full docstring proofs.
   Section descent is an existence-and-uniqueness assertion for one input section;
   localization compares two given sheaf morphisms satisfying a concrete local sum
   predicate. Neither restates the family-existence theorem. Checked identity covers,
   single-sheet splittings, zero-sheet covers, the empty base, disconnected bases with
   varying degree, and arbitrary additive coefficient sheaves. An empty index type can
   split a nonempty base when the finite cover is empty; its trace is zero. Unequal
   cardinalities in two splittings of the same cover force an empty base. The formulas
   remain valid in both cases. No inhabitedness or constant-degree assumption is hidden.
   Independent LeanFinder search for additive transfers by gluing returned condensed
   locally constant sheaf constructions, not these results; Loogle for transfer/sheaf
   returned zero hits. Mathlib grep for transfer/norm/sheaf sums and project `rg`
   found no replacement. The existing module-valued adjunction trace does not supply
   these explicit local sum identities in a few-minute reduction. Checked the source
   characterization at [Stacks 03SH](https://stacks.math.columbia.edu/tag/03SH) and its
   local splitting input [04HN](https://stacks.math.columbia.edu/tag/04HN). Neither open
   lemma has a short missing Lean argument that could be closed during this reading.
4. **Route and pruning — pass after repair.** Read the construction downward from the
   target: choice of natural transformations, naturality, localization comparison,
   and the proved pullback-sum argument. The latter genuinely builds the pullback
   coproduct and checks both inverse identities, including the empty family. Read
   `dag/units/sk-thm-p1.json`: the item realizes no separate unit-level step, and this
   reduction preserves the trace splitting used by locally constant reduction.
   Corrected `No longer needed` to include both imports removed relative to the current
   repository and all displaced old direct proof dependencies, distinguishing those
   still needed transitively. The copies-specific coproduct dependency is replaced
   by the arbitrary-family result; no existing module is asserted pruned from the
   targets' closure. Restored the finite étale local splitting proof-only import in
   the two new open modules whose recorded proof plans use it. Removed the redundant
   finite-sum lemmas import from the descent module, confirmed by compilation.
5. **DAG metadata — pass.** All five new nodes have the required creation, ancestry,
   chapter/unit, source, search, and Lean records. Used the project's declaration
   parser to compare every recorded `lean.statement` with its Lean signature: all
   match. For every node, `proof_deps` equals the union of its proof steps' `uses`.
   The written proof routes and origins agree with the assembly, geometric sum proof,
   and the two remaining mathematical arguments. The local sum predicate is concrete
   and carries its definition node.

Changed only proof-only import placement and pruning: added
`Sheaf.Paper.FiniteEtaleEtaleLocalSplit` to the two open theorem modules and removed
`Mathlib.Algebra.BigOperators.Group.Finset.Lemmas` from the proved descent module.
Corrected the report's removed-import accounting and explicitly classified the work
as a decomposition: one original hole closed, two new holes added, no original theorem
certified without `sorryAx`. No proof body, statement, definition, or node needed repair.
