## What changed

Replaced the hole in `AlgebraicGeometry.Etale.nonempty_strictLocalMateProjectionData`
by a complete Lean assembly through a bounded-below injective representative. The
statement and its existing docstring are unchanged. The assembly obtains the
representative with Mathlib's `DerivedCategory.Plus.exists_injective_nonempty_iso`,
composes source-to-termwise-sections isomorphisms with the canonical comparison to
stage hypercohomology, and proves both fields by substitution and isomorphism
cancellation.

Added two modules, each with one intermediate theorem:
`Sheaf.AlgebraicGeometry.EtaleInjectiveSectionsComparison` and
`Sheaf.AlgebraicGeometry.StrictLocalInjectiveSourceSections`.
The first constructs the actual chain-level restriction and the right-derived
sections comparison. Every definition is an explicit composite of existing maps;
none selects data from an unproved existence theorem. The second states the source
Hom and mate computation on a specified injective representative. No arbitrary
representative or comparison is installed as a definition.

The assigned module adds only proof imports. Its public import is unchanged.
Updated its DAG proof and dependencies and added matching nodes for the two
intermediate theorems. All three files compile together without warnings. The
final proof takes roughly ten seconds; all files are within the per-file limit.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Etale.nonempty_strictLocalMateProjectionData`
(node `lem-weil-pbc-strict-local-mate-projection-formulas`). The assigned module
has no `sorry` left.

Added two holes, exactly the following named public theorems with complete proof
plans in their docstrings:

- `AlgebraicGeometry.Etale.injectiveSections_strictLocal_comparison`
  (`lem-weil-pbc-injective-sections-pullback-comparison`): invertibility of the
  canonical sections comparison at etale stages, and its transition/projection
  squares. This concerns the right-derived sections unit and no source Hom or mate.
- `AlgebraicGeometry.Etale.exists_strictLocalInjectiveSourceSections`
  (`lem-weil-pbc-strict-local-injective-source-sections`): source Hom, transitions,
  and the mate on a specified injective model, valued in actual termwise sections.
  This does not construct the item's stage hypercohomology identifications.

This is a decomposition, not a sorry-free proof of the mathematical result:
one upper hole closed, two lower holes added, net minus one. The theorem combining
these parts is fully proved. No other holes were added or changed.

## No longer needed

Removed four direct proof imports from the assigned module:
`Sheaf.AlgebraicGeometry.StrictHenselizationRestriction`,
`Sheaf.AlgebraicGeometry.StrictLocalCohomologyGerms`,
`Sheaf.AlgebraicGeometry.StrictLocalNeighbourhoodGeometry`, and
`WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`.
Their modules remain in the transitive import closure, and their nodes remain
used by the intermediate source computation and shared definitions. No module
is pruned from the closure. The injective-representative node remains directly used.

The old direct `proof_deps` absent from the assigned node's new direct list are
`def-weil-pbc-direct-image`, `def-weil-pbc-strict-henselization-restriction`,
`def-weil-pbc-canonical-derived-cohomology-germs`, and
`def-weil-pbc-strict-local-neighbourhood-geometry`. All four are still used by the
new source-computation node; this is removal of direct dependencies, not pruning
of these nodes from the mathematical argument or of their modules from the closure.

The final proof does not import `EtaleComplexPullbackTransport`, the
module-coefficient `EtaleFreeSheafDerivedSections`, or the smooth-base-change
free-sheaf comparison. Their signatures do not directly supply the abelian,
arbitrary bounded-below complex comparison needed here. These were exploratory
candidates, not removals from the original import closure.

## Where the brief, the DAG or earlier work was wrong

The previous missing compiled dependency is now available. The original module
compiled successfully at the beginning of this attempt.

The old proof plan combined source computation and target hypercohomology comparison
in one paragraph. It did not provide Lean declarations for these two precise
compatibilities. The new nodes separate them through a real chain-level object and
explicit canonical maps. The isomorphism at a stage follows from etale restriction
preserving injectives. No such claim is made for the limit projection; its sections
comparison is used only as a morphism. Thus this reduction adds neither a qcqs
hypothesis on f nor an invertibility or continuity assumption on the mate.

Read [Stacks 03Q9](https://stacks.math.columbia.edu/tag/03Q9), the final
injective-complex paragraph, and [Stacks 03Q8](https://stacks.math.columbia.edu/tag/03Q8),
the derived variant. Also checked the source labels in `etale-cohomology.tex`:
`theorem-higher-direct-images` and `lemma-higher-direct-images`. The mathematical
steps follow this paragraph, with the comparison unit at the limit instead of any
claim that the pulled-back injective complex computes derived sections there.

The unit record `dag/units/sk-prop-h2.json` has no realized statement or steps
involving this item. The existing ancestor and unit records are retained, and no
unit or chapter route is bypassed. Existing generic localization/injective nodes
are cited in the new plans. The existing sheaf-only localized cohomology theorem
has a natural-number degree and a single sheaf coefficient; it does not state the
required arbitrary-complex, all-integer, canonical-mate comparison.

Mathlib searches were run with LeanSearch (service unavailable), LeanFinder,
Loogle, and grep, and recorded in `searches.jsonl`. They yielded generic naturality,
sheaf cohomology, and injective-preservation infrastructure, not these complete
comparison formulas. No unavailable search is recorded as a negative result.

## New nodes

`lem-weil-pbc-injective-sections-pullback-comparison` records the explicitly
constructed termwise section maps and the canonical derived-sections comparison,
with invertibility only at etale stages and two compatibility squares. Its
statement allows zero complexes, negative degrees and empty stages; the limit
comparison need not be an isomorphism.

`lem-weil-pbc-strict-local-injective-source-sections` computes source derived Hom
and the canonical mate on a specified injective representative. Its intermediate
objects are actual termwise section complexes, so it is not the original theorem
under another name. The final proof needs both new statements and performs the
composition and cancellation joining them.

No change records are needed: no existing statement or definition was changed.

## Earlier second reading (a previous round; superseded)

1. Compared the assigned module with the repository version. The target declaration signature and docstring are unchanged; only proof imports and the proof body changed. Verdict: pass.
2. Compiled all three delivered modules with `lcompile.py --all`; they compile without warnings. The assigned target has no `sorry`; the two split theorems are named, documented, and correspond to the two added DAG nodes. Verdict: pass.
3. Reviewed the split statements and searched the library for duplicates. Each is a strict intermediate compatibility statement: one for termwise sections versus derived sections, and one for source sections and mate evaluation. Neither restates the target. Verdict: pass.
4. The proof follows the bounded-below injective representative route and retains the required source computation and comparison steps. Imports used by the proof are minimal at the public interface; exploratory candidates were not added. Verdict: pass.
5. The DAG proof and proof dependencies match the Lean proof, and the unit route is unchanged. Verdict: pass.

Changed only the report for this second reading; no Lean or DAG repairs were needed.


## Second reading by E3

1. **Existing interfaces: pass.** Compared the assigned file with the repository
   using `diff -u`. Its sole existing theorem signature and complete docstring are
   byte-for-byte unchanged; the public import is unchanged. Changes are the proof,
   two local elaboration options, and plain proof imports. The other two modules
   are new, and no existing definition, hypothesis, conclusion or visibility changes.
   No forced adaptation or statement-change record is needed.
2. **Kernel and construction checks: pass as a decomposition.** Independently ran
   `lcompile.py --all`: comparison 17.7 s, source computation 9.5 s, assembly 13.8 s,
   no warnings. Appended `#print axioms` for all eight delivered declarations to
   scratch copies and compiled each through `lcompile.py`. All five explicit
   definitions/abbreviations use only `propext`, `Classical.choice`, `Quot.sound`;
   the three theorems additionally use `sorryAx`. Exactly the two reported named
   split theorems have a local `sorry`. No forbidden declaration or implementation
   escape is present. The assembly chooses representatives and source isomorphisms
   within a proposition proof; no definition chooses an arbitrary witness from an
   unproved existence theorem. Scratch copies were removed before delivery.
3. **Split statements: pass.** Read both complete signatures, all five constructions,
   and the docstring proofs against the locally obtained Stacks source, labels
   `lemma-higher-direct-images` and `theorem-higher-direct-images`, including its
   subsequent canonical-base-change remark. The first statement is a sections-unit
   comparison independent of source Hom and the mate; the second computes those
   source maps into actual termwise sections. Their composition and cancellation
   are real steps in the upper proof, not application of a renamed target. Stage
   projections are etale base changes, so restriction preserves injectives; no
   such assumption is made for the limit. Zero complexes and empty total spaces
   give zero groups and maps; negative degrees use the same shifted Hom calculation;
   for identity triangles restriction and comparisons give identity squares.
   Arbitrary representative isomorphisms q are handled by naturality. The Q.first
   and Q.over equations fix the geometric restriction, avoiding arbitrary cone legs.
   Independent LeanFinder search for right-derived sections-unit comparison found
   generic injective-resolution naturality, not these maps; Loogle identifier
   search did not resolve the upstream identifier, and a separate naturality query
   found only general naturality. Independent `rg` on Sheaf and upstream sources
   found the K-injective sections comparison infrastructure and the existing
   complex-pullback transport, free-module sections, and strict-local sheaf-only
   exchange statements. None supplies both split statements: transport still needs
   its specified pullback formula, while the others have different coefficients or
   degree/coefficient scope. Neither split hole has a short complete proof from
   these declarations alone. Search failures were not used as negative results.
4. **Route and pruning: pass.** Checked the assembly from its conclusion downward:
   existing Mathlib injective representative, source sections, canonical stage
   comparison, then substitution and isomorphism cancellation. All direct imports
   are used; new public imports supply signature data. The assigned module's proof
   imports are plain imports. Checked `dag/units/sk-prop-h2.json`: its realized
   statement and step lists are empty and neither names this item; the unit and
   ancestor route are retained. Expanded `No longer needed` to list all four old
   direct proof dependencies removed from the assigned node. They remain used by
   the source split, and no module leaves the target import closure.
5. **DAG agreement: pass after metadata repair.** For all three nodes the union of
   proof-step uses equals proof_deps. The existing node changes only Lean/proof
   metadata allowed in stage 3; its mathematical statement is unchanged. Each new
   node has the source, self-contained statement, dependencies, proof steps,
   origin, searches, creation and blueprint provenance, chapter/unit and Lean
   record. Dependencies have existing Lean records or belong to this delivery.
   Replaced each new node's whitespace-flattened Lean statement by the exact
   multiline declaration signature copied from its module, as the brief requires.

Second reading changed only the two new nodes' verbatim Lean-signature metadata
and the report (complete direct-dependency removal list and this independent
review). Lean code and mathematical statements were retained. Accounting remains
one original hole closed, two strictly intermediate holes added, net minus one;
this is a decomposition, not completion of the result.
