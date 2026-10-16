## What changed

`AlgebraicGeometry.ProEtale.comparison_square` is reduced to underived square coherence and
its exact derived transport, preserving the original statement byte for byte. The chosen
Cartesian square uses `sq.isoPullback` with its projection identities.

`ComparisonSquareComponent.lean` proves
`AlgebraicGeometry.ProEtale.comparison_square_component_of_commRing` by specializing the
already proved generic `comparison_coherent` and projecting its square clause. A proof-only
`import all Sheaf.AlgebraicGeometry.ComparisonPullbackCoherence` makes that private proof
available through Lean's module system. The ordinary public import supplies the definitions
in the statement. No library interface was changed.

`ComparisonSquareTransport.lean` states the remaining categorical transport with underived
coherence as an explicit hypothesis. The target imports both helpers only for its proof.
All three modules compile. The second reading also repaired the new node metadata and
expanded the remaining theorem's natural-language proof.

## Proved and sorry left

Original hole closed:

- `AlgebraicGeometry.ProEtale.comparison_square`, node
  `stage3-proetale-comparison-square` (1 of 1 original holes).

Additional theorem fully proved:

- `AlgebraicGeometry.ProEtale.comparison_square_component_of_commRing`, node
  `stage3-proetale-comparison-square-component`. The second reading closed the first
  worker's draft hole here using existing generic coherence. Its printed axioms are only
  `propext`, `Classical.choice` and `Quot.sound`.

One new hole remains:

- `AlgebraicGeometry.ProEtale.comparison_square_of_component`, node
  `stage3-proetale-comparison-square-transport`, whose body is exactly `by sorry`.

Relative to the repository: holes closed 1, holes added 1, net 0. This is a decomposition,
not a completed proof of the target. Relative to the first worker's draft, the second
reading closes one of its two new holes. `comparison_square` and the transport theorem
print only the three allowed axioms and `sorryAx`; the latter is accounted for by this
single admitted transport theorem. No definition was added or changed, and there is no
`sorry` in a definition.

## No longer needed

No existing import or module is pruned. Every import is needed for a public statement or
a proof. The additional `import all` in the component module is proof-only; its ordinary
public import is required for the public statement's comparison-data definitions.

The old direct proof dependency `lem-weil-pbc-comparison-pullback` of
`stage3-proetale-comparison-square` is replaced by the two helper nodes. It remains used
transitively by the proved component step and is not withdrawn. The transport node does
not need either the target node or the component theorem as a dependency: its statement
uses the established comparison definitions, and its mathematical argument assumes the
component equations as `hcomp`. Its formal functoriality/cancellation step has no additional
proof-node prerequisites. No top-level `tool_uses` approval was removed.

## Where the brief, the DAG or earlier work was wrong

The first worker correctly rejected adding a finiteness hypothesis to the target, but
missed the generic `comparison_coherent` proof in `ComparisonPullbackCoherence.lean`.
Although the public bundled `comparison_pullback_coherent` theorem mentions `[Finite Λ]`,
its generic proof applies to all coefficient categories with the indicated sheafification
and colimits. Lean's proof-only `import all` permits its direct reuse without duplicating
its argument or changing its visibility.

The draft transport node listed the target itself in `stmt_deps`, creating a cycle, and
listed the component theorem as a proof dependency although it only needs the supplied
hypothesis. Both edges were removed. Its source path was corrected to the parent's actual
blueprint file. These are repairs to new nodes, not changes to an existing statement.

## New nodes

`stage3-proetale-comparison-square-component` records the arbitrary-ring underived square
component. Its Lean theorem is proved by the existing generic coherence theorem. Searches
found the generic proof in the project and no more direct public specialized theorem.

`stage3-proetale-comparison-square-transport` isolates passage from an assumed underived
component equation through exact derived functors, left-derived comparison isomorphisms
and the bounded-below inclusion. This is strictly the categorical transport part of the
original proof; it does not assert underived coherence. Its docstring explains the
natural-transformation, localization, conjugation and restriction steps. No change record
is needed: all existing statements and definitions are unchanged.

## Second reading by E1

1. **Visible statements.** Compared every delivered file with the repository. The only
   existing declaration is `comparison_square`; its full signature is now byte-for-byte
   identical, including the whitespace before `:=`. Its public import and docstring are
   unchanged. The new helper modules add no definitions and alter no existing declaration.

2. **Proof and trust.** Compiled the three modules in import order with `lcompile.py --all`.
   Scanned their complete text: no forbidden declaration or implementation escape; the
   sole `sorry` is exactly the named transport theorem. A scratch copy printed the axioms
   of all three declarations: the component theorem has only the permitted three axioms;
   the target and transport additionally have the reported `sorryAx`. No data is chosen
   from an unproved existence theorem.

3. **Split statements.** Read the comparison-data definitions, the existing generic
   coherence proof, both fixed derived square constructions, and the source blueprint
   proof. Checked zero sheaves/complexes, the zero coefficient ring and identity squares:
   the component equation is respectively unique or the coherence unit law, and the
   derived statement has the same reductions under its explicit coherence hypothesis.
   The component theorem is now actually proved for every ring. The transport is the
   sourced formal passage to derived categories; it has an additional, substantive
   underived hypothesis and proves only that transport step. It neither proves its own
   hypothesis nor invokes the target, so the delivery is a real reduction rather than
   a renamed admitted copy of the target. Repeated LeanFinder, Loogle and grep searches
   with functoriality/pasting terminology; inspected the generic derived APIs and the
   upstream `mapDerivedCategorySquareIso_hom_app_comp`. They provide parts of the
   calculation, not the fixed-site, left-derived and bounded-below equation by one
   application.

4. **Route and pruning.** Read `dag/units/sk-thm-properbasechange.json`, including its
   statement and all three `realized.steps`, and the source transport proof. The unit's
   projective-line/reduction/torsion route is preserved. No realized unit node or existing
   module is bypassed. Imports are minimal for the stated signatures and proof reuse;
   the direct dependency replacement is exhaustively listed above.

5. **DAG agreement.** Checked all three node records against the Lean declarations,
   including verbatim new signatures, the union of each proof step's `uses`, the source,
   chapter, unit, creation and blueprint fields. The parent uses exactly the two helper
   nodes. The component's proof origin now names its actual existing generic proof.
   Removed the new transport node's circular/unused dependencies and corrected its
   source path; its `hcomp` is assumed, not supplied by its own proof.

**Changes made by this reader:** proved the arbitrary-ring component using proof-only
`import all`; updated that theorem's proof explanation and node proof origin; restored
exact target signature whitespace; repaired the transport node's dependencies/source;
expanded the transport proof explanation; corrected the report's counts and dependency
accounting. No target statement, definition or existing public import was changed.
