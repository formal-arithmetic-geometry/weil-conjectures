## What changed

Replaced the hole in `exists_coefficient_construction` by assembly of coefficient-stage
data and left geometric refinement maps. `refinementComparisonOfLeft` explicitly
constructs the right refinement isomorphism by Mathlib adjunction conjugation, proves
both unit and counit equations, and proves its shift compatibility by the whiskered
unit/left-map/counit formula. This part has no hole.

Moved the original construction data and the two already-proved mate theorems verbatim
to `ConstructibleExceptionalCoefficientConstructionData`, publicly re-exported by the
original module. This permits the new statement modules to use the original data
without an import cycle. Signatures, definition bodies and public names are unchanged.
Added a normalization predicate and a record containing only left refinement maps,
with their geometric realization and descent equations.

## Proved and sorry left

Decomposition, not a net proof: closed the original textual hole in
`WeilConjectures.ConstructibleExceptionalCoefficients.exists_coefficient_construction`
(node `lem-sf-constructible-exceptional-coefficient-construction`), added two holes:

- `WeilConjectures.ConstructibleExceptionalCoefficients.exists_coefficient_stages`
  (`lem-sf-constructible-exceptional-coefficient-stages`): construction steps 1--5,
  no refinement maps.
- `WeilConjectures.ConstructibleExceptionalCoefficients.exists_coefficient_left_refinements`
  (`lem-sf-constructible-exceptional-left-refinements`): only left geometric maps,
  their shift compatibility, ring realization and localization/common-stage equations.

The original module now has zero textual holes. The new conjugate constructor is
fully proved: right invertibility, the unit/counit equations and the right shift
condition are no longer postponed in either split theorem. Two holes total remain
in the new modules. No definition uses a sorry or arbitrary existence witness.

Validation: the server compiled all six delivered modules in dependency order.
The first successful run reported only the inclusion-shift reducibility warning;
its definition is now marked `@[instance_reducible]`, as required for a class-valued
definition. Delivery reruns the compiler and axiom probes.

## No longer needed

No mathematical dependency or module is pruned. All seven original construction
proof dependencies are retained through the two new geometric statements. The
parent proof_deps now name these statements and the proved conjugate constructor.
The constructor uses Mathlib directly and adds no theorem hole. Existing public
prerequisites remain available through the re-export. No upstream declaration was
changed or withdrawn.

## Where the brief, the DAG or earlier work was wrong

The declared dependency interfaces do not directly supply the final construction
record. Three of the seven also cannot be imported by the original module: the
refinement module reaches it through SystemProjectionFormulaCoherence,
FiniteAdjunctionDiagramRealization, FiniteExceptional, the coefficient adjunction
and coherence modules; integral reconstruction reaches it through
IntegralExceptionalInverseImage; integral scalar mates reaches it through integral
shift coherence, finite coefficient Hom change and coefficient adjunctions.
Import-direction checks confirmed these cycles. The new steps retain the geometric
arguments as genuine subproblems instead of importing a cycle or restating the whole
construction under another name. The extra normalization predicate records inherited
shifts and literal raw localization, which the existing field/refinement interfaces
need but the top-level record forgets.

Edge cases: no coefficient exponent zero was introduced (finite stages remain ℕ+).
The stage statement imposes no absolute separatedness of X or Y. Left refinements
are maps on the same operations and realizations; the normalization predicate
asserts no refinement maps. Empty schemes and identity refinements reduce to zero
functors and unitors. Conjugation is valid for every coefficient stage and imposes
no extra geometric hypotheses. Unit-level blueprint routes are retained.

## New nodes

`lem-sf-constructible-exceptional-coefficient-stages` is the existing construction
steps 1--5 with no refinement conclusion, including literal rationalization and
compactification-independent scalar shifts.

`lem-sf-constructible-exceptional-left-refinements` is only the geometric left half
of step 6. Its outputs contain no right comparisons or adjunction equations.

`def-sf-constructible-exceptional-refinement-mate` owns the proved constructor of the
right adjunction conjugate. `def-sf-constructible-exceptional-assembly-data` owns the
new normalization and left-map interfaces. The existing construction-data node is
repointed to its new interface module, with its statement unchanged.

Change record: `coord/changes/A3-coefficient-construction-interface.md`.

## Second reading by A3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
