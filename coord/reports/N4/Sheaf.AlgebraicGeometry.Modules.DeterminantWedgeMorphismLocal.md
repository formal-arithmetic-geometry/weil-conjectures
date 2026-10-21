## What changed

Retired Sheaf.AlgebraicGeometry.Modules.DeterminantWedgeMorphismLocal in favor of
its proved WeilConjectures twin, as requested by coord/retire-items.tsv row 1465
and the human's 2026-10-20 retirement hand-off. deleted.txt withdraws the duplicate.

Adapted the sole direct consumer, Sheaf.AlgebraicGeometry.Modules.DeterminantWedgeMorphism:
its private imports use the official twin and ExteriorSheafPowerComparison. Its proof
calls the official local-data and gluing theorems, then transports the resulting
global map along the canonical exteriorSheafPowerIso comparisons. The existing
proved private forward wedge helper is moved from the retired module. Its public
theorem signature and public imports stay verbatim. Removed the unused private
Mathlib.LinearAlgebra.ExteriorPower.Basis import.

The local-data and gluing DAG nodes now point at the official twin with verbatim
Lean statements and its actual proof dependencies. The parent wedge-construction
node records the two official calls followed by comparison transport. No unit
statement or step changes. No upstream source file or target statement changes.

Change record: coord/changes/N4-retire-determinant-wedge-morphism-local.md.

## Proved and sorry left

Zero of zero existing holes closed; zero holes added or split off; zero left in
the item or delivered consumer. This is a retirement/compatibility repair.

The retired copies of determinant_wedgeMorphism_local_data (node
lem-sc-determinant-wedge-morphism-local-data) and determinant_wedgeMorphism_of_local_data
(node lem-sc-determinant-wedge-morphism-glue) are replaced by their already proved
official declarations, without modifying those declarations. The consumer's
AlgebraicGeometry.Scheme.Modules.determinant_wedgeMorphism_exists remains fully
proved, with its original statement; the representation transport and private
exteriorSheafPowerIso_hom_wedge helper are fully proved.

Validation uses lcompile.py only. The original consumer against the withdrawn
stub fails at line 64 with `Unknown identifier determinant_wedgeMorphism_of_local_data`
and at line 65 with `No goals to be solved`, confirming the required adaptation.
The adapted consumer and all four transitive downstream modules compile cleanly
against the withdrawn stub: DeterminantShortExactExists, DeterminantShortExact,
DeterminantDualEvaluation and ShiftedDeterminantDualEvaluation. The three public
theorems determinant_wedgeMorphism_exists, determinant_wedgeMorphism_local_data
and determinant_wedgeMorphism_of_local_data were checked with #print axioms:
all use only propext, Classical.choice and Quot.sound. The consumer's public
signature was checked verbatim
against the original. Degree zero, empty tuples, empty opens/schemes and zero rings
are covered by the existing comparison and official theorem hypotheses, with no
extra assumptions. Import-closure scan finds no Sheaf/WeilConjectures twin pair
and no reference to the retired module in the adapted consumer's closure.

## No longer needed

Withdrawn module: Sheaf.AlgebraicGeometry.Modules.DeterminantWedgeMorphismLocal.
The consumer's private import of it is replaced by the official twin plus the
existing comparison module. The private Mathlib.LinearAlgebra.ExteriorPower.Basis
import is removed: the upstream local construction and gluing already supply
existence; the consumer only needs comparison transport.

No mathematical node is withdrawn: both local-data and gluing nodes retain their
proved official attachments. Their comparison-only dependency is moved to the
parent, which performs the representation transport. The parent's earlier direct
proof dependency lem-weil-pbc-exterior-power-free-basis is unnecessary for this
consumer proof; its uses inside the official construction remain needed. Likewise,
none of the official local-at, quotient-factor, kernel or gluing dependencies is
claimed globally pruned. No new imports of the already retired Sheaf dependencies
are introduced. A dependency-field scan finds the updated parent as the only
current parent of the two retained local nodes; blueprint.from and created.item
occurrences elsewhere are provenance, not dependency edges.

## Where the brief, the DAG or earlier work was wrong

The generic brief described an open proof obligation, but the live module has no
sorry. The current retirement list explicitly assigns its duplicate retirement;
a no-op delivery would not satisfy that assignment. The twin's exteriorPower
statements differ syntactically from the legacy exteriorSheaf statements, so
merely replacing the import is insufficient. The comparison transport supplies
the required compatibility while preserving the consumer's public API and the
local-construction-and-gluing route of the determinant argument.

The old parent node described an expanded local proof despite the Lean consumer
calling local-data and gluing lemmas. Its proof now records those actual calls
and the comparison transport. No mathematical statement is disputed and no new
node or postponed obligation is introduced.

## Second reading by N4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
