## What changed

Proved `AlgebraicGeometry.Scheme.Modules.cechH1Map_natural` in
`Sheaf.AlgebraicGeometry.CechH1MapNatural`, with its signature and visibility unchanged.
The library already proves the stronger all-degree theorem
`AlgebraicGeometry.Scheme.Modules.cechComparisonMapNaturality` in
`Sheaf.Paper.CechComparisonMapNaturality`. Specialize its existence and naturality
conjuncts to degree one, assemble the family by classical choice, and apply naturality
to the chosen comparisons. This is the same Stacks 01EQ construction, already implemented
in the library. The predicate uniquely determines each chosen map by cancellation against
the resolution identification and H(alpha); no arbitrary undetermined data is introduced.

Added a proof-only import of `Sheaf.Paper.CechComparisonMapNaturality` and updated the
item's node proof, proof dependencies and proof origin. Kept the public statement import
`Sheaf.AlgebraicGeometry.ModuleCechComparison`. The unit record
`sk-thm-curveestimate` realizes only `thm-sc-proper-cohomology` and no proof steps;
this specialization bypasses no unit statement or step. The imported theorem from the
Picard-duality unit is a generic tool for exactly the same Stacks 01EQ assertion.

## Proved and sorry left

Closed one hole: `AlgebraicGeometry.Scheme.Modules.cechH1Map_natural`
(node `lem-sc-cech-h1-map-natural`). No holes remain in the item and no holes were added.
No statements or definitions changed. No new nodes or split-off theorems.

## No longer needed

Removed these direct proof imports:

- `Sheaf.AlgebraicGeometry.ModuleInjectiveOpenCoverCechAcyclic`
- `Sheaf.AlgebraicGeometry.SchemeModulesEnoughInjectives`
- `Sheaf.CategoryTheory.DoubleComplexTotal`
- `Sheaf.CategoryTheory.SiteCechComplex`
- `Sheaf.Paper.PQFCohomology`
- `WeilConjectures.Mathlib.Algebra.Homology.TotalComplex`

The item no longer directly invokes the original proof dependencies:
`lem-weil-pbc-scheme-modules-enough-injectives`, `def-sp-injective-resolutions`,
`def-weil-pbc-site-cech-complex`, `def-sp-double-complex-total`, `def-sc-zariski-site`,
`lem-weil-pbc-module-injective-open-cover-cech-acyclic`,
`thm-sp-double-complex-spectral-sequences`, `pqf-def-cohomology`,
`lem-weil-pbc-injective-resolution-lift-exists`, and
`lem-weil-pbc-derived-functor-map-via-lift`.
The all-degree comparison and its public definitions still use some of their underlying
theory transitively; removal here does not assert that every such module disappears
from the targets' closure. The only direct proof dependency now is
`lem-sc-cech-comparison-map-naturality`.

## Where the brief, the DAG or earlier work was wrong

The planned construction is valid but already implemented in the existing, proved
all-degree comparison theorem. Repeating it is unnecessary. The repository's literature
copy of `cohomology.tex` is absent on this machine; the existing theorem's node and proof
were read and agree with this item's Stacks 01EQ source and original proof plan.
LeanFinder returned general global-sections naturality lemmas, not this comparison;
local searches found the exact stronger library result. The import-direction check
allows the new proof import without a cycle.

## Second reading by G1

1. Compared the sole delivered Lean module with the repository using `diff` and
   checked its existing theorem signature byte for byte. Verdict: unchanged;
   visibility, public imports, definitions, hypotheses and conclusion are preserved.
   Only proof imports, the proof explanation and the proof body differ. No change
   record is required.
2. Compiled the delivered module through `lcompile.py` with no errors or warnings.
   Searched the delivered Lean for forbidden declarations and `sorry`: none.
   Compiled a scratch copy with `#print axioms` for both `cechH1Map_natural` and
   `cechComparisonMapNaturality`: both use only `propext`, `Classical.choice` and
   `Quot.sound`, with no `sorryAx`. Verdict: a complete proof, not a decomposition.
3. No statements were split off and no new declarations or nodes were added.
   Read the all-degree comparison theorem and the definition of
   `IsModuleCechComparison`. Its equation for any injective resolution determines
   the comparison uniquely by cancellation against the resolution isomorphism and
   the invertible homology map of alpha. Thus choice assembles determined maps,
   not arbitrary witnesses of an unproved existence assertion. The specialization
   imposes no extra assumption on the module or cover; zero modules, a single-open
   cover, and the empty cover of the empty scheme are included. Verdict: no new
   statement or hollow definition to repair.
4. Read the proof from its target down through the existing all-degree result;
   searched the library for the comparison predicate and naturality declarations.
   The existing general theorem supplies exactly the existence and naturality
   conjuncts needed, with no duplicated construction. Both imports are needed:
   the public import provides the statement's definitions, the plain import the
   proof's theorem. Checked every old `proof_deps` entry against `No longer needed`:
   all ten omitted entries are listed. Read `dag/units/sk-thm-curveestimate.json`:
   its realized statement remains `thm-sc-proper-cohomology` and it has no realized
   proof steps. Verdict: the shorter route stays below the unit level.
5. Compared the node JSONs: only `proof`, `proof_deps` and `proof_origin` change.
   The new proof names the exact all-degree dependency, degree-one specialization,
   choice and naturality application used by Lean. The source remains Stacks 01EQ.
   No new nodes require additional fields. Verdict: DAG and Lean agree.

Second reading changed only this report, adding the independent checks and verdicts;
no Lean or node repair was necessary. Holes closed: one, `cechH1Map_natural`.
Holes added: zero. Split-off statements: zero.
