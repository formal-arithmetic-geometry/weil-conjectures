## What changed

Proved `AlgebraicGeometry.ProEtale.constructibleDirectImageFiniteness_of_isProper`
with its exact existing signature. A constructible finite-coefficient sheaf is transported
from its etale origin; etale proper finiteness and the canonical bounded-below derived
comparison give the two FIN clauses with bound 2e.

Added `Sheaf.AlgebraicGeometry.FiniteCoefficientRealizationDirectImage`, with the fully
proved theorem `AlgebraicGeometry.ProEtale.finiteCoefficientRealization_directImage`.
It checks the specified coefficient-ring map on constant scalars, identifies restriction
with the fully faithful right adjoint to module sheafification, and cancels that functor
to obtain an ordinary direct-image isomorphism. Private helpers in the item derive it and
take cohomology. All new definitions have concrete, hole-free bodies.

Updated the parent node's proof, proof dependencies and proof origin, and added the node
for the coefficient-realization lemma. No existing statement, definition or public import
changed. The unit's realized statement and proof steps are preserved.

Both modules compiled together through lcompile.py --all without errors or warnings.
Only proof dependencies were imported; upstream exact-functor and derived-comparison
interfaces supply the cohomology and single-degree compatibilities.

## Proved and sorry left

Closed 1 of the item's 1 holes:
`AlgebraicGeometry.ProEtale.constructibleDirectImageFiniteness_of_isProper`
(node `thm-weil-pbc-direct-image-finiteness-proper`).

Also proved the new theorem
`AlgebraicGeometry.ProEtale.finiteCoefficientRealization_directImage`
(node `lem-weil-pbc-finite-coefficient-realization-direct-image`).

No sorry remains in either delivered module; 0 holes added and 0 split off.
This closes the local hole from existing declared dependencies, some of which still rely
on sorry elsewhere in the library; it does not claim an axiom-free target closure.

## No longer needed

Removed these proof imports from the original item:
- `Mathlib.AlgebraicGeometry.Scheme`;
- `Mathlib.RingTheory.Noetherian.Defs`;
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`;
- `Sheaf.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf`;
- `Sheaf.AlgebraicGeometry.ProEtaleSiteComparisonFiniteLevel`;
- `Sheaf.AlgebraicGeometry.ComparisonDirectImage` (added to current sources while this
  session was running).

The first four were redundant with the statement imports and actual proof interfaces.
The separate node `prop-weil-pbc-site-comparison-finite-level` is no longer a direct proof
dependency: exactness of comparison inverse image is already supplied by its existing
upstream instances, while the canonical derived direct-image comparison is used directly.
Its unit and injective-acyclicity clauses are not separately invoked here. The mathematical
comparison dependency `prop-weil-pbc-comparison-direct-image` is retained and realized by
`rightDerivedLowerStarComparisonIso'` from the existing smooth-base-change comparisons
module. No unit step is bypassed. No other declared dependency is pruned, and no module
is withdrawn. No new lower unproved obligations are introduced.

## Where the brief, the DAG or earlier work was wrong

The retained sandbox already contained the intended proof but did not compile: the
scalar-linearity subgoal was indented outside its structure field, its scalar action
needed the original module presentation made explicit, and the natural-isomorphism
composition needed explicit functor associators and whiskering functors. These are fixed.

The original prose transfer omitted the concrete bridge from fixed-ring pro-etale sheaves
to modules over the specified continuous-function coefficient ring sheaf. The added lemma
supplies that bridge for every morphism, without properness or constructibility assumptions.
Its empty-scheme and zero-ring cases require no special assumptions: the unit is a
sheafification isomorphism and the section maps are identities throughout.

The inherited helper's source labels 03DA/0D6E were too broad for its ordinary statement.
They were replaced by the actual module-sheafification and pushforward labels in the local
Stacks source (sites-modules.tex, lemma-sheafification-presheaf-modules and
definition-pushforward). Whole-Mathlib grep through msearch twice timed out; narrow direct
rg on the relevant Mathlib source supplied the missing source-search evidence.

An earlier delivery dry run timed out during worktree checkout before preflight.
On resumption, no delivery process remained active. Both retained modules were compiled
again successfully through lcompile.py --all (0.1 s and 1.2 s), with no warnings.
The resumed required dry run then passed compilation and preflight, with review class
CODEX for the new proved module/node and route-import pruning. No delivery gate was bypassed.

## New nodes

`lem-weil-pbc-finite-coefficient-realization-direct-image` records the fully proved ordinary
realization/direct-image compatibility. It belongs to the parent's chapter and unit,
serves the displayed comparison in the parent proof, and adds no sorry. Searches found
only the general sheafification adjunction API, not this scalar-map compatibility.
No change record is needed: no existing signature or definition changed.

## Second reading by T4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
