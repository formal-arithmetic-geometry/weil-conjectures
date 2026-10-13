## What changed

Proved `AlgebraicGeometry.Scheme.Modules.exists_addEquiv_H_pushforward_natural_of_higherDirectImage_vanishing`
in `Sheaf.AlgebraicGeometry.LerayAcyclicAdditiveNaturality`, preserving its entire signature and
visibility. Added the fully proved private helper `acyclic_composite_comparison`.

The shorter route applies the acyclic-resolution criterion to the pushed-forward injective
resolution. The vanishing assumption makes the pushed-forward augmentation a quasi-isomorphism;
module pushforwards of injectives are acyclic for global sections. Both derived computations
therefore use the same complex. Naturality follows from the same lift of an endomorphism in both
computations. Forget scalars and compose with the existing natural sections and source-model
comparisons to obtain the desired additive equivalence and its naturality equation.

Added four proof-only imports:
`Sheaf.AlgebraicGeometry.ModuleCohomologySourceComparison`,
`Sheaf.AlgebraicGeometry.ModulePushforwardInjectiveAcyclic`,
`Sheaf.AlgebraicGeometry.LeraySectionsResolutionComparison`, and
`Sheaf.CategoryTheory.Abelian.RightDerived.AcyclicComparisonNatural`.
Every added import supplies a declaration used directly. The existing public import is retained.
Updated the item's node proof, proof_deps and proof_origin to describe this route.

Local single-file compilation succeeds without warnings. All four imports pass import_direction.py.
The proof handles degree zero, zero coefficients and empty schemes through the same general
acyclic-resolution argument. No definition, statement, public import or target was changed.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Scheme.Modules.exists_addEquiv_H_pushforward_natural_of_higherDirectImage_vanishing`
(node `lem-pc-k2-leray-acyclic-additive-naturality`).

The private helper `acyclic_composite_comparison` is also fully proved. No holes remain in the
item, and no holes or modules with new holes were added. This is a proof from existing named
library declarations, not a decomposition into new statements.

## No longer needed

No existing imports were removed: the original module had only its statement-level public import.

The item's direct proof route no longer needs
`lem-sc-leray-closed-pushforward-cohomology`, module
`Sheaf.Topology.Sheaves.LerayAcyclicComparison`: no topological spectral sequence or topological
Leray edge is used. It also no longer needs a direct use of
`lem-sc-zariski-flasque-quotient-sections` (Mathlib's flasque quotient/sections results).
Both are removed from the item's proof_deps. This is pruning of this item's planned route;
other targets or dependencies may still need those results.

`lem-sc-module-abelian-zariski-cohomology`, module
`Sheaf.Paper.ZariskiModuleAbelianCohomologyNatural`, is no longer a direct dependency either.
Its comparison is still used transitively by ModuleCohomologySourceComparison through
ZariskiModuleAbelianCohomologyAgree, so it is not claimed as a globally pruned module.
The source-model identification is reused rather than reconstructed here.

`lemma-weil-pbc-leray-acyclicity` remains needed for the acyclic-resolution API.
The unit's realized statement and steps are unchanged; its realized arrays contain no required
node assignments bypassed by this proof.

## Where the brief, the DAG or earlier work was wrong

The planned passage from module higher-direct-image vanishing to abelian higher-image vanishing
is unnecessary. Work entirely in module sheaves through the common pushed-forward resolution,
then forget scalars and reuse the existing natural source-model comparison. This avoids a new
forgetting-coefficients comparison for higher images and the topological Leray spectral sequence.
The mathematical statement was not disputed or altered. No tool failures or forced adaptations.

## Second reading by C2

1. **Statements and interfaces.** Compared the delivered module and node with the repository
version. The theorem signature is byte-for-byte unchanged, and the node statement still has
the same hypotheses and conclusion. Verdict: pass.
2. **Proof and trust boundary.** Compiled the module with `lcompile.py`; it has no `sorry`,
`axiom`, `unsafe`, `opaque`, `extern`, or `implemented_by`. The proof uses only the named
acyclic-resolution, injective-acyclicity, sections-resolution, and source-comparison
interfaces. A scratch-copy `#print axioms` of the public theorem reports exactly
`propext`, `Classical.choice`, and `Quot.sound`, with no `sorryAx`. Verdict: pass.
3. **Split statements and searches.** No split-off theorem was added; the helper is private
and fully proved. The recorded searches include LeanSearch, LeanFinder, and grep, and no
existing declaration was duplicated. Verdict: pass.
4. **Route and pruning.** The proof follows the direct common-resolution route and preserves
the unit route; the unit's `realized` arrays are empty. The node's proof and `proof_deps` match
the imports and actual calls, and the old topological/abelian comparison dependencies are
removed from the route. Verdict: pass.
5. **Nodes and edge cases.** The JSON diff changes only `proof`, `proof_deps`, and
`proof_origin`; all five dependencies match the existing declarations used in the proof.
No new nodes are required. Degree zero, zero coefficients, and empty schemes are
covered uniformly by the categorical argument. I updated the theorem docstring so its proof
matches the implemented route, then recompiled successfully. Verdict: pass.

Changed only the theorem docstring; no statements, definitions, imports, or DAG interfaces
were changed.
