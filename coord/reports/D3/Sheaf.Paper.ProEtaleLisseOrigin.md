## What changed

The unchanged statement `AlgebraicGeometry.Scheme.proEtale_lisse_origin` now has a complete
Lean proof from finite local models. Its public imports and the definition
`IsLisseProEtaleFixedModuleSheaf` are unchanged. Seven new modules record the actual route;
six are proved, and one isolates the fixed finite-module trivialization step of Stacks 099Y.
The existing node's proof and proof dependencies follow this route. No existing statement,
definition, target signature, or consumer interface was changed, so no change record or
forced consumer adaptation is needed.

The forward implication transports finite etale models through the existing comparison
pullback and constant-sheaf adjunctions, then uses the proved fixed-coefficient finite-model
local-constancy and geometric-stalk helpers. The reverse implication removes empty members
of a pro-etale cover while preserving quasi-compactness, computes finite models from stalks,
descends module-type opens by fpqc descent, and reduces to one uniform finite module on each
open. It constructs the etale origin explicitly as comparison lower star, proves its finite
local constancy, and proves the global counit invertible by a mate calculation and local
conservativity. No definition chooses arbitrary data from an unproved existence theorem.

## Proved and sorry left

Original hole closed: `AlgebraicGeometry.Scheme.proEtale_lisse_origin`, 1 of 1.

New proved theorems, with no direct holes:

- `AlgebraicGeometry.Scheme.comparison_finite_models_of_etale_finite_values`
- `AlgebraicGeometry.Scheme.finite_models_of_fixed_lisse`
- `AlgebraicGeometry.Scheme.comparison_counit_restriction_isIso`
- `AlgebraicGeometry.Scheme.proEtale_model_type_opens`
- `AlgebraicGeometry.Scheme.etale_cover_of_proetale_finite_models`
- `AlgebraicGeometry.Scheme.etale_origin_of_finite_models`

One hole added and remaining:
`AlgebraicGeometry.Scheme.etale_cover_of_proetale_uniform_model`, in
`Sheaf.Paper.ProEtaleUniformModelEtaleCover`, node
`lem-sf-proetale-uniform-finite-model-etale-cover`.
Its proof is exactly `by sorry`. Its docstring gives the source and complete proof in words.
It still needs the fixed-coefficient Isom sheaf construction, the finite-presentation
constant-Aut comparison (or transport of the ringed-site Isom theorem with the required
universe and slice compatibilities), then the existing locally-classical etale-section
comparison and point-indexed shrinking of the cover. The finite module is fixed in advance;
this is strictly the uniform trivialization step, with no geometric-stalk hypothesis and
no assertion about comparison origins. The zero module, zero ring and empty base are included.

This is a decomposition, not a net hole reduction or an axiom-free proof of the target:
one upper hole closed, one strictly lower hole added, net zero direct holes. Other imported
library holes remain the obligations of their existing nodes. All definitions and private
helpers in this delivery have actual constructions/proofs and no direct holes.

## No longer needed

Removed direct proof imports from the item:

- `Mathlib.CategoryTheory.Sites.ConstantSheaf`
- `Mathlib.CategoryTheory.Sites.Sheafification`
- `Sheaf.CategoryTheory.SiteConstantModuleIsomSheaf`
- `Sheaf.AlgebraicGeometry.FpqcOpenSubschemeDescent`
- `Sheaf.AlgebraicGeometry.ProEtaleConstantSheafStalk`
- `Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization`
- `Sheaf.AlgebraicGeometry.ComparisonPullbackCoherence`
- `Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory`
- `Sheaf.AlgebraicGeometry.ProEtaleLocallyClassicalEtaleCover`
- `Sheaf.AlgebraicGeometry.ProEtaleSiteComparisonFiniteLevel`

The Isom, fpqc-descent, weakly-etale-localization and locally-classical imports are relocated
to the new helper modules where needed. Constant-sheaf/sheafification APIs remain available
through the imports used by those proofs. Derived-category and comparison-coherence modules
remain transitively reachable; removing their direct imports is not global pruning.

Comparing the complete import graph of the shared source snapshot with this sandbox,
`TargetsCheck` no longer reaches these four modules:

- `Sheaf.AlgebraicGeometry.ProEtaleConstantSheafStalk`
- `Sheaf.AlgebraicGeometry.ProEtaleSheafificationGeometricStalk`
- `Sheaf.AlgebraicGeometry.ProEtaleSiteComparisonFiniteLevel`
- `Sheaf.RingTheory.WeaklyEtaleField`

The item's own closure additionally drops `Sheaf.RingTheory.IndPrincipalZariski`, but other
target paths still reach it. These are import-graph observations, not ledger progress figures;
concurrent landings may change the closure. None realizes a statement or step of this unit
(the unit's `realized.statement` and `realized.steps` records are empty).

The old direct proof dependencies `lem-weil-proetale-constant-sheaf-stalk`,
`prop-weil-pbc-site-comparison-finite-level`, and `lem-weil-pbc-comparison-pullback` are replaced
by the existing fixed-coefficient geometric-fiber API and the proved source comparison
adjunction, pullback and unit APIs. The underlying mathematical steps are retained; the
ringed-interface wrappers are unnecessary for this proof. Other old dependencies now occur
inside the relevant helper nodes rather than directly in the item's proof dependencies.

## Where the brief, the DAG or earlier work was wrong

The planned Isom lemma `siteConstantModule_isomSheaf` is stated for `SheafOfModules` over the
constant ring sheaf on a small category with equal object/hom universes. The item uses
fixed-coefficient `Sheaf (...)(ModuleCat Λ)` on scheme sites with objects in universe u+1
and morphisms in universe u. The existing Isom lemma therefore does not directly provide
the needed fixed-coefficient torsor. Its transport, including slices and universes, belongs
to the one remaining uniform-model theorem. This is an interface gap, not a claim that the
mathematical statement is false. The existing etale ZMod-only constant-ring module
equivalence does not provide the arbitrary-Λ pro-etale bridge either.

The proved source module `WeilConjectures.SixFunctors.ProEtale.ConstructibleSheaf` has a
matching forward finite-model argument, but imports finite-local-constancy reflection,
which imports this item. Importing it here would create a cycle. Its existing comparison
and localization dependencies can be used directly and are used by the new forward proof.

The source's removal of empty covering members needs an explicit quasi-compactness check
for the implemented pro-etale precoverage; the new finite-model proof supplies this through
finite affine refinements. Type opens in the implementation can repeat for isomorphic
models, so they are used as a covering family, without a false disjointness assertion.

## New nodes

`lem-sf-comparison-finite-models-of-etale-finite-values`, module
`Sheaf.Paper.ProEtaleLisseFiniteModels`: proved transport of etale finite constant models
through comparison. Its constant-comparison isomorphism is constructed from adjunctions.

`lem-sf-proetale-lisse-finite-models`, module
`Sheaf.Paper.ProEtaleLisseFiniteModelsFromLisse`: proved extraction of finite models from
local constancy and finite geometric stalks, including deletion of empty cover members.

`lem-sf-proetale-comparison-counit-localization`, module
`Sheaf.Paper.ProEtaleComparisonLocalization`: proved compatibility of invertibility of the
comparison counit with etale restriction, using the mate and pullback-projection calculations.

`lem-sf-proetale-model-type-opens`, module `Sheaf.Paper.ProEtaleModelTypePartition`:
proved fpqc descent of the model-type loci, without a finiteness hypothesis on the models.

`lem-sf-proetale-uniform-finite-model-etale-cover`, module
`Sheaf.Paper.ProEtaleUniformModelEtaleCover`: the sole new hole, the uniform finite-model
Isom-sheaf and etale-section step described above. No clause of the original theorem is
restated under another name.

`lem-sf-proetale-finite-models-etale-cover`, module
`Sheaf.Paper.ProEtaleEtaleFiniteModels`: proved combination of the type opens and uniform
trivializations, with explicit handling of empty pullbacks and universe-small cover indices.

`lem-sf-proetale-origin-from-finite-models`, module
`Sheaf.Paper.ProEtaleOriginFromFiniteModels`: proved construction of the finite locally
constant origin as comparison lower star and proof that its counit is invertible.

## Second reading by D3

1. I compared `Sheaf.Paper.ProEtaleLisseOrigin` with the repository version. The
`IsLisseProEtaleFixedModuleSheaf` definition and `proEtale_lisse_origin` theorem signature
are byte-for-byte unchanged. The helper modules are new files; no existing consumer module
or target statement is adapted, and no change record is required. Verdict: pass.

2. I compiled all eight delivered modules in sandbox import order with `lcompile.py`; they
compile without errors or warnings. The only literal `sorry` is the named theorem
`AlgebraicGeometry.Scheme.etale_cover_of_proetale_uniform_model`, and its docstring gives
its source, a complete proof plan, and the matching split node. There are no `axiom`,
`unsafe`, `opaque`, `implemented_by`, `extern`, or hollow definitions. The direct proofs
of the six other new theorems use only `propext`, `Classical.choice`, and `Quot.sound`;
`#print axioms` reports `sorryAx` for declarations that transitively use the one split
uniform-model theorem. Verdict: pass.

3. I checked the split statement against the fixed-model step it isolates. Its finite
module, finite coefficient ring, and pro-etale covering hypotheses are explicit, its
conclusion is exactly an etale covering with the same model, and it adds no geometric-stalk
or comparison-origin hypothesis. The zero and empty cases are covered by the statement.
The theorem is strictly below the target and is not a restatement of it. I searched the
library for an existing fixed-model etale-trivialization theorem and found none; the
existing Isom-sheaf theorem has incompatible ringed-site universe parameters as described
above. Verdict: pass.

4. I checked the proof from the target downward. The forward clause uses the finite-values
characterization, comparison transport, finite-model local constancy, and finite geometric
stalk theorem. The reverse clause uses finite model extraction, model-type open descent,
the fixed-model split, and the comparison-lower-star origin construction. The main module
imports only declarations used by its statement or proof; the removed proof-only imports
are listed under `## No longer needed`. The unit record has no realized statement or steps,
so no unit route is bypassed. Verdict: pass.

5. I checked every delivered node's declaration, statement, proof steps, proof dependencies,
source, and proof origin against the Lean proof. Each new node has the required metadata and
its `lean` record matches the declaration. The existing target node retains its statement
and now records the helper route; the one remaining split node records the exact unresolved
uniform Isom-sheaf and locally-classical descent step. Verdict: pass.

I changed only this report by adding this second-reading audit. No Lean source, statement,
definition, node, or import required repair.
