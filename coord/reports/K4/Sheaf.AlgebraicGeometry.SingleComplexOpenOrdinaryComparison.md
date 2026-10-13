## What changed

Reduced `AlgebraicGeometry.exists_singleComplexOpen_ordinary_comparison` to two
strictly separate intermediate statements. `BaseDerivedTensorRingTransport`
treats arbitrary compatible coefficient-ring isomorphisms and the localized
base-derived comparison. `OpenOrdinaryTensorGermTransport` supplies open stalk
coordinates and identifies the ordinary target path. The original module
imports both privately and combines their squares with a complete Lean proof.
All existing signatures, visibility, definitions and docstrings are unchanged.

The proof explicitly unfolds `tensorComplex` and uses
`RingHom.algebraMap_toAlgebra` to match the geometric ordinary complex with the
generic scalar-extension complex. A local instance inside the definition of W
pins its derived-category universe to w. The final composition uses functoriality
and associativity. The heartbeat budget is scoped to the theorem; compilation
remains below the 60-second single-file limit.

An unchanged copy of `SingleComplexOpenTensorRestrictionIso` is present solely
so lcompile.py can compile this missing published dependency in sandbox import
order. It is byte-for-byte identical to the repository file, is not an adaptation,
and introduces no delivery change.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.exists_singleComplexOpen_ordinary_comparison`, node
`lem-pc-single-complex-open-ordinary-comparison`. This is a decomposition into
two smaller statements, not a proof from standard axioms alone. The original
module now has no sorry. Its already-proved
`AlgebraicGeometry.comparisonIntoPullback_comp_counit` is unchanged.

Added two holes, each exactly `:= by sorry` in its own public theorem:

- `ModuleCat.exists_baseDerivedTensor_ring_transport`, node
  `lem-pc-base-derived-tensor-ring-transport`.
- `AlgebraicGeometry.exists_openOrdinaryTensor_germ_transport`, node
  `lem-pc-open-ordinary-tensor-germ-transport`.

There are no holes in definitions or private declarations. All statements and
the combining proof compile. The unchanged auxiliary dependency contains no sorry and is not modified.

## No longer needed

No imports removed and no whole modules pruned. The public imports are needed
by the existing statements and counit lemma. `AffineSpectrumOrdinaryComparisonSquare`
provides the general `comparisonIntoTensorPullback` definition; its affine
comparison theorem is not used. `StalkComparisonPullbackNaturality` provides the
existing `comparisonIntoPullback` definition; its K-flat naturality theorem is
not used. The fixed-square source-transport theorem cannot alone change all four
coefficient rings. The restriction-stalk extension remains needed in the new
ordinary germ transport node. Existing definitions and statement dependencies
remain; the item's proof dependencies now record the two new reductions and
the definitions actually expanded by the combining proof.

## Where the brief, the DAG or earlier work was wrong

The previous attempt could not load the published artifact for
`SingleComplexOpenTensorRestrictionIso`. Its unchanged source compiles through
lcompile.py when included in the sandbox, which allows the draft to be checked.
No project tool or library source was modified for this. The earlier draft also
needed the derived universe of W pinned locally, explicit scalar-extension
unfolding, and a final associativity step. Those are repaired.

The generic transport statement contains no schemes, open restriction map beta,
or derived additive stalk comparison nu. The geometric statement contains no
base-derived cohomology source or localizedComparison. Neither restates the
original theorem. The unit record has no realized nodes, and the reduction
preserves the original ring-coordinate, derived-source, ordinary-target route.

Edge cases were checked: coefficient equivalences permit zero rings and zero
complexes; no base flatness or K-flatness is introduced. Empty opens have no z.
Top opens and arbitrary cohomological degrees use the same germ formulas.
The universal counit, cohomology action and localized_eq fields fix the generic
comparison, so the statement does not assert arbitrary comparison maps agree.

The inherited searches.jsonl records LeanFinder, Loogle and grep searches.
Two additional LeanSearch queries were run for the new statements; both returned
Internal Server Error and are recorded as unavailable, not as no match.
Direct rg also inspected both library roots and Mathlib. The fixed-square
SourceTransport changes representatives, whereas this theorem changes the
coefficient rings. Sources reread online include Stacks Tags 06Y6, 0098 and
0DJ7. They supply derived scalar-extension functoriality, pullback stalk tensors,
and the exact comparison map whose open compatibility is being reduced.

## New nodes

`lem-pc-base-derived-tensor-ring-transport`, module
`Sheaf.Algebra.Homology.BaseDerivedTensorRingTransport`, isolates compatible
coefficient equivalences and the square for localizedComparison before ordinary
stalk identifications. Its proof uses universal derived functor uniqueness,
tensor-action compatibility and the scalar-extension adjunction.

`lem-pc-open-ordinary-tensor-germ-transport`, module
`Sheaf.AlgebraicGeometry.OpenOrdinaryTensorGermTransport`, isolates the four open
stalk ring isomorphisms, semilinear input and pure-tensor ordinary complex
coordinates, and their ordinary target-path equation. Both modules are new
proof items with a source and complete proof in words. No change records or
forced adaptations are required.

## Second reading by K4

1. Compared the delivered target module with the repository version. Existing declaration signatures and definitions are unchanged; only proof imports, the theorem proof, and the two newly split theorem modules differ. Verdict: pass.
2. Compiled all sandbox modules with `lcompile.py --all`; compilation succeeds. The only remaining `sorry`s are the two named split theorems, with no `sorry` in definitions or forbidden declarations. Verdict: pass.
3. Checked both split statements against their docstrings and DAG nodes. They are strict reductions: coefficient transport and ordinary germ transport separately, rather than restating the target. Their edge-case discussion covers zero rings, empty opens, top opens, and zero complexes. Verdict: pass.
4. Reviewed the proof route and imports. The target combines the two split results, unfolds `tensorComplex`, uses `RingHom.algebraMap_toAlgebra`, and reassociates functorial compositions. The auxiliary HomologicalComplex imports are proof-only and are private imports; no additional pruning was found. Verdict: pass.
5. Checked DAG `proof`, `proof_deps`, `proof_origin`, and the unit route. The target node records both reductions and the final elementary composition; the split nodes carry sources, proof plans, and matching Lean declarations. Verdict: pass.

I changed the two auxiliary Mathlib HomologicalComplex imports from public to private imports because they are needed only by proofs. No statements or definitions were changed. The required unchanged `SingleComplexOpenTensorRestrictionIso` copy remains solely for sandbox import order.
