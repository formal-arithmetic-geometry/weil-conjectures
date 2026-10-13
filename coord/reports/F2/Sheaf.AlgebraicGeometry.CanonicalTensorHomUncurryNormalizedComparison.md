## What changed

Replaced AlgebraicGeometry.tensorHomUncurry_normalized_comparison's hole by an unchanged-signature proof. Componentwise tensor-Hom and braiding naturality prove that uncurrying factors through evaluation of the identity of the Hom complex. Localization and tensor-model input naturality identify the normalized output with its normalized input tensor identity followed by evaluation. Generic categorical helpers combine the given equality of inputs with the evaluation square.

Added CanonicalTensorHomEvaluationNaturality and CanonicalTensorModelInputNaturality. Updated the original DAG proof to follow this factorization. No existing statement, definition, visibility or public import changed. No data was chosen from an unproved existence theorem.

## Proved and sorry left

Closed AlgebraicGeometry.tensorHomUncurry_normalized_comparison (lem-pc-tensor-hom-uncurry-normalized-comparison).

Added AlgebraicGeometry.tensorHomEvaluation_natural (lem-pc-tensor-hom-evaluation-naturality), currently sorry. This is the square for identity evaluation in its two variables: it has neither P/P' nor phi/phi' nor an equality hypothesis. It is strictly the evaluation-naturality part of the argument, combined with a proved input factorization and tensor algebra. Zero inputs and identity comparisons satisfy this square; no flatness or boundedness is required.

Added AlgebraicGeometry.tensorModelMap_input_natural (lem-pc-tensor-model-input-naturality), currently sorry. It is merely the first-variable naturality of the localization tensor map, with no internal Hom or evaluation. It requires no flatness because no inverse tensor comparison is used. Two holes are added and one is closed: the net hole count increases by one; this is a decomposition.

This delivery is a decomposition, not an axiom-free proof of the whole derived evaluation argument. No sorry remains in the original module or any private helper.

## No longer needed

Removed proof imports Sheaf.Algebra.Homology.KFlatResolution, Sheaf.Algebra.Homology.KInjectiveHomComplex, Mathlib.Algebra.Homology.DerivedCategory.KInjective and Sheaf.Algebra.Homology.HomComplexGlobalCochains from the original module. They are not needed directly by its formal combination proof. Nodes lem-pc-kflat-resolution, lem-pur-hom-kflat-into-kinjective, lem-weil-pbc-kinjective-hom-derived and lem-pur-hom-complex-global-cochains remain needed in the new evaluation-naturality node's proof plan: they are relocated dependencies, not globally pruned theory. No claim is made that a module leaves the targets' closure.

The public differential import remains necessary for the signature and construction. No unit route or unit statement was bypassed; all changes are below the unit level.

## Where the brief, the DAG or earlier work was wrong

The listed dependencies do not themselves expose the normalized evaluation square or the chain-input factorization. The latter is now proved directly; the former is explicitly isolated with a complete proof plan. A generic existential tensor-Hom isomorphism without component normalization cannot substitute for this square.

Lean elaboration is expensive when rewriting the full chosen Hom-complex expressions. Generic categorical helpers avoid repeated rewriting inside these choices. Several intermediate failed attempts hit the single-file timeout; the final implementation uses abstract composition and tensor lemmas instead.

LeanSearch returned Internal Server Error. LeanFinder, Loogle and source searches were run; the generic lax tensor naturality lemma exists, while no normalized evaluation square was found. The cited Stacks pages 08DJ, 0A90 and 0A96 were read online because the local Stacks source files are absent.

## New nodes

lem-pc-tensor-hom-evaluation-naturality, in lean/Sheaf/AlgebraicGeometry/CanonicalTensorHomEvaluationNaturality.lean: the localized identity evaluation square in L and M, extracted from the original proof's naturality and roof-cancellation steps.

lem-pc-tensor-model-input-naturality, in lean/Sheaf/AlgebraicGeometry/CanonicalTensorModelInputNaturality.lean: specialization of lax monoidal localization naturality to a chain map in the first tensor variable. Existing interfaces are unchanged. The fetched delivery base no longer contains the assigned module or its node, so coord/changes/tensorHomUncurry_normalized_comparison.md records its restoration.

lem-pc-tensor-hom-uncurry-normalized-comparison is restored with the unchanged assigned statement, since the latest fetched delivery base lacks this node and module.

## Second reading by F2

1. I compared the assigned theorem signature with its DAG record and the available repository state. The repository checkout has no original file at this path, while the DAG record preserves the original signature; the delivered theorem matches it byte for byte. The two added theorem signatures match their new DAG nodes, including all hypotheses and let-bound instances.

2. I compiled all three delivered Lean modules with `lcompile.py --all`; they compile cleanly. The assigned theorem has no `sorry`; the only remaining `sorry`s are the two named split-off theorems, each public, documented with its source and proof plan, and represented by a DAG node. No axiom, unsafe, opaque, extern, or hollow definition occurs. Explicit #print axioms checks on all three public theorems report only propext, Classical.choice, Quot.sound, and the expected sorryAx; the assigned theorem was checked from a scratch importer of its compiled module. The attempted direct proof of tensor-model naturality was tested against `Functor.LaxMonoidal.μ_natural`; the remaining mismatch is the non-definitional identification of the project tensor object with `pullbackTensorTotal`, so I left the documented split rather than changing its statement.

3. Split statements: The original proof's component factorization uses the explicit component uncurrying equation and braided tensor-Hom naturality. The localization factorization uses the stated input naturality node, and the final comparison uses the stated evaluation square. The formal helper lemmas are strictly smaller algebraic steps, not restatements of the assigned theorem. The source route is preserved below the unit level; no unit statement is bypassed. The Mathlib searches and source searches are recorded in `searches.jsonl` and the node records.

4. Pruning and route: The four removed proof-dependency imports are listed individually under No longer needed. Their nodes remain in the evaluation-naturality plan, so this is relocation, not global pruning. I opened dag/units/sk-thm-picard-duality.json: its realized.statement and its sole realized.steps entry are empty; none is changed. I checked edge cases described by the node docstrings: identity and zero maps, zero complexes, and unbounded complexes introduce no additional hypotheses. The naturality split statements impose no flatness or boundedness beyond the assigned theorem's existing K-flat assumptions. The Stacks source places (08DJ, 0A90, 0A96, and 06YH) agree with the evaluation and lax-monoidal naturality claims used by the reduction.

5. DAG agreement: The original node's three steps match component_input/uncurry_input, localized_factor/localized_uncurry_input, and evaluation_comparison/comparison_of_factorizations, with proof_deps exactly their cited node union. Both new nodes have chapter, unit, source, creation, provenance and search records. I repaired their lean.statement fields to contain the verbatim multiline signatures and removed stale reviewed/reviewed_proof metadata from the restored node: the previous P2 interface review does not certify this new proof. I changed only the attempted proof body of the tensor-model naturality split back to its documented `sorry` after the direct Mathlib proof reached a genuine definitional-structure mismatch; the assigned proof and its signature are unchanged. I added this second-reading record. No imports or existing declarations were changed. The permanent second-reading repairs are verbatim new-node signature records, this report, and setting backward.isDefEq.respectTransparency.types true in the assigned module. After two fluctuating 60-second timeouts, the unchanged proof compiled with that elaboration setting in 56.8 seconds. No definition was altered or module split.
