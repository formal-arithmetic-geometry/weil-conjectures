## What changed

Proved `AlgebraicGeometry.ordinaryEvaluation_precomposition_naturality` in
`Sheaf.AlgebraicGeometry.OrdinaryEvaluationPrecompositionNaturality`, without changing
its signature, definitions, existing docstring, visibility, or public imports. Added the proof-only import
`Sheaf.AlgebraicGeometry.OrdinaryEvaluationComponentFactorization`. Private proved
helpers establish evaluation precomposition, module-evaluation naturality,
and scalar compatibility. Component factorization is split off separately.
These implement the existing node's proof plan.
The tensor identities are proved for an arbitrary sheaf of rings and specialized to
`X.sheaf.over U`, avoiding expensive inference through the scheme's localized site.

The proof factors each nonzero component through `moduleDualEvaluation`, postcomposes
the assumed projection identity with the unit identification, and uses tensor additivity
and evaluation naturality. Functoriality of `homObjMap` and composition of `XIsoOfEq`
finish the output transport. The precomposition and scalar helpers are proved. The nonzero component
factorization remains as one named public theorem in a new module. Its generic
tensor calculation was proved in scratch, but the final definitional match to the
scheme-local component exceeded elaboration limits; the documented statement
is strictly the factorization step, without maps a,f or the scalar z.

Searches: Lean Finder for tensor-evaluation precomposition returned generic evaluation
naturality; Loogle for `CategoryTheory.MonoidalClosed.uncurry` returned the generic
uncurrying API; Mathlib grep for tensor-Hom naturality found no exact projected identity.
LeanSearch for the factorization was unavailable (Internal Server Error).
Repository searches found the private evaluation-naturality proof in
`FiniteProjectiveInternalHomEvaluation`, whose tensor-Hom argument is reused here with
private helpers. Read the cited Stacks Tags 08DQ and 03EO online: the former describes
the ordinary evaluation map and the latter its natural tensor-Hom construction.

## Proved and sorry left

Closed the one hole in
`AlgebraicGeometry.ordinaryEvaluation_precomposition_naturality`
(node `lem-pc-ordinary-evaluation-precomposition-naturality`).
No `sorry` remains in the item's module. One hole is split off as
`AlgebraicGeometry.ordinaryEvaluation_component_factorization` in
`Sheaf.AlgebraicGeometry.OrdinaryEvaluationComponentFactorization`
(node `lem-pc-ordinary-evaluation-component-factorization`).
This is a decomposition: one hole closed and one strictly smaller hole added.
Existing dependencies, including the Hom-complex projection construction, are unchanged.

## No longer needed

None. The unchanged public import `Sheaf.AlgebraicGeometry.OrdinaryEvaluationData`
is required by the statement and definitions. The additional DAG dependency
`lem-pc-finite-projective-internal-hom-evaluation` supplies the real definition
`SheafOfModules.moduleDualEvaluation`, already publicly available through the data module.
Both existing proof dependencies,
`def-pc-ordinary-evaluation-data` and `lem-pc-sheaf-modules-tensor-closed`, remain used.
No node, module, or unit step is bypassed. The new factorization module is the
only proof import added.

## Where the brief, the DAG or earlier work was wrong

No mathematical or interface error found. The unit record
`dag/units/sk-thm-picard-duality.json` has no realized nodes for this item; the
existing node-level evaluation-naturality route is retained. The existing node's proof, proof_deps, and proof_origin now record the factorization
step. No interface change or change record is needed.

## New nodes

`lem-pc-ordinary-evaluation-component-factorization` states the positive-branch
component formula factored through ordinary module evaluation. It has no
precomposition maps, scalar, assumed projection relation, or naturality conclusion,
so it is strictly smaller than the item. Its proof uses only the definition,
tensor-Hom naturality, and the already-defined module evaluation map. The new
module contains exactly the one named public `sorry`. Zero modules and arbitrary
unbounded complexes require no additional hypothesis, and degree equalities are
proof-irrelevant. No change record is required.

## Second reading by C1

1. Compared the full existing module with the repository using diff, and compared
   its theorem signature byte for byte: identical. The only existing-file edits
   are private proved helpers, the target proof, and one plain proof-only import.
   No definition, existing docstring, visibility, or public import changed. No
   change record or forced adaptation is required. Verdict: pass.
2. Compiled both delivered modules in import order with lcompile.py: clean, with
   no warnings. Inspected every delivered declaration: no forbidden declaration
   form, no data definition added, no hidden or anonymous sorry. The only sorry
   is the named public component-factorization theorem, with its matching node
   and complete docstring proof. The scratch #print axioms probe for the target
   and factorization shows only propext, Classical.choice, Quot.sound and sorryAx;
   the latter is accounted for by the reported open dependencies. Verdict: pass
   as a decomposition, not a sorry-free proof of the item.
3. Read localEvaluationComponent and moduleDualEvaluation side by side. With
   r+q=0 the positive branch applies, and p+q=n gives p=r+n. The claimed formula
   is precisely the projection/degree-zero unit identification followed by
   module evaluation and output transport. Tensor-Hom naturality and braiding/
   associator naturality give the written proof; no finite-projectivity or
   boundedness hypothesis is needed for this equality. For p=q=n=r=0 it is
   ordinary b tensor phi evaluation; for r=-q and arbitrary n the same transport
   applies; zero input/output modules yield the zero morphism. Thus the new lemma
   is true and strictly smaller: it has no a, f, z or projection-relation
   hypothesis and proves only the component expansion. Read Stacks
   [08DQ](https://stacks.math.columbia.edu/tag/08DQ), proof of
   lemma-dual-perfect-complex, for the canonical evaluation map, and
   [03EO](https://stacks.math.columbia.edu/tag/03EO) for functorial tensor-Hom
   adjunction. Searched repository and slopmaster2 by moduleDualEvaluation,
   localEvaluationComponent, evaluation_factor and component_factor; the
   available upstream naturality proof is private, and no existing public exact
   factorization was found. Independent Lean Finder, Loogle and grep searches
   found generic curry/uncurry laws, not the scheme-local component formula.
   Corrected the new node's search entries to actual logged queries/results,
   marking the failed LeanSearch request unavailable. Verdict: pass.
4. Traced the target proof: factor the two components, postcompose ha with the
   unit identification, move the scalar through additive tensoring, apply proved
   evaluation naturality, and compose XIsoOfEq transports. All private helpers
   have real proofs. No shorter available public theorem was found. The plain
   factorization import is proof-only, and OrdinaryEvaluationData is needed by
   the signature. Both old proof dependencies remain used; No longer needed is
   complete (none). Read sk-thm-picard-duality.json: realized.statement and its
   realized step are empty, and no realized unit node is bypassed. Tried closing
   factorization with the already-proved generic tensor calculation and explicit
   localized-site parameters in scratch; specialization timed out at 60 seconds.
   Kept the valid smaller hole rather than changing any definition. Verdict: pass.
5. Compared both nodes with Lean. The existing node changes only proof,
   proof_deps and proof_origin; its statement and lean signature are unchanged.
   The new node's verbatim Lean signature, chapter/unit, creation attribution,
   blueprint provenance, source, complete proof and dependency union agree with
   the module. tensorClosed supplies additivity, OrdinaryEvaluationData supplies
   the component/projection constructions, and the internal-Hom evaluation node
   supplies moduleDualEvaluation. Clarified that additional DAG dependency in
   No longer needed. Verdict: pass.

Second reading changed only the new node's search metadata and this report
(including the dependency clarification); no Lean proof or interface was changed.
One item hole is closed and one strictly smaller hole is added: net zero holes.
