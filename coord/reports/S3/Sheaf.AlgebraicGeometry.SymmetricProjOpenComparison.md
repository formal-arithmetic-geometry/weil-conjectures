## What changed

The original theorem `AlgebraicGeometry.SymmetricProjTautologicalCharts.open_compatibility_of_normalized_quotient`
now assembles the witnesses for every open V. Tensor pullback preserves quasi-coherence;
existing normalized descent supplies DV. The new proved symmetric-algebra construction supplies
coefficientwise pullback data with the actual generator formula. The existing source-library
`PullbackData.isPullback` supplies the comparison map and its pullback square. The remaining
quotient-line comparison supplies its line isomorphism and the exact quotient equation. The supplied equality proof is
already guaranteed by the pullback square; proof irrelevance makes its choice immaterial.

`SymmetricAlgebraPullbackData` constructs the affine ring maps by symmetric-algebra lift from
the normalized pullback unit. It proves degree preservation by induction on submodule powers,
bijectivity using affine tensor sections and symmetric algebra base change, degreewise
bijectivity using the homogeneous decomposition, and restriction naturality in both variables.
Its intermediate definitions and lemmas are private and proved.

Each delivered module locally prioritizes `CategoryTheory.Abelian.hasFiniteLimits`, matching
the instance used by the original normalized-quotient definitions. The new BaseChange import
otherwise selects the countable-limit-derived instance, causing the kernel to unfold large
sheafification terms when comparing equivalent module types. The local priority changes no
global instance. Temporary profiling, type comparisons, and diagnostic proofs are removed.
The line theorem takes a proof of the module-object equality induced by the already proved
pullback square. The final assembly passes the transport proof already occurring in the
original predicate. Its small kernel-checked tactic locates that `eqToIso` proof and applies
the line theorem with the existing witnesses. This preserves the exact quotient equation and
avoids normalizing the generated auxiliary proof against a separately written `congrArg`.

`SymmetricProjQuotientPullbackComparison` states only the remaining comparison of the two fixed
quotient lines along a fixed generator-normalized relative-Proj map. It neither constructs the
quotients nor asserts a pullback square. It is a strict part of the argument, also valid for
an arbitrary base morphism. The original theorem's signature and public import are unchanged;
its four additional imports are proof imports. No adopted source-library file is changed.

Remote Lean validation passed without warnings: `SymmetricAlgebraPullbackData` in 21.9 s,
`SymmetricProjQuotientPullbackComparison` in 13.2 s, and the item in 15.2 s. Every file
is below the unchanged 60-second limit.

## Proved and sorry left

Closed the one original direct hole in
`AlgebraicGeometry.SymmetricProjTautologicalCharts.open_compatibility_of_normalized_quotient`
(node `lem-trf-symmetric-proj-open-comparison`) by a complete witness assembly.

Proved the new theorem
`AlgebraicGeometry.SymmetricAlgebraSheaf.exists_normalized_pullbackData`
(node `lem-trf-symmetric-algebra-normalized-pullback-data`) and all its private helpers.

Added one direct hole, exactly the complete proof of
`AlgebraicGeometry.SymmetricProjTautologicalCharts.quotient_comparison_of_normalized_pullbackData`
(node `lem-trf-symmetric-proj-quotient-pullback-comparison`). Its docstring and node contain
the frame-by-frame construction, transition-ratio compatibility, gluing argument, quotient
normalization, and edge cases. No other hole is left or added by this delivery.

The count is one hole closed and one added: a decomposition with net zero holes removed,
not a complete proof of the original mathematical obligation. Existing normalized-descent
and affine-pullback-section dependencies remain usable stage-3 dependencies.

## No longer needed

No existing module is withdrawn and no existing public import is removed. Pruned modules: none.
The parent's previous separate construction of the inverse-image-open relative Proj using
`existsUnique_relProjIso` is replaced by the already proved `PullbackData.isPullback` API.
Accordingly `lemma-nagata-relative-proj-exists` is no longer a direct proof dependency of this
node, although the source BaseChange module still imports Universal and its results remain
needed there. Definitions in the original statement dependencies are retained.

The separate ordinary-pullback quasi-coherence node is replaced in the direct proof by
`def-weil-pbc-tensor-pullback-ordinary-comparison`, whose tensor instance has exactly the
required type. Ordinary pullback quasi-coherence is still used transitively by that instance.
The symmetric-algebra-base-change node remains necessary in the new algebra proof. Affine
restriction data returned alongside DV are unnecessary to this witness assembly, because the
fixed-comparison line theorem works for arbitrary normalized quotients.

## Where the brief, the DAG or earlier work was wrong

No false statement was found. The recorded ordinary-pullback quasi-coherence declaration
alone does not directly give an instance for tensorPullback; the existing tensor/ordinary
comparison supplies the precise instance. The relative Proj source already proves arbitrary
coefficientwise base change, so redoing scheme gluing and chart uniqueness is unnecessary.
The actual missing algebra interface was generator-normalized PullbackData between the two
canonical symmetric graded algebras; this delivery proves it.

Checked the mathematical edge cases: arbitrary nonaffine V needs no intersection to be
affine, since the affine-pair BaseChange API handles refinements; V empty, E zero and the
zero coefficient ring are permitted by all tensor, symmetric-algebra and grading proofs.
Nilpotent degree-one generators give empty localization charts in the remaining line proof.
No finite generation, finite rank, flatness or separation assumption is added.

The current blueprint unit `sk-i-curve-zero` and its realized route are unchanged. The latest
blueprint was searched for symmetric algebra pullback and normalized quotient: no duplicate
statement was found. Searches of the library and Mathlib found the existing affine sections,
symmetric-algebra base change and relative-Proj base-change APIs used here, but no theorem
of the normalized quotient-line comparison.

## New nodes

`lem-trf-symmetric-algebra-normalized-pullback-data` attaches the proved construction in
`Sheaf.AlgebraicGeometry.SymmetricAlgebraPullbackData`. It is the affine coefficient
identification part of the original node's second step, with the generator normalization
needed for the quotient.

`lem-trf-symmetric-proj-quotient-pullback-comparison` attaches the one remaining named theorem
in `Sheaf.AlgebraicGeometry.SymmetricProjQuotientPullbackComparison`. Its inputs include the
already supplied normalized quotients and the fixed generator-preserving coefficient data;
its conclusion concerns only the line isomorphism and quotient equation. It contains neither
existence of normalized quotients nor the geometric base-change conclusion.

## Second reading by S3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
