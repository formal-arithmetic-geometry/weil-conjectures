## What changed

Separated the unchanged twelve definitions into `Sheaf.Paper.FiniteTateSiteDescentDefinitions`,
publicly reexported by the original item module. Split the existence/normalization and
pullback/exponent coherence arguments into two genuinely separate results. The original theorem
now combines these results and proves uniqueness of exponent transitions and uniqueness of
comparison-preserving etale descents by the fully faithful isomorphism equivalence.

The four delivery modules compile together through `lcompile.py --all`. Original theorem
signature and definition bodies were compared to the shared source; none changed. The definition
relocation and all 230 transitive consumers are recorded in
`coord/changes/Q8-finite-tate-normalization-definitions.md`.

## Proved and sorry left

The original hole `AlgebraicGeometry.Scheme.finite_tate_site_descent` is closed by a complete
assembly proof. Its categorical uniqueness clauses and the private generic
`comparison_iso_lift_unique` lemma are proved.

Two holes remain, both exactly public theorem bodies `:= by sorry`:

- `AlgebraicGeometry.Scheme.finite_tate_normalized_comparisons`, node
  `lem-amb-finite-tate-normalized-comparisons`.
- `AlgebraicGeometry.Scheme.finite_tate_normalized_coherence`, node
  `lem-amb-finite-tate-normalized-coherence`.

This is a decomposition: 1 original hole closed, 2 holes added, net -1. It is not a claim to have
proved the remaining root/tensor construction. There are no holes in definitions.

## No longer needed

The original item's long proof-only import list is replaced by the two intermediate modules
and the existing fully faithful comparison module. The definitions module retains the original
eight public imports, plus the private coefficient tensor universe and intrinsic twist imports
needed to elaborate the unchanged definitions. The following former direct proof imports are
removed from the item; their mathematical uses lie in the intermediate proofs where needed:

- `Sheaf.Paper.PurTwistSheafLocallyFree`
- `Sheaf.Paper.ConstantCompletionEquivalence`
- `Mathlib.CategoryTheory.Limits.HasLimits`
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctoriality`
- `Sheaf.AlgebraicGeometry.ProEtaleComparisonPullbackSections`
- `Sheaf.AlgebraicGeometry.ProEtaleRootsOfUnitySheaf`
- `Sheaf.Paper.ComparisonPullbackExact`
- `Sheaf.CategoryTheory.ModulePullbackTensorIso`
- `Sheaf.CategoryTheory.SiteInverseImageTensor`
- `Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence`
- `Sheaf.AlgebraicGeometry.RootsOfUnityInverseImageIso`
- `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`
- `Sheaf.CategoryTheory.ConstantLeftModuleInverseImage`
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`

No module is withdrawn, and no dependency is claimed globally pruned. The original ten proof
nodes are now either cited by the two construction nodes or used by the categorical uniqueness
step. Public dependencies are preserved through reexport.

## Where the brief, the DAG or earlier work was wrong

The two existing construction interfaces use different encodings of the finite root scalar
extension. Their pure tensor comparison is real glue, not a definitional equality. The root
projection data uses a module over a sheafified lifted constant ring, while finite-root site
comparison uses fixed ZMod module sheaves and fixed scalar extension. Scratch proofs establish
several of the needed scalar/tensor identifications; these are not counted as delivered results
until integrated. The source quarantine row was checked; the current source module exists and
is preserved through the public reexport, not withdrawn.

## New nodes

`lem-amb-finite-tate-normalized-comparisons` states only the existence and arbitrary-test root
normalization of the comparison family, with its scalar-extension and tensor-induction proof.

`lem-amb-finite-tate-normalized-coherence` starts with any such normalized comparison family and
proves its scheme pullback and exponent-transition compatibilities. It asserts no existence of
the family and no uniqueness. Thus neither new theorem is the original theorem under a new name.
The source steps are stated in their docstrings and DAG records. The two definition-node Lean
attachments point to the new definition owner module. Change record:
`coord/changes/Q8-finite-tate-normalization-definitions.md`.

## Second reading by Q8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
