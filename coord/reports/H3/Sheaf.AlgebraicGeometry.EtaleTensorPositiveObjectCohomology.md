## What changed

Proved `AlgebraicGeometry.Scheme.Modules.etaleTensorPositiveObjectCohomology` in
`Sheaf.AlgebraicGeometry.EtaleTensorPositiveObjectCohomology`, without changing its
signature or public imports. The proof follows the existing affine localization route:
lift an injective resolution, restrict it along the open immersion, identify the
restricted coefficients with the lift of the restricted tensor-sections sheaf, apply
affine acyclicity, and reflect zero homology through ULift. The localization comparison
between the evaluation complexes is constructed in this proof, including naturality
along the identity-composition equality for the terminal open object.

Added proof-only imports of `Sheaf.Paper.ObjectCohomologyPresheafResolution`,
`Sheaf.CategoryTheory.Sites.CohomologyDerivedEvaluation`,
`Sheaf.AlgebraicGeometry.EtaleAffineQcoherentULift`,
`WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`, and
`Mathlib.CategoryTheory.Preadditive.Injective.Preserves`. Updated the existing node's
proof, proof_deps and proof_origin to describe the compiled argument. No new modules,
nodes, statements, data definitions or forced adaptations are delivered.

Single-file compilation passed without errors or warnings after removing unused imports.
The original hypotheses, coefficient universe, degree, and conclusion are unchanged.
`IsAffineOpen U` gives the affine instance on `U.toScheme`, and module restriction
preserves quasi-coherence. The proof includes the empty affine open and `n = 0`.
The unit sk-prop-cd route is unchanged: the quasi-coherent étale affine-acyclicity step
used by the Artin--Schreier argument remains. The generic resolution/evaluation nodes
from proper base change are used only as tools, not as a replacement for a unit step.

Read the official Stacks proofs at https://stacks.math.columbia.edu/tag/03F3 and
https://stacks.math.columbia.edu/tag/03P2. The listed local Stacks TeX files are absent on
this machine. The argument uses the existing declarations of the cited facts and proves
its complex-comparison glue directly; no unproved new result is asserted.

Searches: LeanFinder via msearch for object cohomology of an open versus global
cohomology of restriction returned no exact match; Loogle for
`CategoryTheory.Sheaf.H', CategoryTheory.Limits.IsZero` returned zero hits.
msearch grep for the target/localization names returned zero hits; direct rg in the
project found the affine vanishing, resolution, and restriction declarations used above.
There is no need for the drafted comparison obligation: it was removed from the sandbox.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.Scheme.Modules.etaleTensorPositiveObjectCohomology`
(node `lem-sc-etale-tensor-positive-object-cohomology`). Proved 1 of 1 sorries;
0 split off and 0 new holes. There is no sorry left in any delivered Lean file.
This is a proof from existing declarations; it does not assert that all transitive
sorry dependencies, including the existing open quasi-coherent identification, are closed.

## No longer needed

Removed the direct imports and proof-dependency edges:

- `Sheaf.CategoryTheory.Sites.CohomologyOverObjectLocalization`,
  node `lem-weil-pbc-cohomology-over-object-localization`: the evaluation-complex
  comparison is constructed directly, so a separate slice-site cohomology theorem is unused.
- `Sheaf.AlgebraicGeometry.EtaleOpenObjectCohomologyNatural`,
  node `lem-weil-pbc-etale-open-object-cohomology-natural`: no naturality over all
  inclusions of opens is needed for this fixed affine-open vanishing.
- `Sheaf.AlgebraicGeometry.EtaleAffineQcoherent`: use the large-coefficient
  realization in `Sheaf.AlgebraicGeometry.EtaleAffineQcoherentULift` directly,
  retaining node `lem-sc-etale-affine-qcoherent` and its affine-acyclicity route.
- `Sheaf.AlgebraicGeometry.EtaleTensorSections`, direct node edge
  `lem-sc-etale-qcoherent-presheaf-functorial`: this proof uses the existing
  sheaf open-identification theorem. Tensor restriction/coherence remains indirectly
  required by the tensor-sections sheaf and identification; it is not globally pruned.

These are local dependency removals; whether other targets still reach those modules
is decided by the maintainer's import-closure ledger. No other original proof dependency
is pruned. Both original public imports and their exposed interfaces are retained.

## Where the brief, the DAG or earlier work was wrong

The plan was mathematically usable. Its generic slice-localization declaration has a
small-category universe interface and the natural open comparison uses large
coefficients, while this theorem uses small coefficients on a large object universe.
Applying either comparison literally is not the required universe bridge. The existing
ULift resolution theorem supplies that bridge; the proof explicitly constructs the
restriction comparison on the large evaluation complexes and then reflects zero to the
small object cohomology using the existing presheaf-resolution comparison.

`Sheaf.H` is a type of additive cohomology classes, not itself an AddCommGrpCat object;
its zero-object form uses `AddCommGrpCat.of`. This was handled in the proof without
changing any existing declaration. There is no disputed statement or source error.

## Second reading by H3

1. Compared the delivered module with the repository version. The theorem signature,
   definitions, and public imports required by the interface are unchanged; only the
   proof and proof-only imports differ.
2. Compiled the module with `lcompile.py`, checked for forbidden declarations and
   untracked `sorry`, and inspected the target's axioms. Compilation is clean; the
   only extra axiom is the existing transitive `sorryAx` dependency of affine
   quasi-coherent acyclicity.
3. Read the proof and checked the edge cases `n = 0` and the empty affine open. The
   localization comparison, coefficient lifting, and ULift reflection establish
   exactly the stated `IsZero` conclusion, with no weakened hypotheses or altered
   definitions. No new statement or split-off node was added.
4. Checked pruning against the proof and node metadata. The removed localization,
   naturality, affine, and tensor-section imports are unused by the compiled proof;
   the node's proof steps and dependencies now describe the direct comparison route.
5. Checked the unit route: the affine quasi-coherent acyclicity step remains the
   `sk-prop-cd` realization, and the target statement remains unchanged. Verdict:
   pass.

Changed only the proof, proof-only imports, node proof metadata, and this report;
no theorem signatures, definitions, or new holes were introduced.
