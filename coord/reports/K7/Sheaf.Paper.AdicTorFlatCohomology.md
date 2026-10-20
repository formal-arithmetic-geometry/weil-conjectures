## What changed

Preserved all original definitions, declaration signatures, universes and public imports
in `Sheaf.Paper.AdicTorFlatCohomology`. No dependency or consumer module is changed.
The main theorem now combines the supplied-model equivalence and the converse Tor
criterion, with a direct Lean proof of the ambient-flatness-to-higher-Tor direction.

The reduction theorem is proved by the new unconditional quotient cohomology sequence.
Flatness of the next cohomology makes the sequence's kernel zero. Exact restriction
reflects that the canonical scalar-extension adjunct is invertible. The scalar/tensor
comparison proves flatness after ordinary scalar extension; tensor-functor isomorphisms
transport this flatness to reduced cohomology. Thus the proof identifies the actual
canonical reduction arrow, including its specified normalized unit.

Three proved private helpers in the item establish flatness of a zero sheaf, K-flatness
of a flat sheaf placed in degree zero, and negative cohomology vanishing of its derived
scalar extension. The canonical K-flat counit computes that extension by its ordinary
single-term model. These helpers prove all required higher Tor vanishing from flat
reduced cohomology, without a new forward-implication hole.

All four delivered Lean modules compile together via `lcompile.py --all` with no
diagnostics (latest run: 0.7, 4.4, 4.5 and 3.6 seconds). Removing the tensor-colimit or
scalar-tensor comparison import caused compilation errors; removing the additional
presheaf sheafification import was successful. No tests or builds outside the prescribed
remote compilation were used.

## Proved and sorry left

The original item had two sorries. Both original declarations now have complete Lean
proofs from the stated lower results:

- `AlgebraicGeometry.Scheme.pbc_adic_tor_flat_cohomology`
- `AlgebraicGeometry.Scheme.pbc_adic_flat_cohomology_reduction`

Three public theorem sorries are added, each in its own new module with a proof in words
and a matching DAG node:

- `AlgebraicGeometry.Scheme.pbc_adic_reduction_cohomology_sequence`
  (`lem-weil-pbc-adic-reduction-cohomology-sequence`).
- `AlgebraicGeometry.Scheme.pbc_adic_tor_implies_flat_cohomology`
  (`lem-weil-pbc-adic-tor-implies-flat-cohomology`).
- `AlgebraicGeometry.Scheme.pbc_adic_flat_iff_supplied_model_flat`
  (`lem-weil-pbc-adic-flat-iff-supplied-model-flat`).

Actual item holes left: zero. New lower holes: three. This is a decomposition of the
two original holes, with an independently completed forward implication and flatness
transport argument; it is not a claim that the three lower results have been proved.
No sorry occurs in a definition, private helper or anonymous proof fragment.

## No longer needed

The following direct proof imports of the original item are removed:

- `Sheaf.Algebra.Homology.KFlat`
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses`
- `Sheaf.Paper.AdicLisseModule`
- `Sheaf.Paper.RefinementCoefficientRealization`
- `Sheaf.Algebra.Homology.BoundedAboveFlatSheafKFlat`
- `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed`
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients`
- `Mathlib.LinearAlgebra.FreeModule.PID`
- `Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`
- `WeilConjectures.CategoryTheory.Triangulated.DerivedCountableProductsCore`
- `Sheaf.NumberTheory.Padics.ExtensionIntegersDvr`
- `Sheaf.Paper.CompletedConstantSheafReduction`
- `Sheaf.Paper.ConstantCompletionEquivalence`
- `Sheaf.Paper.ConstantModuleSectionProperties`
- `Sheaf.Paper.IntegralStratifiedPerfectCharacterization`
- `Sheaf.AlgebraicGeometry.NoetherianStratumDetection`
- `Sheaf.AlgebraicGeometry.ProEtaleImmersionLimitPreservation`
- `Sheaf.Paper.KFlatRingedToposPullback`
- `Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitOfUniverses`
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`
- `Sheaf.CategoryTheory.ModulePullbackTensorIso`
- `Sheaf.CategoryTheory.SequentialTowerEvaluationFull`
- `Mathlib.CategoryTheory.Limits.FunctorCategory.Basic`
- `Sheaf.Algebra.Homology.WeilSiteDerivedTensorDescent`
- `Sheaf.Paper.TorsionLimitSheafCompleteness`
- `Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact`
- `Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization`
- `Sheaf.Paper.KoszulReconstruction`
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`
- `Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients`
- `Sheaf.AlgebraicGeometry.ProEtaleFiniteModules`
- `Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients`
- `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`

Their old mathematical roles either belong to the retained lower statements or are
replaced by the independent-universe bounded-flat criterion and tensor comparison APIs.
The separate presheaf sheafification import tested during development was also removed.
No original dependency node is claimed globally pruned: the lower nodes retain the
relevant parts of the original eleven-step route, so those statements can remain needed
below them. No whole module is withdrawn, and the unit's route is unchanged.

The original item node no longer directly uses these approved tool nodes; their
relevant roles are retained in the lower-node proof dependencies:

- `lem-pc-bounded-above-flat-kflat-site`
- `lem-pc-sheaf-modules-tensor-closed`
- `lem-weil-derived-countable-products-core`
- `lem-weil-l-adic-extension-integers-dvr`
- `lem-weil-pbc-completed-constant-sheaf-reduction`
- `lem-weil-pbc-constant-completion-equivalence`
- `lem-weil-pbc-constant-module-section-properties`
- `lem-weil-pbc-integral-stratified-perfect-characterization`
- `lem-weil-pbc-noetherian-stratum-detection`
- `lem-weil-pbc-proetale-immersion-limit-preservation`
- `lem-weil-pbc-ringed-pullback-preserves-kflat`
- `lem-weil-pbc-ringed-strict-tower-homotopy-limit`
- `lem-weil-pbc-ringed-topoi-derived-tensor-pullback`
- `lem-weil-pbc-ringed-topoi-module-pullback-tensor`
- `lem-weil-pbc-sequential-tower-evaluation-full`
- `lem-weil-pbc-site-derived-tensor-descent`
- `lem-weil-pbc-torsion-limit-sheaf-completeness`
- `lem-weil-proetale-countable-products-exact`
- `lem-weil-proetale-weakly-etale-localization`
- `prop-weil-pbc-koszul-reconstruction`

## Where the brief, the DAG or earlier work was wrong

The integral convenience criterion cannot be imported here: `IntegralCanonicalTruncations`
already imports the item, so the import-direction checker rejects that cycle. Its
convenience coefficient datum also uses E in the smaller universe and lifted integers,
whereas this item uses the actual valuation ring in the coefficient universe. The same
universe/interface distinction affects the stratified perfect characterization; the
converse Tor statement retains that required bridge within its source argument.

The earlier sandbox report was stale: its compile-server failures were temporary. The
current compiler has accepted the proofs. During this resumption, an initial dry run
crashed in shared worktree checkout after its 600-second timeout; a retry ended with
exit code 137 before returning validation output. The corrected dry run in `scratchpad/dry-run-2.log` succeeded: commit
`b667f25fcd` compiled and passed preflight, with review class CODEX for the three
new source lemmas and updated node. No delivery was pushed by that dry run.

A temporary duplicate presentation of the supplied-model predicate was removed; the
original predicate stays verbatim in its original module. New theorem statements were
checked on zero complexes, empty charts, quotient index zero (exponent one), and arbitrary
cohomological degrees. The quotient sequence requires neither boundedness nor flatness;
the other two criteria preserve the original constructibility and base hypotheses.

## New nodes

`lem-weil-pbc-adic-reduction-cohomology-sequence` isolates the two-term completed DVR
quotient resolution and its canonical short exact cohomology sequence (original steps
1 and 3). Its statement covers arbitrary complexes, making it independent of the
flatness argument that uses it.

`lem-weil-pbc-adic-tor-implies-flat-cohomology` isolates only the converse Tor implication
(original steps 1, 2 and 5--8). The forward implication is proved in the item. Its proof
uses stratified finite perfect models, Smith normal form, nonzero torsion-block Tor_1
and descent; it contains neither the supplied-model equivalence nor the canonical
cohomology reduction conclusion.

`lem-weil-pbc-adic-flat-iff-supplied-model-flat` isolates the complete supplied-model
comparison and flatness descent (original steps 1, 2 and 9--11). Its conclusion spells
out the original supplied-model quantifiers directly; no existing definition is moved.

Each new node has a self-contained statement, source, numbered-source proof steps and
their declared dependencies, search records, verbatim Lean theorem signature and
blueprint ancestry. No definition or existing statement repair was made, so no change
record or forced adaptation is required.

## Second reading by K7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
