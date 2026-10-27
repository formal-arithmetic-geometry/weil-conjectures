## Worker report

The item is stated by `AlgebraicGeometry.AlgebraicSpace.spaceDerivedPullback_tensor_preserve_QCoh` in `Sheaf.AlgebraicGeometry.SpaceDerivedQCohPullbackTensor`. The original statement and accepted stage-1 proof are unchanged. The original node changes only in `lean` and in the addition of the landed prerequisites `def-sfb-space-derived-module-calculus` and `def-sfb-space-derived-tensor-pullback` to `stmt_deps`. There are no new nodes, dependency repairs or new definitions.

The earlier BLOCKED ending concerned reopening a reviewed stage-1 split. Current `coord/brief-stage2.md` section 0 explicitly permits recording its stage-2 statement; the queue lists the item at stage 2. No released repair note applies. No stage-1 split is changed.

Hypothesis-by-hypothesis and clause-by-clause reading:

- Base scheme and spaces: `{S : Scheme.{u}} {X Y : AlgebraicSpace S}`. The existing full subcategory defines algebraic spaces over the same base, with natural transformations as morphisms. In the tensor conjunct `Z : AlgebraicSpace S` is arbitrary, independently of X and Y.
- Small étale structure sheaves and universe convention: `X.SmallModules`, `Y.SmallModules`, and `Z.SmallModules` are the landed equivalent small affine ringed-site models, retaining the original coefficient universe `u`. The model has object and morphism universe `u`; the original small étale site has object universe `u+1`, morphism universe `u`. No extra equality between those original universes is imposed.
- Unbounded derived categories: `X.DerivedModules`, `Y.DerivedModules`, `Z.DerivedModules`, with `[HasDerivedCategory.{wX} X.SmallModules]`, `[HasDerivedCategory.{wY} Y.SmallModules]`, and universally quantified `[HasDerivedCategory.{wZ} Z.SmallModules]`. These give three independent localization morphism universes; none restricts boundedness or geometry.
- Canonical ordinary tensor pullback and direct image: the existing `moduleTensorPullback` is the normalized left adjoint to `moduleDirectImage`, whose sections satisfy the compatible-chart limit universal property. The landed `smallModuleTensorPullback` conjugates precisely this functor by `smallModuleEquivalence.inverse` and `smallModuleRestriction`.
- Total derived functors and K-flat computation: `derivedTensorPullback` is Mathlib's `totalLeftDerived` of the landed `smallTensorPullbackComplex` along `DerivedCategory.Q`. Its universal property and canonical `totalLeftDerivedCounit` come from Mathlib's right Kan extension, rather than an arbitrary supplied functor or bare nonempty isomorphism. The prerequisite's derivability theorem and its proof docstring specify computation on K-flat resolutions with flat terms. K-injective direct image is already `derivedDirectImage` in `AlgebraicSpaceDerivedModules`; it is contextual and occurs in neither assertion here.
- Quasi-coherent cohomology: `X.derivedQCohProperty K` unfolds to `∀ n : ℤ, ((X.smallModuleEquivalence.inverse).obj ((DerivedCategory.homologyFunctor X.SmallModules n).obj K)).IsQuasicoherent`. This is exactly the dependency's Mathlib local-presentation predicate after transport back through the specified equivalence. No second quasi-coherence predicate is defined.
- Every morphism: `(a : X ⟶ Y)` has no geometric property hypotheses.
- Pullback clause: the first conjunct is `∀ K : Y.DerivedModules, Y.derivedQCohProperty K → X.derivedQCohProperty ((derivedTensorPullback a).obj K)`.
- Every space and every quasi-coherent pair: the second conjunct binds arbitrary `Z`, its localization choice, and `K L : Z.DerivedModules`, followed by the two quasi-coherence hypotheses.
- Tensor clause: `Z.derivedQCohProperty (Z.derivedDualityModel.closed.tensor.obj (K, L))`. This is the already landed closed derived tensor, characterized on K-flat representatives by `RingedSiteDualityModel.models`, retaining its pure-tensor normalization, signed symmetry and ordinary scalar unit. No second derived tensor is introduced.
- No boundedness, flatness, quasi-compactness or quasi-separatedness assumptions: none occurs in the theorem. There is no finite presentation, constructibility, perfectness or restriction on the degrees.

Dependency declarations read and used (including full signatures and docstrings):

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicSpace`, `EtaleSite`, `etaleTopology`, `structureSheaf`, `Modules`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `HasDerivedCategory`, `DerivedCategory`, `DerivedCategory.Q`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule`: `AlgebraicSpace.QCoh` and the slice sheafification/local-bijection instances. Its predicate is `SheafOfModules.IsQuasicoherent` in `Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent`; `QuasicoherentData` specifies presentations by arbitrary coproducts of the ring, locally on covering slices.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations`: `moduleDirectImageModel`, `moduleDirectImage`, `moduleTensorPullback`, `moduleTensorAdjunction`, with the full chart-limit universal property.
- `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`: `CochainComplex.IsKFlatIndependentCoefficients`, acyclicity of total tensor with every acyclic complex.
- `Mathlib.Algebra.Homology.HomotopyCategory.KInjective`: `CochainComplex.IsKInjective`, null-homotopy of maps from acyclic complexes.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceDerivedModules`: `DerivedModules`, `derivedQCohProperty`, `derivedDirectImage`, `derivedDualityModel`; its imports expose the actual small ringed model, restriction equivalence, cohomology functors and normalized derived tensor.
- `Sheaf.AlgebraicGeometry.SpaceDerivedTensorPullback`: `smallModuleTensorPullback`, `smallModuleTensorPullback_additive`, `smallTensorPullbackComplex`, `smallTensorPullbackComplex_hasLeftDerived`, and `derivedTensorPullback`. The module was read both locally and via `scompile.py --source` to confirm the live server interface. Its source and target localization universes are independent.
- `Mathlib.CategoryTheory.Functor.Derived.LeftDerived`: `Functor.HasLeftDerivedFunctor`, `Functor.totalLeftDerived`, and `Functor.totalLeftDerivedCounit` are the right Kan extension of the specified functor along localization, with its canonical augmentation.

The recorded proof prerequisites with Lean declarations are plain imports: `Sheaf.AlgebraicGeometry.DerivedPullbackTensorQCoh`, re-exporting `AlgebraicGeometry.derivedPullback_tensor_preserve_QCoh` from `WeilConjectures.AlgebraicGeometry.DerivedPullbackTensorQCoh`, and `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`, with `SheafOfModules.CanonicalTensorPullbackOfUniverses.ringedTopoiCanonicalDerivedTensorPullback`. The former's scheme tensor clause uses K-flat representatives; the latter retains the simultaneous natural canonical tensor comparison. The other two proof prerequisites, `lem-sfb-space-derived-etale-chart-calculus` and `lem-sfb-scheme-derived-etale-qcoh-comparison`, have no Lean record, Mathlib match or closed upstream declaration, so there is no module to import. They serve the postponed proof and are not needed to type this statement. Its proof docstring reproduces all three accepted steps, including the Zariski/étale scheme bridge. No wait or dependency cycle is introduced.

Sources read: the actual statements and proofs of Tags 08F4 and 08F5 in `spaces-perfect.tex`; the K-flat resolving-class construction in `sites-cohomology.tex`, Tag 06YY; latest blueprint `sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md` and its direct-images proof. The node's indirect blueprint ancestry, with null `blueprint.from.node`, is preserved.

Edge cases checked before writing: empty algebraic spaces (no nonempty hypothesis or chosen chart), zero complexes (zero cohomology), the structure sheaf in degree zero (the existing `derivedStructure_quasiCoherent` applies), identity maps, arbitrary non-flat morphisms, spaces without qc/qs hypotheses, and complexes unbounded in both directions. The tensor clause quantifies over all spaces independently of the chosen morphism. The helper's flat-resolving-class proof does not add flatness to the main theorem's objects or morphism.

Searches made:

- `msearch.py` LeanFinder “Derived pullback and tensor preserve quasi coherent cohomology on algebraic spaces”: ordinary scheme pullback statements, no matching space theorem.
- Loogle `Functor.totalLeftDerived, SheafOfModules.IsQuasicoherent`: no hits; the API was subsequently read directly in Mathlib.
- Mathlib grep `AlgebraicSpace|quasicoherent.*derived|derived.*quasicoherent`: zero hits.
- LeanSearch and LeanFinder “Canonical unbounded derived tensor pullback on algebraic space small etale module sheaves computed on K flat resolutions”: ordinary scheme/module pullbacks and tensor lemmas, no matching theorem.
- `rg` of `lean/WeilConjectures`, `lean/Sheaf`, and `dag/lean_names_upstream.json` found the existing small-model category, quasi-coherence, direct image and duality model, all reused. Blueprint-id grep in `lean/WeilConjectures` returned no hit for the item. `tools/blueprint_refs.py search 'space derived tensor pullback'` and `'space derived'` returned no blueprint match; `ancestor` returned null.
- During the dry run, another group's landing supplied `def-sfb-space-derived-tensor-pullback` in `SpaceDerivedTensorPullback.lean`. Its source and full Lean record were read, and the final module imports and uses that canonical declaration. The preliminary helper module and proposed new definition node were removed from the delivery; there is one definition per notion. No existing dependency record is overwritten.

The withdrawn `CompactObject` example was read; it currently contains no declarations, so its node record and the current module instructions supplied the formatting conventions. Exactly one theorem with proof `sorry` is delivered. Its module and declaration docstrings carry source, blueprint id, and the complete natural-language proof. All binders and universes are explicit (`autoImplicit false`). No statement correction and no STATEMENT-DISPUTED issue. Verification uses only `scompile.py` and `deliver2.py` with the normal 60-second per-file limit; no local/global library build is run.

## Second reading by Q129

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
