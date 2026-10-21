## What changed

The existing public statement `WeilConjectures.point_fibre_equivalence` is verbatim unchanged.
Its proof now combines the following arguments, rather than leaving the whole conjunction as
one hole:

* Finite coefficients: construct the constant-module/sections adjunction, descend it termwise
  through derived localization, and restrict it using finite-ring constructible origin and
  the algebraically closed etale-point equivalence. The finite equivalence, its unit and
  counit calculations, and its exactness clauses are proved in the item module.
* Integral coefficients: prove sections conservative using normalized reduction, the finite
  equivalence, and the actual Roos completeness triangle. Together with the separate completed
  perfect-realization lemma, the adjunction triangle identity makes the counit invertible.
* Rational coefficients: copy the specified functor to its defining object map. Every tensor
  over the uniformizer localization has a single pure-tensor representative. The normalized
  Hom calculation gives full faithfulness, and the separate lattice calculation gives
  essential surjectivity. These are genuinely different parts of the argument.
* Algebraically closed coefficients: transport the target filtered two-colimit cocone along
  finite-stage equivalences. Its Hom-surjectivity and eventual Hom-injectivity prove the
  specified common-stage functor fully faithful; cocone object-surjectivity proves essential
  surjectivity. Field scalar extension along a ring equivalence has the explicit tensor-tower
  inverse. This argument proves the equivalence independently of shift descent.
* Exactness: prove rational exactness using shift descent through the actual raw localization,
  with the coefficient-one formula specifying the factorization isomorphism. For Qbar the
  separate stage shift lemma handles stage images; the item proof descends an arbitrary
  source distinguished triangle along its recorded triangle isomorphism, including its last
  arrow, to the precise target predicate.

Validation: the complete item file and its sandbox dependencies compile on the server. The conservativity component compiled cleanly, as did
the proved rational-exactness component (23.3 seconds). The target signature was compared
verbatim with the repository version; all Lean lines are at most 100 characters. The new
nodes' dependency unions agree with their proof steps, and no new component has a dependency
path back to the parent. Common-stage elaboration uses a private cocone with proved object
and map equations, keeping the coefficient-choice definitions behind that proof interface;
no existing definition was changed and no compile limit was raised.

All new helpers in the existing module are private and proved. Six separate component modules
are added under `Sheaf.Paper`; two are proved, four retain named holes. No source-library
module, target statement, public definition, or other group's module is changed. The original
node's proof, proof dependencies and proof origin follow this argument. Its obsolete tool
approvals are pruned in order; no approval is added or reordered.

The generic termwise-adjunction and constant-module-constructibility tools now used directly
are `lem-weil-pbc-termwise-adjunction-homotopy` and
`lem-weil-pbc-proetale-constant-module-constructibility`. The independent reader should review
these additional cross-unit tool uses; this worker has not altered maintainer approvals.

## Proved and sorry left

One old hole is closed syntactically:
`WeilConjectures.point_fibre_equivalence` (`lem-weil-point-fibre-equivalence`).
The item module itself has zero remaining `sorry`.

This is a decomposition, not a claim that the full point-equivalence theorem is axiom-free:
four strictly separate lower holes are added, so the local hole delta is 1 closed minus 4
added. The four new holes, each exactly `:= by sorry`, are:

* `WeilConjectures.pointIntegralPerfectRealization` —
  `lem-weil-point-integral-perfect-realization`: fully faithful completed realization and its
  adjunction unit, without the counit assertion that the parent proves by conservativity.
* `WeilConjectures.pointRationalSectionsHom` —
  `lem-weil-point-rational-sections-hom`: the normalized Hom base-change isomorphism; it says
  nothing about essential surjectivity or finite-stage descent.
* `WeilConjectures.pointRationalSectionsLattice` —
  `lem-weil-point-rational-sections-lattice`: existence of integral lattices for bounded
  finite-dimensional complexes; it says nothing about Hom comparison or exactness.
* `WeilConjectures.pointQbarFibre_shift_descent` —
  `lem-weil-point-qbar-fibre-shift-descent`: shift coherence and exactness on stage images;
  the parent separately handles arbitrary source-triangle descent and the equivalence.

New component theorems proved without a `sorry` in their own bodies:

* `WeilConjectures.pointIntegralSections_conservative` —
  `lem-weil-point-integral-sections-conservative`.
* `WeilConjectures.pointRationalFibre_exact` —
  `lem-weil-point-rational-fibre-exact`. This uses the existing proved private raw-localization
  result through a private `import all`; it neither changes that module nor publishes its
  implementation. The finite-dimensional target's closure under triangles and isomorphisms
  is also proved locally.

Existing named dependencies that are still `sorry` remain dependencies, rather than being
reproved or counted as holes closed here. No hole is inside a definition or a private helper.
The new statements include the zero complex, empty support and torsion Hom cases in their
proofs in words; no nonzero-rank or nonempty-support hypothesis was introduced.

## No longer needed

The following private imports are removed from the item module:

* `Sheaf.NumberTheory.Padics.ExtensionIntegersDvr`
* `Sheaf.AlgebraicGeometry.ContinuousCoefficientImmersionRestriction`
* `Sheaf.Paper.CompletedConstantSheafReduction`
* `Sheaf.Paper.ConstantModuleSectionProperties`
* `Sheaf.Paper.PointProEtaleSectionsExact`
* `Sheaf.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctoriality`
* `Mathlib.CategoryTheory.Sites.Sheafification`
* `Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`
* `Mathlib.Algebra.Homology.ShortComplex.PreservesHomology`
* `Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`
* `Mathlib.Algebra.Module.FinitePresentation`
* `Mathlib.CategoryTheory.ObjectProperty.FullSubcategory`
* `WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf`
* `WeilConjectures.AlgebraicGeometry.FiniteLocallyConstantModuleValues`
* `Sheaf.AlgebraicGeometry.ProEtaleConstantSheafStalk`
* `Sheaf.Paper.PointSectionsFiniteness`
* `WeilConjectures.RingTheory.FiniteFreeResolution`
* `Mathlib.LinearAlgebra.FreeModule.PID`
* `Sheaf.CategoryTheory.DerivedCategory.PerfectCohomologyAssembly`
* `Sheaf.Paper.IntegralStratifiedPerfectCharacterization`
* `Sheaf.Paper.DerivedScalarExtensionRestrictionAdjunction`
* `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`
* `Sheaf.Algebra.Homology.KFlat`
* `Sheaf.Paper.DerivedCompleteOnSlices`
* `Sheaf.NumberTheory.Padics.IntegersLocalizationUniformizer`
* `Mathlib.LinearAlgebra.TensorProduct.Basic`
* `Mathlib.RingTheory.Localization.Away.Basic`
* `Mathlib.RingTheory.Flat.Localization`
* `Sheaf.Algebra.Homology.BaseChangeRHomPerfect`
* `Mathlib.RingTheory.Flat.Basic`
* `Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses`
* `WeilConjectures.Algebra.Homology.RhomIntoKInjectiveLocal`
* `Mathlib.LinearAlgebra.Basis.VectorSpace`
* `Sheaf.Paper.PointSectionsScalarExtension`
* `Mathlib.Algebra.Colimit.Module`
* `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`
* `Sheaf.Paper.CompletedScalarShift`
* `Sheaf.Paper.PointSectionsTensorShift`
* `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`
* `WeilConjectures.AlgebraicGeometry.SpecAlgClosedEtaleSheafConstant`

These are import removals from this proof, not withdrawals of their modules. Most of the
integral-perfect and rational-base-change tools remain in the proof plans of the separated
components. Definitions and source declarations that remain transitively needed are preserved.
In particular, this packet does not remove any adopted source declaration or list any module
in `deleted.txt`.

The already proved `AlgebraicGeometry.Etale.constantSheafEquivalenceOfIsSepClosed` in
`WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Ordinary` supplies the module-sheaf
equivalence directly. The finite argument therefore also prunes the planned set-valued
`lem-weil-pbc-spec-algebraically-closed-etale-sheaf-constant` node and its private import.
The unnecessary intermediate `PointFiber` module is not imported.

The finite argument no longer needs a separate finite-stalk/final-point calculation: finite
constructible origin and the etale/pro-etale comparison identify the entire sheaf. Thus the
old direct proof uses of `lem-weil-pbc-finite-locally-constant-module-values` and
`lem-weil-proetale-constant-sheaf-stalk` are unnecessary in this argument. Integral detection
uses the defining completeness triangle directly, rather than an auxiliary K-flat-resolution
construction: `lem-pc-kflat-resolution` and `def-pc-kflat-complex` no longer occur in this
packet's direct proof plan (other retained dependencies may of course still use them).
The common-stage equivalence uses the already specified scalar comparison, so it does not
separately import `Sheaf.Paper.PointSectionsScalarExtension` to construct another comparison.
No UNIT statement or realized proof step is removed; the unit's `realized` lists are empty.
No global module pruning is claimed.

The following obsolete entries of the existing node's top-level `tool_uses` are deleted;
retained approvals keep their original order:

* `lem-weil-l-adic-extension-integers-dvr`
* `lem-weil-pbc-continuous-coefficients-immersion-restriction`
* `lem-weil-pbc-completed-constant-sheaf-reduction`
* `lem-weil-pbc-constant-module-section-properties`
* `lem-weil-pbc-site-r-module-presheaf-sheafification-exact`
* `lem-sp-exact-functor-preserves-homology`
* `lem-weil-pbc-unbounded-derived-iso-cohomology`
* `lem-sc-noetherian-finite-module-finite-presentation`
* `lem-weil-pbc-finite-locally-constant-module-values`
* `lem-weil-pbc-spec-algebraically-closed-etale-sheaf-constant`
* `lem-weil-pbc-finite-free-resolution-noetherian`
* `lem-sc-dvr-fg-torsionfree-free`
* `lem-sf-perfect-cohomology-assembly`
* `lem-weil-pbc-integral-stratified-perfect-characterization`
* `lem-pc-kflat-resolution`
* `lem-sf-derived-homology-long-exact`
* `lem-weil-l-adic-integers-localization-uniformizer`
* `lem-weil-pbc-localization-flat`
* `lem-pc-base-change-rhom-perfect`
* `lem-weil-pbc-flat-tensor-exact`
* `lem-pur-rhom-into-kinjective-local`
* `lem-weil-pbc-vector-space-basis-through-vector`
* `lem-weil-point-sections-scalar-extension`

## Where the brief, the DAG or earlier work was wrong

The mathematical statement is retained. The original plan does not directly supply the
normalized rational Hom calculation or the lattice object required by the specified raw
rational functor. Its generic RHom base-change theorem is stated for one-object ringed-site
modules, while the point fibre uses ordinary modules and a prescribed carrier-size descent.
The Hom component records this bridge and its pure-tensor normalization explicitly.
Likewise the integral realization component is not the discrete constant integral sheaf:
it uses the completed coefficient algebra and its actual scalar map. The existing
`pointSectionsReconstruction` can supply unit/landing properties after constructing its
explicit underived adjunction; it does not itself construct that adjunction, and its ordinary
module derived category is the standard larger model. Those construction and size-transport
requirements are retained in the realization component, rather than silently identified.

The exactness portion required distinguishing the raw scalar localization from its Karoubi
completion. The proved rational-exactness component uses precisely the former. No hypothesis
is added to a target, no conclusion is weakened, and no statement is marked disputed.

## New nodes

`lem-weil-point-integral-sections-conservative` / `Sheaf.Paper.PointIntegralSectionsConservative`:
proved reduction-and-completeness detection, conditional only on the finite equivalences
which the parent has already established. The proof compares the small and standard derived
section models through their homology isomorphisms.

`lem-weil-point-integral-perfect-realization` / `Sheaf.Paper.PointIntegralPerfectRealization`:
completed constant realization, its adjunction and invertible unit; the parent supplies the
separate conservative-counit argument. One retained hole.

`lem-weil-point-rational-sections-hom` / `Sheaf.Paper.PointRationalSectionsHom`:
normalized perfect Hom base change, conditional on the integral equivalence. One retained
hole. It is not the rational equivalence under another name.

`lem-weil-point-rational-sections-lattice` / `Sheaf.Paper.PointRationalSectionsLattice`:
finite free zero-differential lattices, conditional on the integral equivalence. One retained
hole, independent of the Hom calculation.

`lem-weil-point-rational-fibre-exact` / `Sheaf.Paper.PointRationalFibreExact`:
proved shift comparison and distinguished-triangle preservation through the specified raw
localization, including the size-descent counit comparison.

`lem-weil-point-qbar-fibre-shift-descent` / `Sheaf.Paper.PointQbarFibreShiftDescent`:
common-stage shift coherence and exactness on stage triangles. One retained hole; arbitrary
triangle-isomorphism descent and common-stage full faithfulness are proved in the parent.

Every new node has its source, complete proof in words, exact Lean attachment and three kinds
of recorded library search. No existing signature or definition is changed. The proof-scaffolding commands required
`coord/changes/point-fibre-equivalence-proof-scaffolding.md`; all helper instance
registrations in the existing module are local. No consumer or forced adaptation is needed.
The unit-route import `Sheaf.AlgebraicGeometry.ProEtaleSiteComparison` is retained.

## Second reading by B5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
