## Worker report

The module `Sheaf.Algebra.Homology.FlatRingDiagramTensorCohomology` states
`ModuleCat.FlatRingDiagram.flat_ring_diagram_tensor_cohomology`. Its only postponed
proof is that named theorem. Eight accompanying definitions give real comparison
data belonging to this same node; none chooses an arbitrary morphism or an object
from a postponed mere existence assertion. The existing ordinary derived extension
is used unchanged, with its universal counit and K-flat computation property.

Source read: `literature/stacks-project/more-algebra.tex`, lines 14977–15100,
Tags 08HW and 0DJD, including the explanation of both factor-ring actions and the
two-step proof. The current blueprint unit
`literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md`
was also read. This item is an auxiliary algebra lemma, not that unit's statement.
No statement correction, dependency repair or new definition node is needed.

Hypothesis and clause mapping:

- Six commutative rings: the section binds `R A B R₁ A₁ B₁ : Type u`, each with
  `CommRing`. The seven given homomorphisms are their `Algebra` structures.
  `Algebra R A₁`, `Algebra R B₁` and the four `IsScalarTower` instances encode
  exactly the two commutative squares; they specify the common composites, rather
  than additional flatness or injectivity. Every commuting diagram admits this encoding.
- `D = A tensor_R B`, `D₁ = A₁ tensor_R₁ B₁` are actual Mathlib tensor rings.
  `tensorRingMap` is Mathlib's `Algebra.TensorProduct.mapRingHom`, with the two
  scalar-tower equalities as compatibility proofs. Its generator formula is
  `a tensor b ↦ algebraMap A A₁ a tensor algebraMap B B₁ b`.
- Flat `R → R₁` is `hR : (algebraMap R R₁).Flat`. The hypotheses `hA` and `hB`
  are `RingHom.Flat` for the `Algebra.TensorProduct.lift` maps from respectively
  `A tensor_R R₁` and `R₁ tensor_R B` to `A₁` and `B₁`. The lift uses precisely
  the two specified factor maps. There is no flatness hypothesis on `A/R` or `B/R`.
- Arbitrary unbounded `M in D(A)`: `sourceDerived R A B` has domain
  `DerivedCategory (ModuleCat.{u} A)`, and the final equations quantify over every
  such `M`. This uses the ordinary unbounded localization, not a bounded subcategory.
- K-flat derived tensors: `ordinaryDerivedExtendScalars` and
  `ordinaryDerivedChangeOfRings` are the published normalized universal pair.
  Their `computes` property identifies the counit on every K-flat complex.
  `sourceDerived` is restriction from `A` to `R` followed by derived extension
  to `B`. `targetDerived` is derived extension `A → A₁`, restriction to `R₁`,
  and derived extension to `B₁`, exactly the four functors in 0DJD's proof.
- Both commuting factor actions: `S` takes values in `ModuleCat (A tensor_R B)`;
  `T` takes values in `ModuleCat (A₁ tensor_R₁ B₁)`. Natural isomorphisms `eS`
  and `eT` identify their restrictions along `includeRight` with the specified
  cohomology functors, so the second-ring action is the actual cohomology action.
  The two scalar equations specify `a tensor 1` as the cohomology of
  multiplication by `a` on the derived input, including arbitrary `A₁` scalars
  on the intermediate object. Hence these are the source's tensor-ring actions.
  Actions of the factors commute because they act through the commutative tensor ring.
- Every integer degree: `∀ i : ℤ`. The functors are `DerivedCategory.homologyFunctor`.
- The displayed scalar extension: the domain of `c` is `S ⋙ extendScalars
  (tensorRingMap ...)`, namely `D₁ tensor_D H^i(M tensor-derived_R B)`.
  Mathlib's scalar-first order differs from the node's order by tensor symmetry.
  Its codomain is `ordinaryDerivedExtendScalars (algebraMap A A₁) ⋙ T`, namely
  the target cohomology with its full `D₁`-action.
- Isomorphism of `D₁`-modules: `IsIso c` in the functor category of actual
  `D₁`-modules. This includes invertibility of every `c.app M` and naturality in
  all derived morphisms `M → N`, not only chain maps of a selected model.
- Canonical map, not just existence of an unspecified isomorphism:
  `restrictionSquare` is the canonical exact-restriction composition comparison.
  `unitAround` first uses the unit for `A → A₁`, then the unit for `R₁ → B₁`,
  transporting around the two restriction squares. `comparison` is its
  adjunction transpose for `R → B`. `cohomologyComparison` applies cohomology and
  the published exact-restriction homology isomorphism. The final element equation
  requires `c(1 tensor x)` to be precisely this map. `D₁`-linearity then forces
  `c(d tensor x) = d gamma(x)` for every scalar; tensor generators determine c.
- Unit and augmentation normalization: the theorem supplies the three adjunctions
  together with `UnitNormalized` for each. This predicate is an equation for every
  ordinary complex P: the derived unit followed by the universal counit and the
  exact-restriction identification is the localization of the ordinary degreewise
  scalar unit. On K-flat P the counit is invertible by the existing `computes`
  property. Thus on any K-flat resolution it is exactly `p ↦ 1 tensor p`.
  Naturality of the universal counit and the unit at an augmentation `P → M`
  proves compatibility with that augmentation; naturality in the derived category
  includes all changes of such resolutions. The same applies to bounded-above free
  resolutions by the imported bounded-flat K-flat theorem. There are no arbitrary
  or unconstrained model identifications. No explicit resolution choices are
  needed in the statement because its normalization holds on every complex.

The node's conclusion is about scalar extension of cohomology modules. It is
accordingly a natural isomorphism of module-valued functors, with the preceding
canonical map defined on derived objects. It does not assert that tensoring an
arbitrary `D`-complex with `D₁` underived is its derived tensor, which would require
an extra flatness assumption that this source does not give.

Dependency declarations read and used:

- `def-weil-pbc-module-tensor-product`: Mathlib `TensorProduct`, `TensorProduct.mk`,
  `TensorProduct.lift`, `TensorProduct.ext'`, in `LinearAlgebra.TensorProduct.Defs/Basic`.
- `def-weil-module-base-change`: `LinearMap.baseChange` and ordinary extension,
  `Mathlib.LinearAlgebra.TensorProduct.Tower` and
  `Mathlib.Algebra.Category.ModuleCat.ChangeOfRings`.
- `def-weil-pbc-flat-ring-map`: `RingHom.Flat`, `Module.Flat`,
  `Mathlib.RingTheory.RingHom.Flat` and `Mathlib.RingTheory.Flat.Basic`.
- `def-weil-abstract-derived-category`: `DerivedCategory`, `HasDerivedCategory`, `Q`,
  `homologyFunctor`, `homologyFunctorFactors` in Mathlib's DerivedCategory modules.
- `def-pc-module-kflat-complex`: `CategoryTheory.MorphismProperty.kFlat` in
  `WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat`, through the ordinary
  module K-flat imports and the published `computes` property.
- Added landed statement dependency `lem-pur-derived-change-of-rings`:
  `ModuleCat.OrdinaryDerivedChangeOfRings`, `ordinaryDerivedChangeOfRings`,
  `ordinaryDerivedExtendScalars`, `nonempty_ordinaryDerivedChangeOfRings` in
  `Sheaf.Algebra.Homology.OrdinaryDerivedChangeOfRings`. Its ordinary specialization
  and its complete universal/counit signature were read, not reconstructed.
- Canonical restriction: `ModuleCat.derivedRestrictScalars` and
  `derivedRestrictScalarsCompIso` in
  `WeilConjectures.Algebra.Category.ModuleCat.DerivedBaseChange`.
- Canonical homology transport: `Functor.mapDerivedCategoryHomologyFunctorIso` in
  `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`.
- All recorded proof-dependency modules are imported privately. In order: Mathlib's
  flat tensor exactness and `Module.Flat.trans`; `CochainComplex.exists_quasiIso_flat_kFlat`
  in `WeilConjectures.CategoryTheory.DerivedCategory.FlatModel`;
  `CochainComplex.acyclic_mapBifunctor_extendScalars_of_kFlat` in
  `WeilConjectures.Algebra.Homology.KFlatModuleBaseChange`;
  `ModuleCat.flatScalarExtensionHomologyAdjunct_isIso` in
  `WeilConjectures.Algebra.Homology.FlatScalarExtensionHomologyAdjunct`;
  `ModuleCat.scalarExtensionCounit_isIso_of_kFlat` in
  `WeilConjectures.Algebra.Homology.KFlatScalarExtensionCounit`;
  `DerivedCategory.exists_balancedDerivedTensorModel` in
  `Sheaf.Algebra.Homology.BalancedDerivedTensorModel`;
  `DerivedCategory.exists_derivedTensor_second_factor_functor` in
  `Sheaf.Algebra.Homology.DerivedTensorSecondFactorFunctor`;
  `SheafOfModules.SuccessiveDerivedQuotient.successive_derived_quotient_normalization`
  in `Sheaf.Algebra.Homology.SuccessiveDerivedQuotientNormalization`;
  `SheafOfModules.sheafRingDerivedCoefficientAdjunction` in
  `Sheaf.Algebra.Homology.SheafRingDerivedCoefficientAdjunction`;
  `CategoryTheory.singleton_site_module_comparison` in
  `Sheaf.ProperBaseChange.SingletonSiteModuleComparison`;
  `CochainComplex.acyclic_mapBifunctor_of_boundedAbove_flat` in
  `WeilConjectures.Algebra.Homology.BoundedFlatKFlat`.

Edge cases checked mathematically: identity diagram (unit/transpose gives identity
comparison); M = 0; zero coefficient rings; every positive and negative integer
cohomological degree; arbitrarily unbounded complexes. For R = Z and A = B = F_p
with the identity diagram, nonzero Tor in degree -1 is retained: neither factor
was assumed R-flat and the source does not use an A-K-flat representative as if it
were R-K-flat. Arbitrary diagrams can be represented in a common ambient universe;
no finite generation, nontriviality or characteristic condition appears.

Searches for an existing exact statement:

- `msearch.py ... leanfinder "Flat change of a diagram of rings compares derived
  tensor product cohomology after extension of scalars"`: eight hits, including
  `ModuleCat.preservesFiniteLimits_extendScalars_of_flat`, flat tensor exactness
  and Kaehler cotangent base change. No derived arbitrary ring-diagram theorem.
- `msearch.py ... loogle "TensorProduct, Module.Flat"`: twelve hits, about
  nontriviality and linear independence under flat tensor. No match.
- `msearch.py ... leansearch "canonical flat base change derived tensor cohomology
  ring diagram"`: eight hits, including flatness stable under base change and
  `Module.Flat.isBaseChange`; no match.
- `msearch.py ... grep "derived.*[Tt]ensor|[Tt]ensor.*derived" Algebra/Homology`:
  zero hits in Mathlib.
- `rg` in both `lean/WeilConjectures` and `lean/Sheaf` for `flatRingDiagram`,
  `ringDiagram`, `balancedDerivedTensor`, `BalancedDerivedTensor`,
  `derivedTensorSecondFactor`, and `flat_scalar_extension_homology`: located
  existing balanced models and unrelated ring diagrams; no exact statement.
  The exact blueprint-id search in `lean/WeilConjectures` gave no hits.
- Further searches for derived extension/restriction, ordinary scalar adjunctions,
  and tensor cohomology found the existing constructions listed above. They are
  reused, and no alternative derived tensor, localization, or K-flat notion is defined.

Validation: the whole delivered module passed `scompile.py` in module mode twice,
including the actual library module path; no errors or warnings (the expected
postponed-theorem warning is suppressed by the project). All variables and universes
are explicitly bound and `autoImplicit` is false. Every line is at most 100 characters.

## Second reading by ND

The dispatcher explicitly forbids starting other agents. No independent worker was
started and this report does not claim an independent external review. A separate
in-thread rereading compared the final Lean signature against the node and 0DJD.
The maintainer's independent delivery review remains the independent reader.

The rereading checked the order of both tensor factors in hA/hB, all four tower
instances, the two restriction-square orientations, the scalar-first base-change
convention, and that T is defined on D(A₁) so arbitrary A₁ scalar endomorphisms are
specified (rather than only the image of A). It checked that the final equation fixes
the actual linear extension of the canonical map, and that its adjunctions cannot
be arbitrarily rescaled because UnitNormalized uses the ordinary unit and existing
universal counit on every complex. The main theorem has all three flatness assumptions,
no boundedness assumption, all integer degrees, and actual D₁-linear natural c.

One implementation mismatch found before the final version was that Lean omits R
from targetDerived's inferred section parameters: only A, R₁, A₁, B₁ are needed.
Call sites were corrected and the complete file recompiled successfully. No mismatch
with the mathematical node was found, and no statement correction was made.
