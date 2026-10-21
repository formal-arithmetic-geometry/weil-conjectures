## Worker report

The module `Sheaf.CategoryTheory.DerivedCategory.PerfectScalarTensorCoherence`
states `DerivedCategory.PerfectScalar.perfect_scalar_tensor_coherence`. Its conclusion is the
existence of the comparison data and every equation in the existential proposition `PerfectScalar.Coherence`.
The only postponed theorem is `perfect_scalar_tensor_coherence`, with `sorry` and the complete
13-step DAG proof in its docstring. The proposition is a statement package, not an
assumed instance. There is no proof of a mathematical assertion in this delivery.

The intrinsic helper abbreviations `D`, `E`, `coefficient`, and `symmetry` reuse
existing categories, termwise extension, degree-zero complex, and derived Koszul
symmetry. `B` selects the recorded universal fixed-second-factor left derived
functor at S[0]. This is a universal object, determined up to its canonical
comparison, not a choice from an unconstrained existence claim. `modelMap` is the
actual derived counit followed by the actual single-factor totalization isomorphism
and ordinary left unitor. No map is an arbitrary parameter or a Nonempty choice.
The theorem does not choose any of its asserted comparison data to define an object.

Hypothesis and clause correspondence:

- Commutative rings and unital ring maps are `R S : CommRingCat.{u}` and `f : R ⟶ S`.
  The entire ring family is quantified so tower comparisons share one choice of data.
  The instance family `∀ R, HasDerivedCategory.{w} (ModuleCat.{u} R)` specifies only
  localization sizes. `u` and `w` are explicit and independent; no equality is imposed.
- D(R) and perfect objects are `D R` and the recorded `IsPerfectRingComplex`.
  `preserves` says B carries the full perfect subcategory into the target full perfect
  subcategory. Its restriction is therefore a functor, with the same derived maps.
- Signed total and derived tensor are the existing cochain and K-flat derived monoidal
  tensors `⊗`. Their differential and braiding are the existing Koszul conventions.
  `tensorPerfect` and `unitPerfect` ensure these operations stay in Perf; they express
  the objects already used by the node's tensor/unit formulas.
- B(P) = P tensor^L S is literally `B f`, obtained from
  `exists_derivedTensor_second_factor_functor f.hom` at `coefficient S`.
- R-linear and additive on perfect Hom sets are `_linear` and `_additive`.
  The target scalar is `f.hom r • ...`, so no extra algebra action is assumed.
- Bounded finite-projective representatives are `a b : ℤ`, `IsStrictlyGE a`,
  `IsStrictlyLE b`, and `∀ n, Module.Projective ... ∧ Module.Finite ...`.
  `_model` asserts the canonical `modelMap f P` is invertible on every such representative.
- The maps b and the coefficient-unit comparison are `tensor` and `unit`, both `Iso`s.
  Their normalization equations are `_tensor_model` and `_unit_model`.
  The termwise map is the inverse of `mapCochainComplexμIso`, built from the existing
  scalar-extension `AlgebraTensorModule.distribBaseChange`. It sends
  s tensor (x tensor y) to (s tensor x) tensor (1 tensor y); its inverse multiplies
  a and b. This is the node's displayed formula after the recorded TensorProduct.comm
  conversion from M tensor S to S tensor M. The coefficient-unit normalization uses
  `mapCochainComplexεIso.inv`, namely multiplication f(r)s, with inverse insertion of 1.
- `_tensor_natural` quantifies arbitrary derived arrows a and b, not just localized
  chain maps. `_comp_natural` and `_identity_natural` do the same for the tower and identity.
  All model normalizations hold for every finite-projective representative. Naturality
  applied to derived model isomorphisms is precisely conjugation independence of the
  chosen representatives, including the cocycle for three choices. There is no fixed-model
  restriction on the asserted derived comparisons.
- Associator, signed symmetry and both unitors are the clauses `_associativity`,
  `_symmetry_compatibility`, `_left_unit`, and `_right_unit`. `symmetry` is the concrete
  `DerivedMonoidal.braiding'`, induced by the Koszul braiding; no arbitrary braiding is used.
- For R → S → T, `comp f g P` has source B(g)(B(f)(P)) and target B(f ≫ g)(P).
  `_comp_model` identifies it with termwise `extendScalarsComp.symm`, whose map multiplies
  g(s)t. `_identity_model` uses `extendScalarsId`, scalar multiplication.
- `_comp_left_unit`, `_comp_right_unit`, and `_four_ring` are the two unit equations and
  the four-ring associativity equation. Identity maps are allowed in all binders.
- `_comp_tensor`, `_comp_coefficient_unit`, `_identity_tensor`, and
  `identity_coefficient_unit` are all tower and identity tensor/coefficient-unit squares.

Dependencies used, with signatures and docstrings read in the read-only sources:

- `Sheaf.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral`:
  `DerivedCategory.IsPerfectRingComplex` (bounded finite-projective model predicate).
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`, `Q`, and
  `HasDerivedCategory`; used through the public dependency imports.
- `Mathlib.Algebra.Homology.BifunctorShift`: `CochainComplex.mapBifunctor` and the
  tensor realization on cochain complexes, accessed via the existing monoidal imports.
- `Mathlib.LinearAlgebra.TensorProduct.Tower`: `LinearMap.baseChange`,
  `AlgebraTensorModule.distribBaseChange`, with its generator and inverse formulas;
  `ModuleCat.extendScalars` is its bundled functor interface.
- `Sheaf.Algebra.Homology.DerivedTensorSecondFactorFunctor`:
  `DerivedCategory.exists_derivedTensor_second_factor_functor`, including its actual
  universal derived counit. This supplies B and modelMap.
- `WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle`:
  `CochainComplex.mapBifunctorSingle₂Iso` removes S[0] from the mixed total tensor.
- `WeilConjectures.Algebra.Homology.Monoidal.MapHomologicalComplex`:
  `Functor.mapCochainComplexμIso` and `mapCochainComplexεIso` give the concrete normalizations.
- `Mathlib.Algebra.Category.ModuleCat.Monoidal.Adjunction`: ordinary balanced tensorators.
- `WeilConjectures.Algebra.Category.ModuleCat.DerivedBaseChange`:
  `ModuleCat.extendScalars_additive` supplies the existing needed additive instance.
- Existing monoidal derived-category and linearity instances give the derived tensor
  and R/S scalar actions. The derived symmetry is `DerivedMonoidal.braiding'`.
- Proof-only imports: `WeilConjectures.Algebra.Homology.BoundedFlatKFlat`,
  `Mathlib.Algebra.Homology.DerivedCategory.KProjective`, `Mathlib.RingTheory.Flat.Basic`.
  They supply the already stated projective-flat, bounded-flat K-flat and derived Hom inputs.
  The remaining proof dependencies are available through the statement imports.

Edge cases checked before writing: the zero ring and zero module, empty finite generating
lists, the zero complex with a > b, arbitrary negative degrees (Koszul parity), identity maps
in every place in a tower, and nonflat maps such as Z → Z/2. No Nontrivial, field,
Noetherian, flat ring-map, or boundedness assumption on the whole derived category is imposed.
The comparison at a finite-projective model has boundedness hypotheses only where needed.

Searches actually run:

- msearch.py leanfinder: "Derived extension of scalars on perfect complexes is symmetric
  monoidal and coherent with composition of ring maps". Eight hits concerning derived
  linearity and exact functors; none the combined statement.
- msearch.py loogle: "ModuleCat.extendScalars, ModuleCat.monoidalCategory, Functor.Monoidal".
  No hits (unknown identifier Functor.Monoidal).
- msearch.py leansearch: "Derived extension of scalars preserves perfect complexes and
  is symmetric monoidal". Eight hits: ModuleCat symmetricCategory, extendScalars and
  its identity/pseudofunctor comparisons, flat exactness, and derived linearity; no match.
- msearch.py grep: "extendScalars|baseChange|derivedTensor" in Algebra/Category/ModuleCat.
  Found ordinary monoidal Adjunction and ordinary Pseudofunctor, used rather than duplicated.
- rg of lean/WeilConjectures and lean/Sheaf: perfectScalar/PerfectScalar, scalar coherence,
  monoidal, derivedTensor, baseChange, scalarExtension, and extendScalars-derived.
  `PerfectScalarExtension` gives preservation only; `ScalarInternalHomTowerCoherence`
  concerns sheaf internal Hom, not this ring-perfect conjunction. No existing exact match.
- rg of the node ID in lean/WeilConjectures: no recorded existing declaration.
  Subsequent focused search located the existing extendScalars_additive instance, imported.

No new definition nodes, dependency repairs, statement corrections or disputes.
The item's original statement and all dependency lists are unchanged.

## Second reading by NG

The dispatcher brief assigns the maintainer the independent review and explicitly forbids
starting other agents. This section records the worker's separate rereading, not a claim
that another agent reviewed it. I reopened the item and module and matched every clause
above. In particular I checked the orientations of b, c and the identity, the inverse
orientation of extendScalarsComp, both unit equations, the four-ring composites, all four
coefficient/tensor squares, and the fact that naturality uses arbitrary derived arrows.
I checked that the actual derived counit appears in modelMap, so the normalizations do
not identify arbitrary existential isomorphisms with canonical ones by assertion.
The compiler interface repairs qualified Functor whiskering and imported the existing
ordinary scalar-extension additive instance. They do not change the mathematical statement.

Validation: prescribed scompile.py compiled both sandbox and library paths under the
60-second default. The final statement uses an existential proposition rather than a structure, avoiding
expensive generated congruence declarations. Intrinsic helpers are irreducible after
their concrete construction. The temporary profiling option was removed.

Unused proof binder names are prefixed with underscores rather than disabling a linter;
all their hypotheses remain present. This also avoids changing the proposition.
