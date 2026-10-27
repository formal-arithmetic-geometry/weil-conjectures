## Worker report

The module `Sheaf.Paper.NativeWeilClosedForgetful` states
`AlgebraicGeometry.ProEtaleWeilSheaf.native_closed_forgetful`. It uses the actual
native category, its actual derived localization, the actual coefficient sheaf,
and the actual contragredient internal-Hom construction. All postponed proofs
are named theorems with source and proof docstrings. Definitions have real data;
the comparison structures are data in the conclusion of the theorem, never
hypotheses replacing the assertion to be stated.

The previous worker's stale-assignment answer does not describe this stage-2
assignment: the live node has a stage-1 PASS and no Lean record. This delivery
leaves its mathematical statement and its stage-1 split untouched.

Hypotheses and objects, clause by clause:

- Finite field: `(k₀ : Type u) [Field k₀] [Finite k₀]`.
- Prime coefficient characteristic different from the base characteristic:
  `(l : ℕ) [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]`.
- The separated finite-type scheme is `(X : Scheme.{u})` with
  `[X.Over (Spec (CommRingCat.of k₀))]`, and the three main-theorem instances
  `LocallyOfFiniteType`, `QuasiCompact`, and `IsSeparated` on that structure map.
  Locally finite type plus quasi-compact is finite type.
- The algebraic closures are the native library's `AlgebraicClosure k₀` and
  `PadicAlgCl l`. These are the fixed closures in the native category named by
  the node; no additional property of a closure is imposed. The geometric
  fibre is `(X ↘ Spec (CommRingCat.of k₀)).geometricFiber`. We do not construct a
  second fibre or a second Weil category from a different choice of closure.
- Geometric semilinear Frobenius is the one already used by
  `WeilSheaf.frobeniusPullback k₀ l X`: its presentation is pushforward along
  the inverse geometric automorphism, hence the pullback along that
  automorphism. This is not absolute Frobenius on the geometric scheme.
- `R_T` is the existing `ProEtale.adicConstantSheaf` on that fibre, used by
  `ProEtale.AdicSheaf l T`. Its sections are the locally finite-span continuous
  functions of the upstream finite-subextension coefficient sheaf. A finite
  span of algebraic elements lies in one finite intermediate field; conversely
  such a field is finite-dimensional. Thus this is the coefficient condition
  in the node, not all arbitrary continuous maps to the algebraic closure.
- Ordinary modules are the actual `ProEtale.AdicSheaf l T = Mod R_T`.
  Native Weil sheaves are `ProEtaleWeilSheaf k₀ l X`, the existing
  `Endofunctor.IsoAlgebra` of the Frobenius functor. Their maps intertwine the
  invertible structure maps. No fixed-pair category in a derived category is
  substituted.
- Both unbounded derived categories are literally `DerivedCategory` of these
  abelian categories. `nativeForget` is an abbreviation for
  `IsoAlgebra.forget.mapDerivedCategory`, not an unspecified derived functor.
- `WeilComplex k₀ l X` is used literally for the full bounded constructible
  subcategory. Its definition tests constructibility on underlying cohomology.

Conclusions, clause by clause:

- Exactness is `(nativeForget k₀ l X).IsTriangulated`; the functor carries its
  existing integer shift compatibility. Conservativity is
  `(nativeForget k₀ l X).ReflectsIsomorphisms`.
- Commutation with every cohomology degree is the natural isomorphism
  `U ⋙ DerivedCategory.homologyFunctor _ n ≅
  DerivedCategory.homologyFunctor _ n ⋙ IsoAlgebra.forget _`, for every `n : ℤ`.
- Restriction to the bounded constructible full subcategory is expressed by
  `DerivedCategory.TStructure.t.bounded (U.obj K.obj)` and
  `ProEtale.IsAdicConstructibleSheaf (Hⁿ(U.obj K.obj))` for every actual
  `K : WeilComplex k₀ l X`. The full-subcategory functor is precisely the
  restriction of `U` satisfying this object property; no additional choice of
  maps is necessary.
- The final existential supplies `NativeClosedComparison k₀ l X`, together
  with its `Compatible` property. Its source and ordinary Hom bifunctors have
  `NativeHomRepresentatives` models, with naturality in BOTH variables. The
  source restriction in each target variable is naturally isomorphic to the
  recorded `derivedHom k₀ l X L`. The ordinary restriction is the same
  `DerivedCategory.bifunctorRHom` construction for `Mod.ihom`.
- These representative models are actual sheaf internal-Hom product totals
  `CochainComplex.bifunctorHomObj`, not global Hom groups. The source uses
  `ihomBifunctor k₀ l X`, hence its contragredient Weil action. Models for an
  arbitrary source into a K-injective target also give the stated two-K-injective
  model by specialization.
- `CoefficientClosedStructure` supplies the tensor monoidal structure and
  actual tensor--Hom adjunction, evaluation and transpose for each specified
  Hom bifunctor. Its unit is identified with the existing regular coefficient
  module in degree zero. `NativeOrdinaryTensorModels` specifies the ordinary
  derived tensor on every K-flat representative using the actual sum-total
  relative tensor. K-flatness is its acyclic-test definition. The signed-swap
  equation specifies the usual Koszul symmetry on every bidegree.
- `NativeAdjunctionNormalization` fixes the adjunction on representatives by
  componentwise uncurrying using the EXISTING `Mod.ihomAdjunction`, not merely
  an unspecified adjunction with the same right adjoint. The right tensor
  parameter is first in `Mod.tensorLeft`'s curried bifunctor. Consequently the
  total indexed by `(p,q)` requires the factor `(-1)^(pq)` when uncurrying into
  the usual left-first evaluation. The formula records that sign explicitly.
- `tensorComparison` and `homComparison` are natural isomorphisms of the full
  two-variable derived functors. Their types quantify over all unbounded
  derived objects. They impose no constructibility or boundedness hypotheses
  on `K`, `L`, or the later object `W`.
- The Hom arrow is fixed in `Compatible` as `nativeHomComparison`: transpose
  of the tensor comparison inverse followed by mapped evaluation.
  `NativeHomRepresentativeCompatibility` further fixes its chain-level
  comparison by ALL product projections and the canonical localization
  factorization isomorphisms. Underlying K-injectivity is asserted there, not
  assumed of arbitrary underlying complexes. Thus these are canonical
  comparisons, rather than arbitrary isomorphisms between the object values.
  The source derived tensor is the left adjoint of the actual native Hom;
  together with this normalized closed comparison it is the derived diagonal
  tensor, up to its uniquely compatible adjoint isomorphism.
- `NativeTensorCoherence` records associator and both unit squares. Its unit
  comparison is the real image of `adicConstant` via
  `Functor.mapDerivedCategorySingleFunctor`, not a free extra unit map.
- `NativeSymmetryCompatibility` is the symmetry square under that same tensor
  comparison. `NativeEvaluationCompatibility` is exactly the displayed image
  of evaluation, using the two comparison components.
- `nativeBidual` is DEFINED as the transpose of symmetry followed by the
  specified evaluation. `NativeBidualNaturality` quantifies over every `W`
  and every source morphism. `NativeBidualCompatibility` states the image of
  this morphism under forgetting, including both Hom comparisons and the
  contravariant transport through the inverse inner comparison. No field
  or theorem asserts that a biduality map is an isomorphism.

Dependencies read and used:

- `Sheaf.Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum`, its
  `geometricFiber` and `CoefficientDatum`; the native fixed-closure
  specialization is supplied by the actual Weil category's source.
- `Sheaf.AlgebraicGeometry.FrobeniusDetailed`:
  `WeilConjectures.FiniteFieldDatum.geometricFrobenius`, including its full
  semilinear automorphism signature. Native Frobenius uses this geometric
  convention, rather than a noninvertible absolute endomorphism.
- `WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic`:
  `Profinite.padicAlgClCondensedRing`, `padicAlgClSubfunctor`,
  `padicAlgClRingPresheaf`, `padicAlgClRingObj`; actual coefficient data reused
  transitively by the native module category.
- `Sheaf.Paper.CompletedCondensedCoefficients`:
  `AlgebraicGeometry.ProEtale.completedCondensedAlgebraicClosure` and
  `completedCondensedPullback` explain the finite-subextension colimit and
  inverse-image compatibility. The recorded primary
  `completedCondensedIntegral` and its related declarations were read too.
  This is imported as a proof prerequisite, not used to define new coefficients.
- `Sheaf.CategoryTheory.RingedSiteModules`:
  `CategoryTheory.ringedSiteModules`, the transparent general-site
  `SheafOfModules` presentation. The native `Mod` presentation is retained;
  no private sheaf-of-modules category is created.
- Mathlib `CategoryTheory.Endofunctor.Algebra` and its invertible-structure
  full subcategory; upstream `CategoryTheory.Endofunctor.IsoAlgebra` is
  precisely this notion. No dependency repair is required.
- Mathlib `DerivedCategory`, `HasDerivedCategory` and localization `Q`;
  Mathlib `CochainComplex.IsKInjective`, with the full null-homotopy signature.
- `Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses`:
  `CategoryTheory.derivedInternalHomOfUniverses`, read with its full independent
  site/coefficient/localization universes. Its ringed-site construction is the
  generic proof prerequisite; the native construction is reused explicitly.
- `Sheaf.Algebra.Homology.RingedDerivedClosedSymmetricMonoidal`:
  `CategoryTheory.ringedDerived_closed_symmetric_monoidal` and its
  representative/coherence data. The current statement retains the normalized
  adjunction condition, rather than taking a bare existential adjunction from
  this theorem without its representative model.
- `Sheaf.Paper.CoefficientRingedTensorHomModel`:
  `WeilConjectures.CoefficientClosedStructure` and its `tensor`, `evaluation`,
  and `transpose` declarations are reused directly. The ordinary native
  `Mod` interface requires the explicit representative equations in this
  module; no duplicate definition of closed structure is introduced.
- Native modules `WeilConjectures.WeilSheaf.Category`, `Dual`, `DerivedHom`,
  `TensorHomAdjunction`, and their transitive adic-coefficient and hom-complex
  sources were read. Used declarations include `WeilComplex`,
  `ProEtaleWeilSheaf`, `WeilSheaf.frobeniusPullback`, `ihomBifunctor`,
  `derivedHom`, `adicConstant`, `Mod.ihom`, `Mod.tensorLeft`,
  `Mod.ihomAdjunction`, `DerivedCategory.bifunctorRHom`,
  `CochainComplex.bifunctorHomObj`, its projections and map operations,
  `CochainComplex.mapBifunctor`, and `HomologicalComplex.ιMapBifunctor`.

The available proof-dependency modules for K-flat/K-injective resolutions,
K-flat ringed pullback, right-derived composition, Hom quasi-isomorphisms,
site tensor descent, and the normalized ringed tensor--Hom adjunction are
imported. Proof-only DAG nodes not yet recorded in Lean are not fabricated
as additional hypotheses of the statement.

Edge cases checked: the empty geometric scheme and zero objects cause no
exception; all degrees are integers, including negative degrees in the Koszul
signs; all complexes in the comparison and biduality assertions may be
unbounded; `W` may be zero or arbitrary, with no reflexivity claim; finite-type
hypotheses concern the structure morphism and not the choice of representatives;
`l = ringChar k₀` and nonprime `l` are excluded exactly as in the node. For the
identity Frobenius action, the native abelian category is still the category
with an automorphism, not the underlying category, and this statement keeps it.

Searches performed before writing:

- `msearch.py ... leanfinder`: "Forgetting Frobenius action from derived Weil
  sheaves preserves derived tensor internal Hom symmetry evaluation and
  biduality transpose". Eight hits, including cartesian closed
  `expComparison_iso_of_frobeniusMorphism_iso` and its converse and
  `LightCondensed.ihomPoints` formulas/closedness instances. None is the
  native derived Weil assertion.
- `msearch.py ... loogle`: `"DerivedCategory", "tensor"`: no hits.
- `msearch.py ... grep`: `Weil.*[Dd]erived|[Dd]erived.*Weil|IsoAlgebra` in
  `CategoryTheory`: no hits.
- `rg` for the node id and `native_closed_forgetful|nativeClosedForgetful`
  in `lean/WeilConjectures`, `lean/Sheaf`, and the upstream-name index: no
  full existing theorem. Related native single-resolution Hom lemmas exist
  in `Sheaf/Paper/NativeWeilDerivedHomSingleResolution.lean`; they do not
  assert closedness, comparisons, symmetry, evaluation, or biduality.
- `rg` for ordinary/adical internal-Hom bifunctor wrappers in `lean/Sheaf`
  found no ordinary wrapper. Searches for tensor, Hom, and evaluation in the
  native upstream sources found the underived `Dual` and
  `TensorHomAdjunction` declarations and the two-resolution `DerivedHom`.
  They are reused; no underived tensor/Hom is redefined privately.
- Read the current blueprint proof at
  `literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-thm-sf-package/cor-coef-verdier-weil-equivariance.proof.md`,
  as well as every dependency's recorded signature/docstring and the item's
  eight-step proof, including the recent normalized-adjunction review fix.

The helper definitions package only this item's specified functors, comparisons
and normalization equations, and are listed in `lean.declarations` with their
source/blueprint docstrings. There are no new DAG notions, dependency repairs,
or mathematical statement changes. No statement dispute was found.

Validation uses only `scompile.py` and the prescribed `deliver2.py` dry run.

## Second reading by Q25

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
