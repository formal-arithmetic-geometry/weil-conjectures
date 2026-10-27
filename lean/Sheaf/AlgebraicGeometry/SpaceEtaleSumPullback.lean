module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceDerivedPullbackModels
import Sheaf.AlgebraicGeometry.SpaceChartTensorRealization
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import Sheaf.AlgebraicGeometry.SpaceCotangentRingMap
import Sheaf.CategoryTheory.LocalizedModuleExactForSystems
import WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
import Sheaf.AlgebraicGeometry.EnlargedRingedCompositionLocalization
import Sheaf.AlgebraicGeometry.SpaceGeometricPointsConservative
import Sheaf.CategoryTheory.RingedSliceExtensionTensor
import Mathlib.Algebra.Homology.BifunctorShift
import Sheaf.Algebra.Homology.RingedSiteRestrictionKFlat
import Sheaf.Paper.KFlatRingedToposPullback
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Paper.RingedTopoiDerivedPullbackIndependent
import WeilConjectures.CategoryTheory.NatTransFromResolvingClass

/-! # Étale sum extension and arbitrary tensor pullback for algebraic spaces

Source: Stacks Project, Modules on Sites, Tags 03DI, 03DJ, 0710 and 0E8I;
Derived Categories of Spaces, equation-stalk-j-shriek (08GU); Cohomology on Sites,
Tags 06YY, 0E8K and 0G7E (blueprint: lem-sfb-space-etale-sum-pullback).

Sum extension is specified by its adjunction to literal étale restriction. Its unit
is the inclusion of each local lift summand. The sheafification universal property
below specifies the sum formula without enlarging the universe of section modules.
The exchange map is the explicit unit-comparison-counit mate, before testing stalks.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u w

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace.EtaleSum

variable {S : Scheme.{u}} {X Z X₁ Z₁ : AlgebraicSpace S}

/-- Literal étale restriction admits sum extension as left adjoint.
Source: Stacks 03DI (blueprint: lem-sfb-space-etale-sum-pullback).
Proof: extend the ringed site to étale algebraic spaces, identify the site of Z
with the slice over Z, and sheafify the presheaf direct sum indexed by lifts.
A map from this sum to a sheaf is exactly a compatible family of maps on its
summands, hence a map to restriction. Transport through the scheme-site equivalences.
The Hom bijection fixes the left adjoint up to its unique adjunction-compatible iso. -/
@[instance] theorem restriction_isRightAdjoint (j : Z ⟶ X) (hj : IsEtale j.hom.hom) :
    (AlgebraicSpace.pullback j hj).IsRightAdjoint := by
  sorry

/-- Sum extension, selected by the left-adjoint universal property of actual restriction.
Source: Stacks 03DI (blueprint: lem-sfb-space-etale-sum-pullback). -/
def extension (j : Z ⟶ X) (hj : IsEtale j.hom.hom) : Z.Modules ⥤ X.Modules :=
  (AlgebraicSpace.pullback j hj).leftAdjoint

/-- The adjunction retains the summand inclusions and the evaluation counit.
Source: Stacks 03DI (blueprint: lem-sfb-space-etale-sum-pullback). -/
def adjunction (j : Z ⟶ X) (hj : IsEtale j.hom.hom) :
    extension j hj ⊣ AlgebraicSpace.pullback j hj :=
  Adjunction.ofIsRightAdjoint (AlgebraicSpace.pullback j hj)

/-- Inclusion of the summand belonging to a scheme chart with its chosen lift to Z.
Source: Stacks 03DI, 0710 (blueprint: lem-sfb-space-etale-sum-pullback). -/
def summand (j : Z ⟶ X) (hj : IsEtale j.hom.hom) (M : Z.Modules)
    (T : Z.EtaleSite) (m : M.val.obj (op T)) :
    ((extension j hj).obj M).val.obj (op ((etaleMap j hj).obj T)) :=
  ((adjunction j hj).unit.app M).val.app (op T) m

/-- The compatible-summand universal property of sheafification of the lift-indexed sum.
Source: Stacks 03DI (blueprint: lem-sfb-space-etale-sum-pullback).
A morphism from the direct-sum presheaf is precisely a compatible map alpha on
lifted charts. Requiring its extension to be unique is the module-sheafification
universal property; arbitrary and empty sets of lifts are included. -/
def SumSheafification (j : Z ⟶ X) (hj : IsEtale j.hom.hom) : Prop :=
  ∀ (M : Z.Modules) (N : X.Modules) (α : M ⟶ (AlgebraicSpace.pullback j hj).obj N),
    ∃! β : (extension j hj).obj M ⟶ N,
      ∀ (T : Z.EtaleSite) (m : M.val.obj (op T)),
        β.val.app (op ((etaleMap j hj).obj T)) (summand j hj M T m) =
          α.val.app (op T) m

/-- Both literal restriction and sum extension are exact, and their counit evaluates
all lift summands. Source: Stacks 03DI, 03DJ (blueprint: lem-sfb-space-etale-sum-pullback).
Proof: compatible maps on summands give the sheafification universal property.
Restriction is exact on the localized site. Extension is right exact as a left
adjoint; it preserves injections because sectionwise direct sums and sheafification
do. The identity map of the restricted module evaluates each summand to itself. -/
theorem exact_sum_evaluation (j : Z ⟶ X) (hj : IsEtale j.hom.hom) :
    SumSheafification j hj ∧
      (extension j hj).Additive ∧ PreservesFiniteLimits (extension j hj) ∧
      PreservesFiniteColimits (extension j hj) ∧
      (AlgebraicSpace.pullback j hj).Additive ∧
      PreservesFiniteLimits (AlgebraicSpace.pullback j hj) ∧
      PreservesFiniteColimits (AlgebraicSpace.pullback j hj) ∧
      ∀ (N : X.Modules) (T : Z.EtaleSite)
        (m : N.val.obj (op ((etaleMap j hj).obj T))),
        ((adjunction j hj).counit.app N).val.app (op ((etaleMap j hj).obj T))
          (summand j hj ((AlgebraicSpace.pullback j hj).obj N) T m) = m := by
  sorry

/-- Étaleness of the primed map follows from the actual Cartesian square.
Source: Stacks 03DI and representable base change
(blueprint: lem-sfb-space-etale-sum-pullback).
Proof: test on a scheme over X₁. Its further fibre product is the scheme test
of j along the composite to X, and the resulting projection is étale. -/
theorem baseChange_etale (j : Z ⟶ X) (h : X₁ ⟶ X) (j₁ : Z₁ ⟶ X₁)
    (hZ : Z₁ ⟶ Z) (hj : IsEtale j.hom.hom) (sq : IsPullback hZ j₁ j h) :
    IsEtale j₁.hom.hom := by
  sorry

/-- The canonical ringed pullback comparison is fixed on each chart tensor.
Source: Stacks 03D8, 03G8, 04LZ (blueprint: lem-sfb-space-etale-sum-pullback). -/
def RestrictionFormula (j : Z ⟶ X) (h : X₁ ⟶ X) (j₁ : Z₁ ⟶ X₁)
    (hZ : Z₁ ⟶ Z) (hj : IsEtale j.hom.hom) (hj₁ : IsEtale j₁.hom.hom)
    (χ : AlgebraicSpace.pullback j hj ⋙ moduleTensorPullback hZ ≅
      moduleTensorPullback h ⋙ AlgebraicSpace.pullback j₁ hj₁) : Prop :=
  ∀ (N : X.Modules) (T : Z.EtaleSite) (r : ModuleChart hZ T)
    (a : (moduleChartTarget h).obj ((etaleMap j₁ hj₁).obj r.left) ⟶
      ((etaleMap j hj).obj T).obj),
    a.left = r.hom.left →
    ∀ (b : Z₁.structureSheaf.obj.obj (op r.left))
      (m : N.val.obj (op ((etaleMap j hj).obj T))),
      (χ.hom.app N).val.app (op r.left)
          (moduleTensorSection hZ ((AlgebraicSpace.pullback j hj).obj N) T r b m) =
        moduleTensorSection h N ((etaleMap j hj).obj T)
          (CostructuredArrow.mk (Y := (etaleMap j₁ hj₁).obj r.left) a) b m

/-- The structural-ring comparison is uniquely normalized by local tensor multiplication.
Source: Stacks 03D8; Properties of Spaces 03G8, 04LZ
(blueprint: lem-sfb-space-etale-sum-pullback).
Proof: use ringed pullback composition for hZ;j = j₁;h and the chart-unit tensor
realization. Restriction has the unchanged structural ring, so the comparison sends
b tensor m to b tensor m on the same underlying scheme chart. These local tensors
generate after sheafification, giving existence, invertibility and uniqueness. -/
theorem restrictionComparison_existsUnique (j : Z ⟶ X) (h : X₁ ⟶ X)
    (j₁ : Z₁ ⟶ X₁) (hZ : Z₁ ⟶ Z) (hj : IsEtale j.hom.hom)
    (sq : IsPullback hZ j₁ j h) :
    ∃! χ : AlgebraicSpace.pullback j hj ⋙ moduleTensorPullback hZ ≅
      moduleTensorPullback h ⋙
        AlgebraicSpace.pullback j₁ (baseChange_etale j h j₁ hZ hj sq),
      RestrictionFormula j h j₁ hZ hj (baseChange_etale j h j₁ hZ hj sq) χ := by
  sorry

/-- The unique chart-normalized restriction comparison, with no arbitrary isomorphism.
Source: Stacks 03D8 (blueprint: lem-sfb-space-etale-sum-pullback). -/
def restrictionComparison (j : Z ⟶ X) (h : X₁ ⟶ X) (j₁ : Z₁ ⟶ X₁)
    (hZ : Z₁ ⟶ Z) (hj : IsEtale j.hom.hom) (sq : IsPullback hZ j₁ j h) :=
  Classical.choose (restrictionComparison_existsUnique j h j₁ hZ hj sq)

/-- Component of the fixed mate, before any invertibility assertion.
Source: Stacks 03DI, 03D8 (blueprint: lem-sfb-space-etale-sum-pullback). -/
def exchangeApp (j : Z ⟶ X) (h : X₁ ⟶ X) (j₁ : Z₁ ⟶ X₁)
    (hZ : Z₁ ⟶ Z) (hj : IsEtale j.hom.hom) (sq : IsPullback hZ j₁ j h)
    (M : Z.Modules) :
    (extension j₁ (baseChange_etale j h j₁ hZ hj sq)).obj
        ((moduleTensorPullback hZ).obj M) ⟶
      (moduleTensorPullback h).obj ((extension j hj).obj M) :=
  (extension j₁ (baseChange_etale j h j₁ hZ hj sq)).map
    ((moduleTensorPullback hZ).map ((adjunction j hj).unit.app M)) ≫
  (extension j₁ (baseChange_etale j h j₁ hZ hj sq)).map
    ((restrictionComparison j h j₁ hZ hj sq).hom.app ((extension j hj).obj M)) ≫
  (adjunction j₁ (baseChange_etale j h j₁ hZ hj sq)).counit.app
    ((moduleTensorPullback h).obj ((extension j hj).obj M))

/-- Naturality of the explicit unit-comparison-counit composite.
Source: Stacks 03DI, 03D8 (blueprint: lem-sfb-space-etale-sum-pullback).
Proof: move a module map past the unit, then the restriction comparison, then the
counit, using their three naturality equations and functoriality of extension. -/
theorem exchange_naturality (j : Z ⟶ X) (h : X₁ ⟶ X) (j₁ : Z₁ ⟶ X₁)
    (hZ : Z₁ ⟶ Z) (hj : IsEtale j.hom.hom) (sq : IsPullback hZ j₁ j h)
    {M N : Z.Modules} (f : M ⟶ N) :
    (extension j₁ (baseChange_etale j h j₁ hZ hj sq)).map
        ((moduleTensorPullback hZ).map f) ≫ exchangeApp j h j₁ hZ hj sq N =
      exchangeApp j h j₁ hZ hj sq M ≫ (moduleTensorPullback h).map
        ((extension j hj).map f) := by
  sorry

/-- The mate of the fixed comparison: insert the slice unit, compare pullbacks,
and evaluate the primed slice counit. Source: Stacks 03DI and 03D8
(blueprint: lem-sfb-space-etale-sum-pullback). -/
def exchange (j : Z ⟶ X) (h : X₁ ⟶ X) (j₁ : Z₁ ⟶ X₁)
    (hZ : Z₁ ⟶ Z) (hj : IsEtale j.hom.hom) (sq : IsPullback hZ j₁ j h) :
    moduleTensorPullback hZ ⋙ extension j₁ (baseChange_etale j h j₁ hZ hj sq) ⟶
      extension j hj ⋙ moduleTensorPullback h where
  app := exchangeApp j h j₁ hZ hj sq
  naturality := fun {_ _} f ↦ exchange_naturality j h j₁ hZ hj sq f


/-- The specified mate is invertible for arbitrary structural-ring pullback.
Source: Stacks 0710, 05V5, 08GU (blueprint: lem-sfb-space-etale-sum-pullback).
Proof: geometric lifts to Z₁ correspond bijectively to lifts to Z. Étaleness
identifies their structural stalk rings. On stalks the mate sends the tensor in
a lift summand to the same tensor in the corresponding summand of the extended
module. Tensor distributes over arbitrary direct sums, including the empty sum,
so it is invertible without flatness. Conservative geometric stalks detect isos. -/
@[instance] theorem exchange_isIso (j : Z ⟶ X) (h : X₁ ⟶ X) (j₁ : Z₁ ⟶ X₁)
    (hZ : Z₁ ⟶ Z) (hj : IsEtale j.hom.hom) (sq : IsPullback hZ j₁ j h) :
    IsIso (exchange j h j₁ hZ hj sq) := by
  sorry

/-- The ordinary comparison in the orientation of the statement.
Source: Stacks 03DI, 0710 (blueprint: lem-sfb-space-etale-sum-pullback). -/
def comparison (j : Z ⟶ X) (h : X₁ ⟶ X) (j₁ : Z₁ ⟶ X₁)
    (hZ : Z₁ ⟶ Z) (hj : IsEtale j.hom.hom) (sq : IsPullback hZ j₁ j h) :=
  (asIso (exchange j h j₁ hZ hj sq)).symm

/-- The summand formula after arbitrary structural-ring tensoring, on local
representatives. Passing to pointed-neighbourhood germs gives exactly the
geometric-fibre direct-sum tensor identification.
Source: Stacks 03DI, 0710, 05V5, 08GU (blueprint: lem-sfb-space-etale-sum-pullback).
Proof: the slice unit inserts the lift summand, the normalized restriction
comparison retains its scalar and its section, and the evaluation counit evaluates
that summand. This gives the formula before taking germs. Every stalk tensor has
such local representatives. Relabelling lifts by the Cartesian square gives the
stated fibre formula; direct sums use finite support even for infinite fibres. -/
theorem exchange_summand (j : Z ⟶ X) (h : X₁ ⟶ X) (j₁ : Z₁ ⟶ X₁)
    (hZ : Z₁ ⟶ Z) (hj : IsEtale j.hom.hom) (sq : IsPullback hZ j₁ j h)
    (M : Z.Modules) (T : Z.EtaleSite) (r : ModuleChart hZ T)
    (a : (moduleChartTarget h).obj
        ((etaleMap j₁ (baseChange_etale j h j₁ hZ hj sq)).obj r.left) ⟶
      ((etaleMap j hj).obj T).obj) (ha : a.left = r.hom.left)
    (b : Z₁.structureSheaf.obj.obj (op r.left)) (m : M.val.obj (op T)) :
    (exchangeApp j h j₁ hZ hj sq M).val.app
        (op ((etaleMap j₁ (baseChange_etale j h j₁ hZ hj sq)).obj r.left))
        (summand j₁ (baseChange_etale j h j₁ hZ hj sq)
          ((moduleTensorPullback hZ).obj M) r.left (moduleTensorSection hZ M T r b m)) =
      moduleTensorSection h ((extension j hj).obj M) ((etaleMap j hj).obj T)
        (CostructuredArrow.mk
          (Y := (etaleMap j₁ (baseChange_etale j h j₁ hZ hj sq)).obj r.left) a)
        b (summand j hj M T m) := by
  sorry

/-- The specified exchange preserves the evaluation counits, after the canonical
restriction comparison. Source: Stacks 03DI, 0710
(blueprint: lem-sfb-space-etale-sum-pullback).
Proof: in each geometric lift summand both paths send m tensor b to m tensor b.
Stalk detection of equality gives the square. Equivalently this is the triangle
identity for the unit-comparison-counit mate, with the normalized comparison. -/
theorem exchange_counit (j : Z ⟶ X) (h : X₁ ⟶ X) (j₁ : Z₁ ⟶ X₁)
    (hZ : Z₁ ⟶ Z) (hj : IsEtale j.hom.hom) (sq : IsPullback hZ j₁ j h)
    (N : X.Modules) :
    exchangeApp j h j₁ hZ hj sq ((AlgebraicSpace.pullback j hj).obj N) ≫
        (moduleTensorPullback h).map ((adjunction j hj).counit.app N) =
      (extension j₁ (baseChange_etale j h j₁ hZ hj sq)).map
          ((restrictionComparison j h j₁ hZ hj sq).hom.app N) ≫
        (adjunction j₁ (baseChange_etale j h j₁ hZ hj sq)).counit.app
          ((moduleTensorPullback h).obj N) := by
  sorry

/-- Additivity needed to act termwise, including on unbounded complexes.
Source: Stacks 03DJ (blueprint: lem-sfb-space-etale-sum-pullback).
Proof: exact sum extension preserves binary sums and their addition maps. -/
@[instance] theorem extension_additive (j : Z ⟶ X) (hj : IsEtale j.hom.hom) :
    (extension j hj).Additive := by
  sorry

/-- Exactness of extension on finite limits.
Source: Stacks 03DJ (blueprint: lem-sfb-space-etale-sum-pullback).
Proof: direct sums preserve injections, sheafification is exact, and extension
is additive; kernels and finite products are therefore preserved. -/
@[instance] theorem extension_limits (j : Z ⟶ X) (hj : IsEtale j.hom.hom) :
    PreservesFiniteLimits (extension j hj) := by
  sorry

/-- Exactness of extension on finite colimits.
Source: Stacks 03DI (blueprint: lem-sfb-space-etale-sum-pullback).
Proof: extension is a left adjoint, hence preserves all colimits. -/
@[instance] theorem extension_colimits (j : Z ⟶ X) (hj : IsEtale j.hom.hom) :
    PreservesFiniteColimits (extension j hj) := by
  sorry

/-- The same sum extension on the existing small affine ringed model.
Source: Stacks 039Z, 03DI (blueprint: lem-sfb-space-etale-sum-pullback). -/
def smallExtension (j : Z ⟶ X) (hj : IsEtale j.hom.hom) :
    Z.SmallModules ⥤ X.SmallModules :=
  Z.smallModuleEquivalence.inverse ⋙ extension j hj ⋙ X.smallModuleRestriction

/-- The same literal restriction on the existing small affine model.
Source: Stacks 039Z, 03DI (blueprint: lem-sfb-space-etale-sum-pullback). -/
def smallRestriction (j : Z ⟶ X) (hj : IsEtale j.hom.hom) :
    X.SmallModules ⥤ Z.SmallModules :=
  X.smallModuleEquivalence.inverse ⋙ AlgebraicSpace.pullback j hj ⋙ Z.smallModuleRestriction

/-- Exactness survives the specified small-site equivalences.
Source: Stacks 039Z, 03DJ (blueprint: lem-sfb-space-etale-sum-pullback).
Proof: equivalences preserve kernels and cokernels; combine this with exactness
of extension and restriction on the original scheme-object sites. -/
theorem small_exact (j : Z ⟶ X) (hj : IsEtale j.hom.hom) :
    (smallExtension j hj).Additive ∧ PreservesFiniteLimits (smallExtension j hj) ∧
      PreservesFiniteColimits (smallExtension j hj) ∧
      (smallRestriction j hj).Additive ∧ PreservesFiniteLimits (smallRestriction j hj) ∧
      PreservesFiniteColimits (smallRestriction j hj) := by
  sorry

/-- Additivity of extension in the shared small model.
Source: Stacks 039Z, 03DJ (blueprint: lem-sfb-space-etale-sum-pullback).
Proof: transport additivity through the two module equivalences. -/
@[instance] theorem smallExtension_additive (j : Z ⟶ X) (hj : IsEtale j.hom.hom) :
    (smallExtension j hj).Additive := by
  sorry

/-- Finite limits for extension in the shared small model.
Source: Stacks 039Z, 03DJ (blueprint: lem-sfb-space-etale-sum-pullback).
Proof: transport preservation of finite limits through the module equivalences. -/
@[instance] theorem smallExtension_limits (j : Z ⟶ X) (hj : IsEtale j.hom.hom) :
    PreservesFiniteLimits (smallExtension j hj) := by
  sorry

/-- Finite colimits for extension in the shared small model.
Source: Stacks 039Z, 03DI (blueprint: lem-sfb-space-etale-sum-pullback).
Proof: transport the left adjunction through the module equivalences. -/
@[instance] theorem smallExtension_colimits (j : Z ⟶ X) (hj : IsEtale j.hom.hom) :
    PreservesFiniteColimits (smallExtension j hj) := by
  sorry

/-- Exact sum extension on the unbounded derived categories, by termwise application.
Source: Stacks 03DJ, 014X (blueprint: lem-sfb-space-etale-sum-pullback). -/
def derivedExtension (j : Z ⟶ X) (hj : IsEtale j.hom.hom)
    [HasDerivedCategory.{w} Z.SmallModules] [HasDerivedCategory.{w} X.SmallModules] :
    Z.DerivedModules ⥤ X.DerivedModules :=
  (smallExtension j hj).mapDerivedCategory

/-- Additivity of literal restriction in the small model.
Source: Stacks 039Z, 03DJ (blueprint: lem-sfb-space-etale-sum-pullback).
Proof: restriction is additive sectionwise and equivalences preserve addition. -/
@[instance] theorem smallRestriction_additive (j : Z ⟶ X) (hj : IsEtale j.hom.hom) :
    (smallRestriction j hj).Additive := by
  sorry

/-- Restriction and extension preserve flat-term K-flat complexes with no bounds.
Source: Stacks 0E8I, 0E8K, 0G7E (blueprint: lem-sfb-space-etale-sum-pullback).
Proof: the projection isomorphism (j_!P) tensor H = j_!(P tensor j^*H)
proves flatness using exactness of restriction and extension. Summing it in each
integer total degree gives the complex projection isomorphism, commuting with both
differentials and their Koszul signs. An acyclic H restricts to an acyclic complex;
K-flatness of P and exact extension prove the extended tensor acyclic. Restriction
preserves K-flatness by 0E8K and flat terms by 0G7E. These arguments use direct sums,
never products or boundedness. Transport preserves the same tensor universal properties. -/
theorem preserves_flatKFlat (j : Z ⟶ X) (hj : IsEtale j.hom.hom) :
    (∀ P : CochainComplex Z.SmallModules ℤ, SingleComplex.FlatKFlat Z P →
      SingleComplex.FlatKFlat X
        (((smallExtension j hj).mapHomologicalComplex (.up ℤ)).obj P)) ∧
    (∀ P : CochainComplex X.SmallModules ℤ, SingleComplex.FlatKFlat X P →
      SingleComplex.FlatKFlat Z
        (((smallRestriction j hj).mapHomologicalComplex (.up ℤ)).obj P)) := by
  sorry


/-- Transport of the fixed mate through the specified affine-basis equivalences.
Source: Stacks 039Z, 03DI (blueprint: lem-sfb-space-etale-sum-pullback). -/
def smallExchangeApp (j : Z ⟶ X) (h : X₁ ⟶ X) (j₁ : Z₁ ⟶ X₁)
    (hZ : Z₁ ⟶ Z) (hj : IsEtale j.hom.hom) (sq : IsPullback hZ j₁ j h)
    (M : Z.SmallModules) :
    (smallExtension j₁ (baseChange_etale j h j₁ hZ hj sq)).obj
        ((smallModuleTensorPullback hZ).obj M) ⟶
      (smallModuleTensorPullback h).obj ((smallExtension j hj).obj M) :=
  X₁.smallModuleRestriction.map
    ((extension j₁ (baseChange_etale j h j₁ hZ hj sq)).map
        (Z₁.smallModuleEquivalence.unitIso.inv.app
          ((moduleTensorPullback hZ).obj (Z.smallModuleEquivalence.inverse.obj M))) ≫
      exchangeApp j h j₁ hZ hj sq (Z.smallModuleEquivalence.inverse.obj M) ≫
      (moduleTensorPullback h).map (X.smallModuleEquivalence.unitIso.hom.app
        ((extension j hj).obj (Z.smallModuleEquivalence.inverse.obj M))))

/-- Naturality survives the fixed equivalence transport.
Source: Stacks 039Z, 03DI (blueprint: lem-sfb-space-etale-sum-pullback).
Proof: naturality of the two equivalence units and of exchange gives this equation
by functoriality of restriction. -/
theorem smallExchange_naturality (j : Z ⟶ X) (h : X₁ ⟶ X) (j₁ : Z₁ ⟶ X₁)
    (hZ : Z₁ ⟶ Z) (hj : IsEtale j.hom.hom) (sq : IsPullback hZ j₁ j h)
    {M N : Z.SmallModules} (f : M ⟶ N) :
    (smallExtension j₁ (baseChange_etale j h j₁ hZ hj sq)).map
        ((smallModuleTensorPullback hZ).map f) ≫ smallExchangeApp j h j₁ hZ hj sq N =
      smallExchangeApp j h j₁ hZ hj sq M ≫ (smallModuleTensorPullback h).map
        ((smallExtension j hj).map f) := by
  sorry

/-- The termwise exchange on the same small ringed models as derived pullback.
Source: Stacks 039Z, 03DI (blueprint: lem-sfb-space-etale-sum-pullback). -/
def smallExchange (j : Z ⟶ X) (h : X₁ ⟶ X) (j₁ : Z₁ ⟶ X₁)
    (hZ : Z₁ ⟶ Z) (hj : IsEtale j.hom.hom) (sq : IsPullback hZ j₁ j h) :
    smallModuleTensorPullback hZ ⋙ smallExtension j₁ (baseChange_etale j h j₁ hZ hj sq) ⟶
      smallExtension j hj ⋙ smallModuleTensorPullback h where
  app := smallExchangeApp j h j₁ hZ hj sq
  naturality := fun {_ _} f ↦ smallExchange_naturality j h j₁ hZ hj sq f

/-- The transported ordinary comparison is invertible.
Source: Stacks 039Z, 0710 (blueprint: lem-sfb-space-etale-sum-pullback).
Proof: every component is the original invertible mate conjugated by the two
specified equivalence units, so is invertible. -/
@[instance] theorem smallExchange_isIso (j : Z ⟶ X) (h : X₁ ⟶ X) (j₁ : Z₁ ⟶ X₁)
    (hZ : Z₁ ⟶ Z) (hj : IsEtale j.hom.hom) (sq : IsPullback hZ j₁ j h) :
    IsIso (smallExchange j h j₁ hZ hj sq) := by
  sorry

/-- The comparison chain map, using only the prescribed degreewise maps.
Source: Stacks 06YY, 014X (blueprint: lem-sfb-space-etale-sum-pullback). -/
def complexExchange (j : Z ⟶ X) (h : X₁ ⟶ X) (j₁ : Z₁ ⟶ X₁)
    (hZ : Z₁ ⟶ Z) (hj : IsEtale j.hom.hom) (sq : IsPullback hZ j₁ j h)
    (P : CochainComplex Z.SmallModules ℤ) :
    ((smallExtension j₁ (baseChange_etale j h j₁ hZ hj sq)).mapHomologicalComplex (.up ℤ)).obj
        (((smallModuleTensorPullback hZ).mapHomologicalComplex (.up ℤ)).obj P) ⟶
      ((smallModuleTensorPullback h).mapHomologicalComplex (.up ℤ)).obj
        (((smallExtension j hj).mapHomologicalComplex (.up ℤ)).obj P) :=
  ((smallExchange j h j₁ hZ hj sq).mapHomologicalComplex (.up ℤ)).app P

/-- Literal restriction composes as precomposition on the unchanged scheme charts.
Source: Stacks 03DI, 03D8 (blueprint: lem-sfb-space-etale-sum-pullback).
Proof: the two chart maps differ only by associativity of natural-transformation
composition. Extensionality on the underlying chart objects, ring sections, module
sections and restriction maps, followed by proof irrelevance, identifies the functors.
This is an equality of the explicit restriction constructions, not an equality of
arbitrarily selected adjoints. -/
theorem restriction_comp {T : AlgebraicSpace S} (k : T ⟶ Z) (j : Z ⟶ X)
    (hk : IsEtale k.hom.hom) (hj : IsEtale j.hom.hom) :
    AlgebraicSpace.pullback j hj ⋙ AlgebraicSpace.pullback k hk =
      AlgebraicSpace.pullback (k ≫ j) (isEtale_comp _ _ hk hj) := by
  sorry

/-- Canonical restriction composition is transport along the literal chart equality.
Source: Stacks 03DI (blueprint: lem-sfb-space-etale-sum-pullback). -/
def restrictionComposition {T : AlgebraicSpace S} (k : T ⟶ Z) (j : Z ⟶ X)
    (hk : IsEtale k.hom.hom) (hj : IsEtale j.hom.hom) :=
  eqToIso (restriction_comp k j hk hj)

/-- Flattening the two lift labels, defined as the adjunction-composition mate.
Source: Stacks 03DI (blueprint: lem-sfb-space-etale-sum-pullback). -/
def composition {T : AlgebraicSpace S} (k : T ⟶ Z) (j : Z ⟶ X)
    (hk : IsEtale k.hom.hom) (hj : IsEtale j.hom.hom) :
    extension k hk ⋙ extension j hj ≅ extension (k ≫ j) (isEtale_comp _ _ hk hj) :=
  Adjunction.leftAdjointCompIso (adjunction k hk) (adjunction j hj)
    (adjunction (k ≫ j) (isEtale_comp _ _ hk hj)) (restrictionComposition k j hk hj)

/-- Nested evaluation agrees with evaluation after flattening lift labels.
Source: Stacks 03DI, 0710 (blueprint: lem-sfb-space-etale-sum-pullback).
Proof: the composition is the mate of the identity-on-sections restriction
comparison. In both paths each pair of lifts evaluates its section to the same
section of N. Sheafification, or conservative geometric stalks, detects equality. -/
theorem composition_counit {T : AlgebraicSpace S} (k : T ⟶ Z) (j : Z ⟶ X)
    (hk : IsEtale k.hom.hom) (hj : IsEtale j.hom.hom) (N : X.Modules) :
    (composition k j hk hj).hom.app
          ((AlgebraicSpace.pullback (k ≫ j) (isEtale_comp _ _ hk hj)).obj N) ≫
        (adjunction (k ≫ j) (isEtale_comp _ _ hk hj)).counit.app N =
      (extension j hj).map ((extension k hk).map
          ((restrictionComposition k j hk hj).inv.app N)) ≫
        (extension j hj).map ((adjunction k hk).counit.app
          ((AlgebraicSpace.pullback j hj).obj N)) ≫
        (adjunction j hj).counit.app N := by
  sorry

/-- Exchange commutes with composition of étale slices, using the same flattening maps.
Source: Stacks 03DI, 0710, 03D8 (blueprint: lem-sfb-space-etale-sum-pullback).
Proof: relabel a pair of lifts to Z and then T by its single composite lift.
Both paths send its tensor m tensor b to the same tensor in the composite lift
summand. On iterated structural scalars both give m tensor bc by balancing.
Conservative geometric stalks detect the equality. No finiteness is needed. -/
theorem exchange_composition {T T₁ : AlgebraicSpace S}
    (j : Z ⟶ X) (h : X₁ ⟶ X) (j₁ : Z₁ ⟶ X₁) (hZ : Z₁ ⟶ Z)
    (hj : IsEtale j.hom.hom) (sq : IsPullback hZ j₁ j h)
    (k : T ⟶ Z) (k₁ : T₁ ⟶ Z₁) (hT : T₁ ⟶ T)
    (hk : IsEtale k.hom.hom) (sqk : IsPullback hT k₁ k hZ) (M : T.Modules) :
    (extension j₁ (baseChange_etale j h j₁ hZ hj sq)).map
          (exchangeApp k hZ k₁ hT hk sqk M) ≫
        exchangeApp j h j₁ hZ hj sq ((extension k hk).obj M) ≫
        (moduleTensorPullback h).map ((composition k j hk hj).hom.app M) =
      (composition k₁ j₁ (baseChange_etale k hZ k₁ hT hk sqk)
          (baseChange_etale j h j₁ hZ hj sq)).hom.app ((moduleTensorPullback hT).obj M) ≫
        exchangeApp (k ≫ j) h (k₁ ≫ j₁) hT (isEtale_comp _ _ hk hj)
          (sqk.paste_vert sq) M := by
  sorry

/-- The original slice adjunction transported through the specified equivalences.
Source: Stacks 039Z, 03DI (blueprint: lem-sfb-space-etale-sum-pullback). -/
def smallAdjunction (j : Z ⟶ X) (hj : IsEtale j.hom.hom) :
    smallExtension j hj ⊣ smallRestriction j hj :=
  (Z.smallModuleEquivalence.symm.toAdjunction.comp (adjunction j hj)).comp
    X.smallModuleEquivalence.toAdjunction

/-- Restriction preserves finite limits on the small model.
Source: Stacks 039Z, 03DJ (blueprint: lem-sfb-space-etale-sum-pullback).
Proof: transport exactness of literal restriction through the equivalences. -/
@[instance] theorem smallRestriction_limits (j : Z ⟶ X) (hj : IsEtale j.hom.hom) :
    PreservesFiniteLimits (smallRestriction j hj) := by
  sorry

/-- Restriction preserves finite colimits on the small model.
Source: Stacks 039Z, 03DJ (blueprint: lem-sfb-space-etale-sum-pullback).
Proof: transport exactness of literal restriction through the equivalences. -/
@[instance] theorem smallRestriction_colimits (j : Z ⟶ X) (hj : IsEtale j.hom.hom) :
    PreservesFiniteColimits (smallRestriction j hj) := by
  sorry

/-- The canonical termwise slice restriction on derived modules.
Source: Stacks 014X, 03DJ (blueprint: lem-sfb-space-etale-sum-pullback). -/
def derivedRestriction (j : Z ⟶ X) (hj : IsEtale j.hom.hom)
    [HasDerivedCategory.{w} X.SmallModules] [HasDerivedCategory.{w} Z.SmallModules] :
    X.DerivedModules ⥤ Z.DerivedModules :=
  (smallRestriction j hj).mapDerivedCategory

variable [HasDerivedCategory.{w} X.SmallModules] [HasDerivedCategory.{w} Z.SmallModules]
  [HasDerivedCategory.{w} X₁.SmallModules] [HasDerivedCategory.{w} Z₁.SmallModules]

/-- The derived exchange has exactly the stated ordinary comparison as its value on
EVERY flat-term K-flat representative; the two routes retain the canonical derived
pullback counits and the exact-extension localization comparison.
Source: Stacks 06YS, 06YY (blueprint: lem-sfb-space-etale-sum-pullback). -/
def DerivedComputation (j : Z ⟶ X) (h : X₁ ⟶ X) (j₁ : Z₁ ⟶ X₁)
    (hZ : Z₁ ⟶ Z) (hj : IsEtale j.hom.hom) (sq : IsPullback hZ j₁ j h)
    (δ : derivedTensorPullback hZ ⋙ derivedExtension j₁ (baseChange_etale j h j₁ hZ hj sq) ≅
      derivedExtension j hj ⋙ derivedTensorPullback h) : Prop :=
  ∀ P : CochainComplex Z.SmallModules ℤ, SingleComplex.FlatKFlat Z P →
    δ.hom.app (DerivedCategory.Q.obj P) ≫
        (derivedTensorPullback h).map ((smallExtension j hj).mapDerivedCategoryFactors.hom.app P) ≫
        ((smallTensorPullbackComplex h).totalLeftDerivedCounit DerivedCategory.Q
          (HomologicalComplex.quasiIso X.SmallModules (.up ℤ))).app
          (((smallExtension j hj).mapHomologicalComplex (.up ℤ)).obj P) =
      (derivedExtension j₁ (baseChange_etale j h j₁ hZ hj sq)).map
          (((smallTensorPullbackComplex hZ).totalLeftDerivedCounit DerivedCategory.Q
            (HomologicalComplex.quasiIso Z.SmallModules (.up ℤ))).app P) ≫
        (smallExtension j₁ (baseChange_etale j h j₁ hZ hj sq)).mapDerivedCategoryFactors.hom.app
          (((smallModuleTensorPullback hZ).mapHomologicalComplex (.up ℤ)).obj P) ≫
        DerivedCategory.Q.map (complexExchange j h j₁ hZ hj sq P)

/-- The fixed ordinary mate descends uniquely to the unbounded derived categories.
Source: Stacks 06YS, 06YY; Derived Categories 05RT; Categories 04VK
(blueprint: lem-sfb-space-etale-sum-pullback).
Proof, following the node's steps 5--8:
1. The projection formula and exactness prove that extension preserves flat-term
   K-flat complexes; restriction does so by the restriction K-flat theorem.
2. Resolve any complex by a flat-term K-flat P. Exact extension takes P to an
   adapted resolution. The canonical left-derived counits compute both composites
   by their termwise values, and exchange_summand is their chain isomorphism.
3. Naturality extends this comparison from the resolving class to the homotopy
   category. The right calculus of fractions and localization universal property
   descend it to the derived category. Descend the inverse in the same way.
4. Natural comparison with a resolution identifies each composite with the identity,
   and shows uniqueness. Thus computation holds on every adapted representative,
   not only on one selected resolution, and on all maps between representatives.
5. Finite sums and shifts remain adapted. Their comparisons and nested-slice
   counits are degreewise maps, so their ordinary equalities descend by this same
   unique comparison; no bounds, finite fibres or flatness of h are used. -/
theorem derivedComparison_existsUnique (j : Z ⟶ X) (h : X₁ ⟶ X) (j₁ : Z₁ ⟶ X₁)
    (hZ : Z₁ ⟶ Z) (hj : IsEtale j.hom.hom) (sq : IsPullback hZ j₁ j h) :
    ∃! δ : derivedTensorPullback hZ ⋙
        derivedExtension j₁ (baseChange_etale j h j₁ hZ hj sq) ≅
      derivedExtension j hj ⋙ derivedTensorPullback h,
      DerivedComputation j h j₁ hZ hj sq δ := by
  sorry

/-- The derived comparison is selected from its unique computation on all K-flat models.
Source: Stacks 06YY (blueprint: lem-sfb-space-etale-sum-pullback). -/
def derivedComparison (j : Z ⟶ X) (h : X₁ ⟶ X) (j₁ : Z₁ ⟶ X₁)
    (hZ : Z₁ ⟶ Z) (hj : IsEtale j.hom.hom) (sq : IsPullback hZ j₁ j h) :=
  (Classical.choose (derivedComparison_existsUnique j h j₁ hZ hj sq)).symm


/-- The standard termwise shift transported through localization Q.
Source: Stacks 014X (blueprint: lem-sfb-space-etale-sum-pullback). -/
@[instance_reducible] def tensorComplexShift {A B : AlgebraicSpace S}
    [HasDerivedCategory.{w} A.SmallModules] (f : A ⟶ B) :
    (smallTensorPullbackComplex f).CommShift ℤ :=
  Functor.CommShift.comp
    ((smallModuleTensorPullback f).mapHomologicalComplex (.up ℤ)) DerivedCategory.Q

/-- Exact extension uses Mathlib's standard localization shift comparison.
Source: Stacks 014X (blueprint: lem-sfb-space-etale-sum-pullback). -/
@[instance_reducible] def extensionShift (j : Z ⟶ X) (hj : IsEtale j.hom.hom) :
    (derivedExtension j hj).CommShift ℤ :=
  inferInstanceAs ((smallExtension j hj).mapDerivedCategory.CommShift ℤ)

/-- Normalization of a derived pullback shift by its canonical computation counit.
Source: Stacks 06YY, 014X (blueprint: lem-sfb-space-etale-sum-pullback). -/
def PullbackShiftFormula {A B : AlgebraicSpace S}
    [HasDerivedCategory.{w} A.SmallModules] [HasDerivedCategory.{w} B.SmallModules]
    (f : A ⟶ B) (sh : (derivedTensorPullback f).CommShift ℤ) : Prop :=
  ∀ (n : ℤ) (P : CochainComplex B.SmallModules ℤ),
    (derivedTensorPullback f).map ((DerivedCategory.Q.commShiftIso n).hom.app P) ≫
        (sh.commShiftIso n).hom.app (DerivedCategory.Q.obj P) ≫
        (shiftFunctor A.DerivedModules n).map
          (((smallTensorPullbackComplex f).totalLeftDerivedCounit DerivedCategory.Q
            (HomologicalComplex.quasiIso B.SmallModules (.up ℤ))).app P) =
      ((smallTensorPullbackComplex f).totalLeftDerivedCounit DerivedCategory.Q
          (HomologicalComplex.quasiIso B.SmallModules (.up ℤ))).app
          ((shiftFunctor (CochainComplex B.SmallModules ℤ) n).obj P) ≫
        ((tensorComplexShift f).commShiftIso n).hom.app P

/-- Canonical shifts on derived pullback exist with their counit normalization.
Source: Stacks 06YY, 014X (blueprint: lem-sfb-space-etale-sum-pullback).
Proof: compute on flat-term K-flat complexes. Their shifts are adapted, and termwise
pullback commutes with the signed shift differential. Descent along quasi-isomorphisms
gives the coherent shift data and its counit equation. All objects have an adapted
resolution, so this normalization determines the shift data uniquely. -/
theorem pullbackShift_existsUnique {A B : AlgebraicSpace S}
    [HasDerivedCategory.{w} A.SmallModules] [HasDerivedCategory.{w} B.SmallModules]
    (f : A ⟶ B) :
    ∃! sh : (derivedTensorPullback f).CommShift ℤ, PullbackShiftFormula f sh := by
  sorry

/-- The canonical shift structure, fixed by computation on complexes.
Source: Stacks 06YY (blueprint: lem-sfb-space-etale-sum-pullback). -/
@[instance_reducible] def pullbackShift {A B : AlgebraicSpace S}
    [HasDerivedCategory.{w} A.SmallModules] [HasDerivedCategory.{w} B.SmallModules]
    (f : A ⟶ B) : (derivedTensorPullback f).CommShift ℤ :=
  Classical.choose (pullbackShift_existsUnique f)

/-- Ordinary termwise exchange commutes with the canonical signed shift maps.
Source: Stacks 014X, 06YY (blueprint: lem-sfb-space-etale-sum-pullback).
Proof: in degree r both paths are the same ordinary comparison at P.X(r+n).
The shifted differentials have the same sign (-1)^n, preserved by additivity. -/
theorem complexExchange_shift (j : Z ⟶ X) (h : X₁ ⟶ X) (j₁ : Z₁ ⟶ X₁)
    (hZ : Z₁ ⟶ Z) (hj : IsEtale j.hom.hom) (sq : IsPullback hZ j₁ j h) :
    NatTrans.CommShift ((smallExchange j h j₁ hZ hj sq).mapHomologicalComplex (.up ℤ)) ℤ := by
  sorry

/-- Derived exchange preserves the canonical shifts, with each constituent's
normalization specified by its computation counit, rather than chosen freely.
Source: Stacks 014X, 06YY (blueprint: lem-sfb-space-etale-sum-pullback).
Proof: resolve by P and compare both paths by DerivedComputation. Shifted P is
again flat-term K-flat. The ordinary shift equality gives equal chain maps; the
canonical pullback and exact-extension computation counits descend this equality. -/
theorem derivedComparison_shift (j : Z ⟶ X) (h : X₁ ⟶ X) (j₁ : Z₁ ⟶ X₁)
    (hZ : Z₁ ⟶ Z) (hj : IsEtale j.hom.hom) (sq : IsPullback hZ j₁ j h)
    (n : ℤ) (K : Z.DerivedModules) :
    (derivedComparison j h j₁ hZ hj sq).inv.app
          ((shiftFunctor Z.DerivedModules n).obj K) ≫
        (derivedTensorPullback h).map
          (((extensionShift j hj).commShiftIso n).hom.app K) ≫
        ((pullbackShift h).commShiftIso n).hom.app ((derivedExtension j hj).obj K) =
      (derivedExtension j₁ (baseChange_etale j h j₁ hZ hj sq)).map
          (((pullbackShift hZ).commShiftIso n).hom.app K) ≫
        ((extensionShift j₁ (baseChange_etale j h j₁ hZ hj sq)).commShiftIso n).hom.app
          ((derivedTensorPullback hZ).obj K) ≫
        (shiftFunctor X₁.DerivedModules n).map
          ((derivedComparison j h j₁ hZ hj sq).inv.app K) := by
  sorry

/-- The two ordinary functors preserve every finite sum, including the empty sum.
Their natural comparison therefore commutes with the canonical finite-sum maps.
Source: Stacks 03DI, 03D7 (blueprint: lem-sfb-space-etale-sum-pullback).
Proof: both tensor pullback and sum extension are left adjoints. Each preserves
colimits. Naturality at each sum injection identifies their comparison with the
sum of its components; the empty case is their preserved zero object. -/
theorem comparison_finiteSums (j : Z ⟶ X) (h : X₁ ⟶ X) (j₁ : Z₁ ⟶ X₁)
    (hZ : Z₁ ⟶ Z) (hj : IsEtale j.hom.hom) (sq : IsPullback hZ j₁ j h)
    (I : Type u) [Finite I] :
    PreservesColimitsOfShape (Discrete I) (extension j hj ⋙ moduleTensorPullback h) ∧
      PreservesColimitsOfShape (Discrete I)
        (moduleTensorPullback hZ ⋙ extension j₁ (baseChange_etale j h j₁ hZ hj sq)) := by
  sorry

/-- Derived comparison preserves finite sums, including zero, by the same model formula.
Source: Stacks 06YS, 06YY, 014X (blueprint: lem-sfb-space-etale-sum-pullback).
Proof: choose adapted representatives for the finitely many summands. Their finite
sum remains adapted. The ordinary comparison is the sum of its components, so
DerivedComputation gives the same equation after localization; additivity provides
finite-sum preservation and includes the empty sum. -/
theorem derivedComparison_finiteSums (j : Z ⟶ X) (h : X₁ ⟶ X) (j₁ : Z₁ ⟶ X₁)
    (hZ : Z₁ ⟶ Z) (hj : IsEtale j.hom.hom) (sq : IsPullback hZ j₁ j h)
    (I : Type u) [Finite I] :
    PreservesColimitsOfShape (Discrete I) (derivedExtension j hj ⋙ derivedTensorPullback h) ∧
      PreservesColimitsOfShape (Discrete I)
        (derivedTensorPullback hZ ⋙
          derivedExtension j₁ (baseChange_etale j h j₁ hZ hj sq)) := by
  sorry


/-- The derived evaluation counit is uniquely its termwise evaluation on complexes.
Source: Stacks 014X, 03DI (blueprint: lem-sfb-space-etale-sum-pullback).
Proof: apply the ordinary evaluation counit degreewise and localize. Naturality
makes this a transformation before localization; full faithfulness of restriction
along Q gives existence and uniqueness with the specified factorization maps. -/
theorem derivedCounit_existsUnique (j : Z ⟶ X) (hj : IsEtale j.hom.hom) :
    ∃! ε : derivedRestriction j hj ⋙ derivedExtension j hj ⟶ 𝟭 X.DerivedModules,
      ∀ P : CochainComplex X.SmallModules ℤ,
        ε.app (DerivedCategory.Q.obj P) =
          (derivedExtension j hj).map
              ((smallRestriction j hj).mapDerivedCategoryFactors.hom.app P) ≫
            (smallExtension j hj).mapDerivedCategoryFactors.hom.app
              (((smallRestriction j hj).mapHomologicalComplex (.up ℤ)).obj P) ≫
            DerivedCategory.Q.map
              (((smallAdjunction j hj).counit.mapHomologicalComplex (.up ℤ)).app P) := by
  sorry

/-- The fixed derived evaluation map, selected by its unique termwise normalization.
Source: Stacks 014X, 03DI (blueprint: lem-sfb-space-etale-sum-pullback). -/
def derivedCounit (j : Z ⟶ X) (hj : IsEtale j.hom.hom) :=
  Classical.choose (derivedCounit_existsUnique j hj)

/-- Transport the ordinary restriction comparison to the shared small models.
Source: Stacks 039Z, 03D8 (blueprint: lem-sfb-space-etale-sum-pullback). -/
def smallRestrictionComparisonApp (j : Z ⟶ X) (h : X₁ ⟶ X) (j₁ : Z₁ ⟶ X₁)
    (hZ : Z₁ ⟶ Z) (hj : IsEtale j.hom.hom) (sq : IsPullback hZ j₁ j h)
    (M : X.SmallModules) :
    (smallModuleTensorPullback hZ).obj ((smallRestriction j hj).obj M) ⟶
      (smallRestriction j₁ (baseChange_etale j h j₁ hZ hj sq)).obj
        ((smallModuleTensorPullback h).obj M) :=
  Z₁.smallModuleRestriction.map
    ((moduleTensorPullback hZ).map (Z.smallModuleEquivalence.unitIso.inv.app
        ((AlgebraicSpace.pullback j hj).obj (X.smallModuleEquivalence.inverse.obj M))) ≫
      (restrictionComparison j h j₁ hZ hj sq).hom.app (X.smallModuleEquivalence.inverse.obj M) ≫
      (AlgebraicSpace.pullback j₁ (baseChange_etale j h j₁ hZ hj sq)).map
        (X₁.smallModuleEquivalence.unitIso.hom.app
          ((moduleTensorPullback h).obj (X.smallModuleEquivalence.inverse.obj M))))

/-- Naturality of transported restriction comparison.
Source: Stacks 039Z, 03D8 (blueprint: lem-sfb-space-etale-sum-pullback).
Proof: compose naturality of the original normalized comparison with naturality
of the equivalence units and apply the restriction functor. -/
theorem smallRestrictionComparison_naturality (j : Z ⟶ X) (h : X₁ ⟶ X)
    (j₁ : Z₁ ⟶ X₁) (hZ : Z₁ ⟶ Z) (hj : IsEtale j.hom.hom)
    (sq : IsPullback hZ j₁ j h) {M N : X.SmallModules} (f : M ⟶ N) :
    (smallModuleTensorPullback hZ).map ((smallRestriction j hj).map f) ≫
        smallRestrictionComparisonApp j h j₁ hZ hj sq N =
      smallRestrictionComparisonApp j h j₁ hZ hj sq M ≫
        (smallRestriction j₁ (baseChange_etale j h j₁ hZ hj sq)).map
          ((smallModuleTensorPullback h).map f) := by
  sorry

/-- The transported comparison as a natural transformation.
Source: Stacks 039Z, 03D8 (blueprint: lem-sfb-space-etale-sum-pullback). -/
def smallRestrictionComparison (j : Z ⟶ X) (h : X₁ ⟶ X) (j₁ : Z₁ ⟶ X₁)
    (hZ : Z₁ ⟶ Z) (hj : IsEtale j.hom.hom) (sq : IsPullback hZ j₁ j h) :
    smallRestriction j hj ⋙ smallModuleTensorPullback hZ ⟶
      smallModuleTensorPullback h ⋙
        smallRestriction j₁ (baseChange_etale j h j₁ hZ hj sq) where
  app := smallRestrictionComparisonApp j h j₁ hZ hj sq
  naturality := fun {_ _} f ↦ smallRestrictionComparison_naturality j h j₁ hZ hj sq f

/-- The derived restriction comparison is uniquely the ordinary one on adapted models.
Source: Stacks 06YS, 06YY, 0E8K (blueprint: lem-sfb-space-etale-sum-pullback).
Proof: restriction preserves adapted complexes. Compute both derived pullbacks
on such a complex, use the transported ordinary comparison in each degree, and
descend through resolutions. Local tensor normalization fixes the chain map;
localization gives the unique transformation and inverse. -/
theorem derivedRestrictionComparison_existsUnique (j : Z ⟶ X) (h : X₁ ⟶ X)
    (j₁ : Z₁ ⟶ X₁) (hZ : Z₁ ⟶ Z) (hj : IsEtale j.hom.hom)
    (sq : IsPullback hZ j₁ j h) :
    ∃! χ : derivedRestriction j hj ⋙ derivedTensorPullback hZ ≅
        derivedTensorPullback h ⋙
          derivedRestriction j₁ (baseChange_etale j h j₁ hZ hj sq),
      ∀ (P : CochainComplex X.SmallModules ℤ), SingleComplex.FlatKFlat X P →
          χ.hom.app (DerivedCategory.Q.obj P) ≫
              (derivedRestriction j₁ (baseChange_etale j h j₁ hZ hj sq)).map
                (((smallTensorPullbackComplex h).totalLeftDerivedCounit DerivedCategory.Q
                  (HomologicalComplex.quasiIso X.SmallModules (.up ℤ))).app P) ≫
              (Functor.mapDerivedCategoryFactors
                (smallRestriction j₁ (baseChange_etale j h j₁ hZ hj sq))).hom.app
                (((smallModuleTensorPullback h).mapHomologicalComplex (.up ℤ)).obj P) =
            (derivedTensorPullback hZ).map
                ((smallRestriction j hj).mapDerivedCategoryFactors.hom.app P) ≫
              ((smallTensorPullbackComplex hZ).totalLeftDerivedCounit DerivedCategory.Q
                (HomologicalComplex.quasiIso Z.SmallModules (.up ℤ))).app
                (((smallRestriction j hj).mapHomologicalComplex (.up ℤ)).obj P) ≫
              DerivedCategory.Q.map
                (((smallRestrictionComparison j h j₁ hZ hj sq).mapHomologicalComplex
                  (.up ℤ)).app P) := by
  sorry

/-- The canonical derived restriction comparison, fixed by ordinary local tensors.
Source: Stacks 06YY, 0E8K (blueprint: lem-sfb-space-etale-sum-pullback). -/
def derivedRestrictionComparison (j : Z ⟶ X) (h : X₁ ⟶ X) (j₁ : Z₁ ⟶ X₁)
    (hZ : Z₁ ⟶ Z) (hj : IsEtale j.hom.hom) (sq : IsPullback hZ j₁ j h) :=
  Classical.choose (derivedRestrictionComparison_existsUnique j h j₁ hZ hj sq)

/-- The derived comparison preserves the specified evaluation counit square.
Source: Stacks 03DI, 06YY, 0E8K (blueprint: lem-sfb-space-etale-sum-pullback).
Proof: resolve N on X by an adapted P. Its restriction and successive extensions
remain adapted. The ordinary exchange_counit is exactly the required chain-map
identity on this P. DerivedComputation and the two counit normalizations give the
square at Q(P); naturality in its resolution isomorphism gives it for every N. -/
theorem derivedComparison_counit (j : Z ⟶ X) (h : X₁ ⟶ X) (j₁ : Z₁ ⟶ X₁)
    (hZ : Z₁ ⟶ Z) (hj : IsEtale j.hom.hom) (sq : IsPullback hZ j₁ j h)
    (N : X.DerivedModules) :
    (derivedComparison j h j₁ hZ hj sq).inv.app ((derivedRestriction j hj).obj N) ≫
        (derivedTensorPullback h).map ((derivedCounit j hj).app N) =
      (derivedExtension j₁ (baseChange_etale j h j₁ hZ hj sq)).map
          ((derivedRestrictionComparison j h j₁ hZ hj sq).hom.app N) ≫
        (derivedCounit j₁ (baseChange_etale j h j₁ hZ hj sq)).app
          ((derivedTensorPullback h).obj N) := by
  sorry


/-- Flatten nested sum extensions in the original small-model coefficient universe.
The middle equivalence unit is removed before applying ordinary flattening.
Source: Stacks 039Z, 03DI (blueprint: lem-sfb-space-etale-sum-pullback). -/
def smallCompositionApp {T : AlgebraicSpace S} (k : T ⟶ Z) (j : Z ⟶ X)
    (hk : IsEtale k.hom.hom) (hj : IsEtale j.hom.hom) (M : T.SmallModules) :
    (smallExtension j hj).obj ((smallExtension k hk).obj M) ⟶
      (smallExtension (k ≫ j) (isEtale_comp _ _ hk hj)).obj M :=
  X.smallModuleRestriction.map
    ((extension j hj).map (Z.smallModuleEquivalence.unitIso.inv.app
        ((extension k hk).obj (T.smallModuleEquivalence.inverse.obj M))) ≫
      (composition k j hk hj).hom.app (T.smallModuleEquivalence.inverse.obj M))

/-- Naturality of flattened sum extension on the small models.
Source: Stacks 039Z, 03DI (blueprint: lem-sfb-space-etale-sum-pullback).
Proof: use naturality of the removed equivalence unit and of the ordinary
adjunction-composition isomorphism; apply the outer restriction functor. -/
theorem smallComposition_naturality {T : AlgebraicSpace S} (k : T ⟶ Z) (j : Z ⟶ X)
    (hk : IsEtale k.hom.hom) (hj : IsEtale j.hom.hom)
    {M N : T.SmallModules} (f : M ⟶ N) :
    (smallExtension j hj).map ((smallExtension k hk).map f) ≫
        smallCompositionApp k j hk hj N =
      smallCompositionApp k j hk hj M ≫
        (smallExtension (k ≫ j) (isEtale_comp _ _ hk hj)).map f := by
  sorry

/-- The fixed natural flattening transformation, before localization.
Source: Stacks 039Z, 03DI (blueprint: lem-sfb-space-etale-sum-pullback). -/
def smallComposition {T : AlgebraicSpace S} (k : T ⟶ Z) (j : Z ⟶ X)
    (hk : IsEtale k.hom.hom) (hj : IsEtale j.hom.hom) :
    smallExtension k hk ⋙ smallExtension j hj ⟶
      smallExtension (k ≫ j) (isEtale_comp _ _ hk hj) where
  app := smallCompositionApp k j hk hj
  naturality := fun {_ _} f ↦ smallComposition_naturality k j hk hj f

/-- Exact termwise flattening induces the uniquely normalized derived composition.
Source: Stacks 03DI, 014X (blueprint: lem-sfb-space-etale-sum-pullback).
Proof: flatten the two lift labels degreewise; its inverse separates the two labels.
Both are natural chain maps. Descend through Q; its universal property makes the
result unique with the displayed factorization through the standard exact-functor
computation maps. The construction works for every complex, with no resolutions
needed for exact extension. -/
theorem derivedComposition_existsUnique {T : AlgebraicSpace S}
    [HasDerivedCategory.{w} T.SmallModules] (k : T ⟶ Z) (j : Z ⟶ X)
    (hk : IsEtale k.hom.hom) (hj : IsEtale j.hom.hom) :
    ∃! e : derivedExtension k hk ⋙ derivedExtension j hj ≅
        derivedExtension (k ≫ j) (isEtale_comp _ _ hk hj),
      ∀ P : CochainComplex T.SmallModules ℤ,
        e.hom.app (DerivedCategory.Q.obj P) ≫
            (smallExtension (k ≫ j) (isEtale_comp _ _ hk hj)).mapDerivedCategoryFactors.hom.app P =
          (derivedExtension j hj).map
              ((smallExtension k hk).mapDerivedCategoryFactors.hom.app P) ≫
            (smallExtension j hj).mapDerivedCategoryFactors.hom.app
              (((smallExtension k hk).mapHomologicalComplex (.up ℤ)).obj P) ≫
            DerivedCategory.Q.map
              (((smallComposition k j hk hj).mapHomologicalComplex (.up ℤ)).app P) := by
  sorry

/-- The derived flattening map is determined by its explicit termwise sum formula.
Source: Stacks 03DI, 014X (blueprint: lem-sfb-space-etale-sum-pullback). -/
def derivedComposition {T : AlgebraicSpace S} [HasDerivedCategory.{w} T.SmallModules]
    (k : T ⟶ Z) (j : Z ⟶ X) (hk : IsEtale k.hom.hom) (hj : IsEtale j.hom.hom) :=
  Classical.choose (derivedComposition_existsUnique k j hk hj)

/-- The derived comparison commutes with flattening nested étale extensions.
Source: Stacks 03DI, 06YY, 0710 (blueprint: lem-sfb-space-etale-sum-pullback).
Proof: resolve M by a flat-term K-flat P. Its extensions and restrictions remain
adapted. DerivedComputation identifies this equation with exchange_composition on P,
with the derivedComposition equation removing the localization comparison maps.
Naturality along the resolution quasi-isomorphism proves it for arbitrary M.
The same argument applied to exchange_counit and composition_counit proves the
nested evaluation equations, using the fixed termwise derivedCounit normalization. -/
theorem derivedComparison_composition {T T₁ : AlgebraicSpace S}
    [HasDerivedCategory.{w} T.SmallModules] [HasDerivedCategory.{w} T₁.SmallModules]
    (j : Z ⟶ X) (h : X₁ ⟶ X) (j₁ : Z₁ ⟶ X₁) (hZ : Z₁ ⟶ Z)
    (hj : IsEtale j.hom.hom) (sq : IsPullback hZ j₁ j h)
    (k : T ⟶ Z) (k₁ : T₁ ⟶ Z₁) (hT : T₁ ⟶ T)
    (hk : IsEtale k.hom.hom) (sqk : IsPullback hT k₁ k hZ) (M : T.DerivedModules) :
    (derivedExtension j₁ (baseChange_etale j h j₁ hZ hj sq)).map
          ((derivedComparison k hZ k₁ hT hk sqk).inv.app M) ≫
        (derivedComparison j h j₁ hZ hj sq).inv.app ((derivedExtension k hk).obj M) ≫
        (derivedTensorPullback h).map ((derivedComposition k j hk hj).hom.app M) =
      (derivedComposition k₁ j₁ (baseChange_etale k hZ k₁ hT hk sqk)
          (baseChange_etale j h j₁ hZ hj sq)).hom.app ((derivedTensorPullback hT).obj M) ≫
        (derivedComparison (k ≫ j) h (k₁ ≫ j₁) hT (isEtale_comp _ _ hk hj)
          (sqk.paste_vert sq)).inv.app M := by
  sorry

end AlgebraicGeometry.AlgebraicSpace.EtaleSum
