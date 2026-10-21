/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q102
-/
module

public import Sheaf.Paper.PurityFiniteSetting
public import Sheaf.AlgebraicGeometry.FrobeniusDetailed
public import Sheaf.AlgebraicGeometry.FrobeniusTrivializationPullback
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Sheaf.AlgebraicGeometry.NormalizedProEtalePullbackCoherence
import Mathlib.AlgebraicGeometry.Pullbacks
import Sheaf.AlgebraicGeometry.AbsoluteFrobeniusUniversalHomeomorphism
public import WeilConjectures.AlgebraicGeometry.UniversalHomeomorphismInvariance
import Sheaf.SixFunctors.FrobeniusSquareCartesian

/-!
# Scheme and geometric Frobenius of a purity datum

Source: main-20261015 blueprint, `sec-smooth-purity/sk-def-sf-weil-complexes`,
`def-pur-scheme-geometric-frobenius`, order 2579
(blueprint: def-pur-scheme-geometric-frobenius).

The maps use the chosen fibre product and the unrestricted `galoisMap` interface.
The comparison is the specified composite of pullback composition and the canonical
absolute-Frobenius trivialization. The latter's projection and section-unit equations,
and the composition comparison's conjugate-adjunction equation, determine the selected
witnesses up to equality. No unnormalized isomorphism is selected.

## Main definitions

- `PurityFiniteSetting.schemeGeometricFrobeniusComparison`: the comparison kappa.
- `PurityFiniteSetting.frobeniusGaloisSquareComparison`: the Galois-square identification.
- `PurityFiniteSetting.frobeniusSchemeSquareComparison`: the scheme-square identification.

## Main statements

- `PurityFiniteSetting.schemeGeometricFrobenius_squares`: both squares and site invariance.
- `PurityFiniteSetting.schemeGeometricFrobenius_naturality`: the specified equality of paths.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open scoped AlgebraicGeometry

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures.PurityFiniteSetting

attribute [local instance 10000] proEtaleDerivedCanonicalCategory

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

/-- The coefficient ring of the purity datum is finite.
Source: the finite coefficient extension ring at the positive level
(blueprint: def-pur-scheme-geometric-frobenius). -/
theorem coefficient_ring_finite (P : PurityFiniteSetting.{u}) : Finite P.Ring :=
  Padic.finite_coefficientExtensionRing
    P.coefficients.l P.extension P.level P.level_pos

attribute [local irreducible] Ring ringCommRing


/-- Scalar extension of an arbitrary model, without an absolute finite-type assumption.
This abbreviates the recorded base-change functor, rather than introducing another fibre.
Source: blueprint order 2579 (blueprint: def-pur-scheme-geometric-frobenius). -/
def frobeniusFiber (P : PurityFiniteSetting.{u})
    (T₀ : Over (Spec (CommRingCat.of P.field.k₀))) :
    Over (Spec (CommRingCat.of P.field.k)) :=
  (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap P.field.k₀ P.field.k)))).obj T₀

/-- Base change of the given model morphism using `def-pc-base-change`.
Source: blueprint order 2579 (blueprint: def-pur-scheme-geometric-frobenius). -/
def frobeniusMap (P : PurityFiniteSetting.{u})
    {X₀ Y₀ : Over (Spec (CommRingCat.of P.field.k₀))} (f₀ : X₀ ⟶ Y₀) :
    (P.frobeniusFiber X₀).left ⟶ (P.frobeniusFiber Y₀).left :=
  ((Over.pullback
    (Spec.map (CommRingCat.ofHom (algebraMap P.field.k₀ P.field.k)))).map f₀).left

/-- The existing semilinear coefficient action at geometric Frobenius gamma.
Source: blueprint order 2579 (blueprint: def-pur-scheme-geometric-frobenius). -/
def frobeniusGaloisMap (P : PurityFiniteSetting.{u})
    (T₀ : Over (Spec (CommRingCat.of P.field.k₀))) :
    (P.frobeniusFiber T₀).left ⟶ (P.frobeniusFiber T₀).left :=
  P.field.galoisMap T₀.hom
    (@FiniteField.geometricFrobeniusAlgEquivOfAlgebraic P.field.k₀ P.field.k _
      (Fintype.ofFinite P.field.k₀) _ _ _)

/-- The inverse coefficient action, at arithmetic Frobenius sigma.
Source: blueprint order 2579 (blueprint: def-pur-scheme-geometric-frobenius). -/
def frobeniusArithmeticMap (P : PurityFiniteSetting.{u})
    (T₀ : Over (Spec (CommRingCat.of P.field.k₀))) :
    (P.frobeniusFiber T₀).left ⟶ (P.frobeniusFiber T₀).left :=
  P.field.galoisMap T₀.hom
    (@FiniteField.geometricFrobeniusAlgEquivOfAlgebraic P.field.k₀ P.field.k _
      (Fintype.ofFinite P.field.k₀) _ _ _).symm

/-- The actual base change of the model's absolute q-power Frobenius, denoted Phi.
Source: blueprint order 2579 (blueprint: def-pur-scheme-geometric-frobenius). -/
def frobeniusSchemeMap (P : PurityFiniteSetting.{u})
    (T₀ : Over (Spec (CommRingCat.of P.field.k₀))) :
    (P.frobeniusFiber T₀).left ⟶ (P.frobeniusFiber T₀).left :=
  P.frobeniusMap (Over.homMk
    (T₀.left.iterateFrobenius P.field.prime (P.field.model_characteristic T₀.hom) P.field.a)
    (P.field.model_frobenius_over T₀.hom))

/-- The chosen scalar-extension fibre has the characteristic of the model field.
Source: the recorded model characteristic and restriction from top sections
(blueprint: def-pur-scheme-geometric-frobenius). -/
theorem frobeniusFiber_characteristic (P : PurityFiniteSetting.{u})
    (T₀ : Over (Spec (CommRingCat.of P.field.k₀))) :
    (P.frobeniusFiber T₀).left.IsCharacteristic P.field.p :=
  ⟨P.field.prime, natCast_eq_zero_of_natCast_top_eq_zero
    (P.field.model_characteristic (pullback.fst T₀.hom
      (Spec.map (CommRingCat.ofHom (algebraMap P.field.k₀ P.field.k))) ≫ T₀.hom))⟩

/-- Absolute q-power Frobenius on the scalar extension, distinct from its k-linear Phi.
Source: blueprint order 2579 (blueprint: def-pur-scheme-geometric-frobenius). -/
def frobeniusAbsoluteMap (P : PurityFiniteSetting.{u})
    (T₀ : Over (Spec (CommRingCat.of P.field.k₀))) :
    (P.frobeniusFiber T₀).left ⟶ (P.frobeniusFiber T₀).left :=
  (P.frobeniusFiber T₀).left.iterateFrobenius P.field.prime
    ((P.frobeniusFiber_characteristic T₀).2 ⊤) P.field.a

set_option backward.isDefEq.respectTransparency false in
private theorem absolute_naturality {X Y : Scheme.{u}} (f : X ⟶ Y)
    {p : ℕ} (hp : p.Prime) (hX : (p : Γ(X, ⊤)) = 0)
    (hY : (p : Γ(Y, ⊤)) = 0) (n : ℕ) :
    X.iterateFrobenius hp hX n ≫ f = f ≫ Y.iterateFrobenius hp hY n := by
  apply Scheme.Hom.ext (by ext x; rfl)
  intro U
  simp only [Scheme.Hom.comp_app]
  change f.app U ≫ (X.iterateFrobenius hp hX n).app (f ⁻¹ᵁ U) ≫
    X.presheaf.map (𝟙 _) =
      (Y.iterateFrobenius hp hY n).app U ≫ f.app U
  rw [X.presheaf.map_id, Category.comp_id]
  ext s
  exact (map_pow (f.app U).hom s _).symm

set_option backward.isDefEq.respectTransparency false in
/-- Both arithmetic factorizations of absolute Frobenius, and the resulting geometric
factorization used to define kappa. Source: blueprint order 2579, affine verification
(blueprint: def-pur-scheme-geometric-frobenius).
Proof: on Spec(B0 tensor k), the arithmetic coefficient action sends b tensor c to
b tensor c^q; Phi sends it to b^q tensor c. Both composites send it to b^q tensor c^q,
the absolute q-power map. The affine fibre-product identification is supplied by
lem-weil-pbc-fibre-product-affine-spectra. The computations agree on restrictions,
so glue on arbitrary models. Compose with the inverse coefficient action from
def-weil-frobenius-detailed to obtain Phi = F followed by g_gamma. -/
theorem schemeGeometricFrobenius_factorization (P : PurityFiniteSetting.{u})
    (T₀ : Over (Spec (CommRingCat.of P.field.k₀))) :
    P.frobeniusAbsoluteMap T₀ = P.frobeniusArithmeticMap T₀ ≫ P.frobeniusSchemeMap T₀ ∧
    P.frobeniusAbsoluteMap T₀ = P.frobeniusSchemeMap T₀ ≫ P.frobeniusArithmeticMap T₀ ∧
    P.frobeniusSchemeMap T₀ = P.frobeniusAbsoluteMap T₀ ≫ P.frobeniusGaloisMap T₀ := by
  let : Fintype P.field.k₀ := Fintype.ofFinite P.field.k₀
  let b := Spec.map (CommRingCat.ofHom (algebraMap P.field.k₀ P.field.k))
  let π := pullback.fst T₀.hom b
  let ρ := pullback.snd T₀.hom b
  let σ := @FiniteField.geometricFrobeniusAlgEquivOfAlgebraic P.field.k₀ P.field.k _
    (Fintype.ofFinite P.field.k₀) _ _ _
  have hA := P.field.galoisMap_projections T₀.hom σ.symm
  have hS₁ : P.frobeniusSchemeMap T₀ ≫ π = π ≫
      T₀.left.iterateFrobenius P.field.prime (P.field.model_characteristic T₀.hom)
        P.field.a := by
    simp [frobeniusSchemeMap, frobeniusMap, π, b, Over.pullback_map_left]
  have hS₂ : P.frobeniusSchemeMap T₀ ≫ ρ = ρ := by
    simp [frobeniusSchemeMap, frobeniusMap, ρ, b, Over.pullback_map_left]
  have hF₁ : P.frobeniusAbsoluteMap T₀ ≫ π = π ≫
      T₀.left.iterateFrobenius P.field.prime (P.field.model_characteristic T₀.hom)
        P.field.a := absolute_naturality π _ _ _ _
  have hF₂ : P.frobeniusAbsoluteMap T₀ ≫ ρ =
      ρ ≫ Spec.map (CommRingCat.ofHom σ.symm.toRingHom) := by
    apply AlgebraicGeometry.ext_to_Spec
    change (Scheme.ΓSpecIso (CommRingCat.of P.field.k)).inv ≫
        (P.frobeniusAbsoluteMap T₀ ≫ ρ).appTop =
      (Scheme.ΓSpecIso (CommRingCat.of P.field.k)).inv ≫
        (ρ ≫ Spec.map (CommRingCat.ofHom σ.symm.toRingHom)).appTop
    rw [Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop]
    conv_rhs => rw [← Category.assoc, ← Scheme.ΓSpecIso_inv_naturality]
    ext x
    change (ρ.appTop ((Scheme.ΓSpecIso (CommRingCat.of P.field.k)).inv x)) ^
        P.field.p ^ P.field.a =
      ρ.appTop ((Scheme.ΓSpecIso (CommRingCat.of P.field.k)).inv (σ.symm x))
    have hx : σ.symm x = x ^ (P.field.p ^ P.field.a) := by
      change x ^ Fintype.card P.field.k₀ = _
      rw [← Nat.card_eq_fintype_card, P.field.card_base, P.field.cardinality_eq]
    rw [hx, map_pow, map_pow]
  have h₁ : P.frobeniusAbsoluteMap T₀ =
      P.frobeniusArithmeticMap T₀ ≫ P.frobeniusSchemeMap T₀ := by
    apply pullback.hom_ext
    · change _ ≫ π = (_ ≫ _) ≫ π
      erw [hF₁, Category.assoc, hS₁, ← Category.assoc, hA.1]
    · change _ ≫ ρ = (_ ≫ _) ≫ ρ
      rw [hF₂, Category.assoc, hS₂]
      exact hA.2.symm
  have h₂ : P.frobeniusAbsoluteMap T₀ =
      P.frobeniusSchemeMap T₀ ≫ P.frobeniusArithmeticMap T₀ := by
    apply pullback.hom_ext
    · change _ ≫ π = (_ ≫ _) ≫ π
      erw [hF₁, Category.assoc, hA.1, hS₁]
    · change _ ≫ ρ = (_ ≫ _) ≫ ρ
      erw [hF₂, Category.assoc, hA.2, ← Category.assoc, hS₂]
  refine ⟨h₁, h₂, ?_⟩
  erw [h₂, Category.assoc, (P.field.galoisMap_inverse T₀.hom σ).2]
  exact (Category.comp_id (P.frobeniusSchemeMap T₀)).symm

attribute [local irreducible] CategoryTheory.constantSheaf conjugateIsoEquiv
  proEtaleRingModuleAdjunction conjugateEquiv proEtaleRingDirectImageMap
  proEtaleConstantRingComparison proEtaleRingModulePullback
  proEtaleRingModulePullbackObj proEtaleRingModulePullbackMap

attribute [local irreducible] Functor.mapDerivedCategory
  proEtaleFrobeniusDerivedIso proEtaleFrobeniusDerivedComp

attribute [local irreducible] DerivedCategory instCategoryDerivedCategory
  HasDerivedCategory.standard Scheme.iterateFrobenius

/-- The ordinary comparison selected by the normalized Frobenius pullback theorem.
Source: blueprint order 2579 and Stacks 0D6D
(blueprint: def-pur-scheme-geometric-frobenius). -/
def selectedComp (p : ℕ) (hp : p.Prime) (A : Type u)
    [instA : CommRing A] [finA : Finite A] {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    proEtaleConstantRingPullback A (f ≫ g) ≅
      proEtaleConstantRingPullback A g ⋙ proEtaleConstantRingPullback A f :=
  (absoluteFrobenius_proEtale_trivialization_pullback p hp A).choose_spec.2.choose f g

/-- The ordinary trivialization selected jointly with the composition comparison.
Source: blueprint order 2579 and Stacks 0F6W
(blueprint: def-pur-scheme-geometric-frobenius). -/
def selectedTau (p : ℕ) (hp : p.Prime) (A : Type u)
    [instA : CommRing A] [finA : Finite A] (X : Scheme.{u}) (hX : X.IsCharacteristic p) (b : ℕ) :
    proEtaleConstantRingPullback A (X.iterateFrobenius hp (hX.2 ⊤) b) ≅ 𝟭 _ :=
  (absoluteFrobenius_proEtale_trivialization_pullback p hp A).choose_spec.2.choose_spec.2.choose
    X hX b

/-- Exact derived descent of the jointly selected ordinary composition comparison.
Source: blueprint order 2579 and Stacks 0D6D
(blueprint: def-pur-scheme-geometric-frobenius). -/
def selectedDerivedComp (p : ℕ) (hp : p.Prime) (A : Type u)
    [instA : CommRing A] [finA : Finite A] {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    proEtaleConstantRingDerivedPullback A (f ≫ g) ≅
      proEtaleConstantRingDerivedPullback A g ⋙ proEtaleConstantRingDerivedPullback A f :=
  proEtaleFrobeniusDerivedComp A f g (selectedComp p hp A f g)

/-- Exact derived descent of the jointly selected ordinary Frobenius trivialization.
Source: blueprint order 2579 and Stacks 0F6W
(blueprint: def-pur-scheme-geometric-frobenius). -/
def selectedDerivedTau (p : ℕ) (hp : p.Prime) (A : Type u)
    [instA : CommRing A] [finA : Finite A] (X : Scheme.{u}) (hX : X.IsCharacteristic p) (b : ℕ) :
    proEtaleConstantRingDerivedPullback A (X.iterateFrobenius hp (hX.2 ⊤) b) ≅ 𝟭 _ :=
  proEtaleFrobeniusDerivedIso A (selectedTau p hp A X hX b)

attribute [local irreducible] selectedComp selectedTau selectedDerivedComp selectedDerivedTau

section ComparisonDefinitions

attribute [local irreducible] frobeniusFiber frobeniusMap frobeniusGaloisMap
  frobeniusArithmeticMap frobeniusSchemeMap

/-- Select the ordinary composition family fixed by the dependency's section equation
for the conjugate direct-image comparison. That equation and the fixed adjunctions
uniquely determine this family; exact descent is the K-flat-normalized derived comparison.
Source: blueprint order 2579; Stacks 0D6D
(blueprint: def-pur-scheme-geometric-frobenius). -/
def frobeniusOrdinaryComposition (P : PurityFiniteSetting.{u})
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    proEtaleConstantRingPullback P.Ring (f ≫ g) ≅
      proEtaleConstantRingPullback P.Ring g ⋙ proEtaleConstantRingPullback P.Ring f :=
  letI : Finite P.Ring := coefficient_ring_finite P
  selectedComp P.field.p P.field.prime P.Ring f g

/-- Exact descent of the normalized ordinary comparison, with the canonical derived
composition identification of the dependency. Source: blueprint order 2579; Stacks 0D6D
(blueprint: def-pur-scheme-geometric-frobenius). -/
def frobeniusDerivedComposition (P : PurityFiniteSetting.{u})
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    proEtaleConstantRingDerivedPullback P.Ring (f ≫ g) ≅
      proEtaleConstantRingDerivedPullback P.Ring g ⋙
        proEtaleConstantRingDerivedPullback P.Ring f :=
  letI : Finite P.Ring := coefficient_ring_finite P
  selectedDerivedComp P.field.p P.field.prime P.Ring f g

/-- The canonical relative-Frobenius trivialization at exponent a, followed by exact
termwise descent. The dependency's relative-Frobenius projection equation fixes r;
its section-unit equation then uniquely fixes tau, so this chooses no arbitrary data.
Source: blueprint order 2579, explicit kappa formula; Stacks 0F6W
(blueprint: def-pur-scheme-geometric-frobenius). -/
def frobeniusAbsoluteTrivialization (P : PurityFiniteSetting.{u})
    (T₀ : Over (Spec (CommRingCat.of P.field.k₀))) :
    proEtaleConstantRingDerivedPullback P.Ring (P.frobeniusAbsoluteMap T₀) ≅
      𝟭 (proEtaleDerivedCategory (P.frobeniusFiber T₀).left P.Ring) :=
  letI : Finite P.Ring := coefficient_ring_finite P
  selectedDerivedTau P.field.p P.field.prime P.Ring (P.frobeniusFiber T₀).left
    (P.frobeniusFiber_characteristic T₀) P.field.a

/-- The specified comparison kappa: rewrite Phi = F followed by g_gamma, apply the
canonical composition comparison, then tau at exponent a, whiskered by g_gamma.
Source: blueprint order 2579, explicit comparison composite
(blueprint: def-pur-scheme-geometric-frobenius). -/
def schemeGeometricFrobeniusComparison (P : PurityFiniteSetting.{u})
    (T₀ : Over (Spec (CommRingCat.of P.field.k₀))) :
    proEtaleConstantRingDerivedPullback P.Ring (P.frobeniusSchemeMap T₀) ≅
      proEtaleConstantRingDerivedPullback P.Ring (P.frobeniusGaloisMap T₀) :=
  eqToIso (congrArg (proEtaleConstantRingDerivedPullback P.Ring)
    (P.schemeGeometricFrobenius_factorization T₀).2.2) ≪≫
    P.frobeniusDerivedComposition (P.frobeniusAbsoluteMap T₀) (P.frobeniusGaloisMap T₀) ≪≫
    Functor.isoWhiskerLeft (proEtaleConstantRingDerivedPullback P.Ring
      (P.frobeniusGaloisMap T₀)) (P.frobeniusAbsoluteTrivialization T₀) ≪≫
    Functor.rightUnitor _

end ComparisonDefinitions

set_option backward.isDefEq.respectTransparency false in
/-- The Cartesian geometric-Galois square and the commuting scheme-Frobenius square.
The absolute Frobenii are universal homeomorphisms and give equivalences of small etale
sites. Source: blueprint order 2579, two squares and absolute-Frobenius paragraph
(blueprint: def-pur-scheme-geometric-frobenius).
Proof: apply lem-weil-frobenius-square-cartesian to the given model morphism; its
unrestricted coefficient maps give inverse automorphisms and the Cartesian square.
Every ring map preserves qth powers, so model absolute Frobenius commutes with f0;
base change preserves this identity, giving the second square. The scalar-extended
schemes map to Spec(k0) by their first projection. Apply
lem-pur-absolute-frobenius-universal-homeomorphism to these structure maps, then
thm-weil-pbc-universal-homeomorphism-invariance to obtain etale-site equivalences.
Neither argument requires finite type of the structure maps. No Cartesian assertion
about the scheme-Frobenius square is made. -/
theorem schemeGeometricFrobenius_squares (P : PurityFiniteSetting.{u})
    (X₀ Y₀ : Over (Spec (CommRingCat.of P.field.k₀))) (f₀ : X₀ ⟶ Y₀) (d : ℕ)
    [LocallyOfFiniteType f₀.left] [QuasiCompact f₀.left] [IsSeparated f₀.left]
    [SmoothOfRelativeDimension d (P.frobeniusMap f₀)] :
    IsIso (P.frobeniusGaloisMap X₀) ∧ IsIso (P.frobeniusGaloisMap Y₀) ∧
    IsPullback (P.frobeniusGaloisMap X₀) (P.frobeniusMap f₀) (P.frobeniusMap f₀)
      (P.frobeniusGaloisMap Y₀) ∧
    P.frobeniusGaloisMap X₀ ≫ P.frobeniusMap f₀ =
      P.frobeniusMap f₀ ≫ P.frobeniusGaloisMap Y₀ ∧
    P.frobeniusSchemeMap X₀ ≫ P.frobeniusMap f₀ =
      P.frobeniusMap f₀ ≫ P.frobeniusSchemeMap Y₀ ∧
    IsUniversalHomeomorphism (P.frobeniusAbsoluteMap X₀) ∧
    IsUniversalHomeomorphism (P.frobeniusAbsoluteMap Y₀) ∧
    (P.frobeniusAbsoluteMap X₀).Etale.IsEquivalence ∧
    (P.frobeniusAbsoluteMap Y₀).Etale.IsEquivalence ∧
    (Scheme.etaleSetPullback (P.frobeniusAbsoluteMap X₀)).IsEquivalence ∧
    (Scheme.etaleSetPullback (P.frobeniusAbsoluteMap Y₀)).IsEquivalence := by
  let b := Spec.map (CommRingCat.ofHom (algebraMap P.field.k₀ P.field.k))
  let σ := @FiniteField.geometricFrobeniusAlgEquivOfAlgebraic P.field.k₀ P.field.k _
    (Fintype.ofFinite P.field.k₀) _ _ _
  have hX := P.field.galoisMap_inverse X₀.hom σ
  have hY := P.field.galoisMap_inverse Y₀.hom σ
  let eX : (P.frobeniusFiber X₀).left ≅ (P.frobeniusFiber X₀).left :=
    ⟨P.frobeniusGaloisMap X₀, P.frobeniusArithmeticMap X₀, hX.1, hX.2⟩
  let eY : (P.frobeniusFiber Y₀).left ≅ (P.frobeniusFiber Y₀).left :=
    ⟨P.frobeniusGaloisMap Y₀, P.frobeniusArithmeticMap Y₀, hY.1, hY.2⟩
  have hsq := P.field.frobenius_square_cartesian X₀ Y₀ f₀
  have hcomm : P.frobeniusSchemeMap X₀ ≫ P.frobeniusMap f₀ =
      P.frobeniusMap f₀ ≫ P.frobeniusSchemeMap Y₀ := by
    have h : Over.homMk
        (X₀.left.iterateFrobenius P.field.prime (P.field.model_characteristic X₀.hom)
          P.field.a) (P.field.model_frobenius_over X₀.hom) ≫ f₀ =
        f₀ ≫ Over.homMk
          (Y₀.left.iterateFrobenius P.field.prime (P.field.model_characteristic Y₀.hom)
            P.field.a) (P.field.model_frobenius_over Y₀.hom) := by
      apply Over.OverMorphism.ext
      exact absolute_naturality f₀.left P.field.prime
        (P.field.model_characteristic X₀.hom) (P.field.model_characteristic Y₀.hom) _
    unfold frobeniusSchemeMap frobeniusMap
    change ((Over.pullback b).map _).left ≫ ((Over.pullback b).map f₀).left =
      ((Over.pullback b).map f₀).left ≫ ((Over.pullback b).map _).left
    simpa only [Functor.map_comp, Over.comp_left] using
      congrArg (fun g ↦ ((Over.pullback b).map g).left) h
  have hUH (T₀ : Over (Spec (CommRingCat.of P.field.k₀))) :
      IsUniversalHomeomorphism (P.frobeniusAbsoluteMap T₀) := by
    let : (P.frobeniusFiber T₀).left.Over (Spec (CommRingCat.of P.field.k₀)) :=
      ⟨pullback.fst T₀.hom b ≫ T₀.hom⟩
    exact P.field.absoluteFrobenius_isUniversalHomeomorphism (P.frobeniusFiber T₀).left
  have : IsUniversalHomeomorphism (P.frobeniusAbsoluteMap X₀) := hUH X₀
  have : IsUniversalHomeomorphism (P.frobeniusAbsoluteMap Y₀) := hUH Y₀
  have hEX := AlgebraicGeometry.Etale.universalHomeomorphism_invariance.{u, u}
    (P.frobeniusAbsoluteMap X₀)
  have hEY := AlgebraicGeometry.Etale.universalHomeomorphism_invariance.{u, u}
    (P.frobeniusAbsoluteMap Y₀)
  have hset (T₀ : Over (Spec (CommRingCat.of P.field.k₀)))
      [IsUniversalHomeomorphism (P.frobeniusAbsoluteMap T₀)] :
      (Scheme.etaleSetPullback (P.frobeniusAbsoluteMap T₀)).IsEquivalence := by
    obtain ⟨E, hE, _⟩ := (AlgebraicGeometry.Etale.universalHomeomorphism_invariance.{u, u}
      (P.frobeniusAbsoluteMap T₀)).2.2.1
    rw [← hE]
    infer_instance
  exact ⟨eX.isIso_hom, eY.isIso_hom, hsq.2.2.2.2.2.1, hsq.2.2.2.2.1, hcomm,
    hUH X₀, hUH Y₀, hEX.1, hEY.1, hset X₀, hset Y₀⟩

attribute [local irreducible] frobeniusFiber frobeniusMap frobeniusGaloisMap
  frobeniusArithmeticMap frobeniusSchemeMap

/-- The pullback-composition identification from the first commuting square.
Source: blueprint order 2579, c_g (blueprint: def-pur-scheme-geometric-frobenius). -/
def frobeniusGaloisSquareComparison (P : PurityFiniteSetting.{u})
    (X₀ Y₀ : Over (Spec (CommRingCat.of P.field.k₀))) (f₀ : X₀ ⟶ Y₀) (d : ℕ)
    [LocallyOfFiniteType f₀.left] [QuasiCompact f₀.left] [IsSeparated f₀.left]
    [SmoothOfRelativeDimension d (P.frobeniusMap f₀)] :
    proEtaleConstantRingDerivedPullback P.Ring (P.frobeniusGaloisMap Y₀) ⋙
        proEtaleConstantRingDerivedPullback P.Ring (P.frobeniusMap f₀) ≅
      proEtaleConstantRingDerivedPullback P.Ring (P.frobeniusMap f₀) ⋙
        proEtaleConstantRingDerivedPullback P.Ring (P.frobeniusGaloisMap X₀) :=
  (P.frobeniusDerivedComposition (P.frobeniusMap f₀) (P.frobeniusGaloisMap Y₀)).symm ≪≫
    eqToIso (congrArg (proEtaleConstantRingDerivedPullback P.Ring)
      (P.schemeGeometricFrobenius_squares X₀ Y₀ f₀ d).2.2.2.1.symm) ≪≫
    P.frobeniusDerivedComposition (P.frobeniusGaloisMap X₀) (P.frobeniusMap f₀)

/-- The pullback-composition identification from the second commuting square.
Source: blueprint order 2579, c_Phi (blueprint: def-pur-scheme-geometric-frobenius). -/
def frobeniusSchemeSquareComparison (P : PurityFiniteSetting.{u})
    (X₀ Y₀ : Over (Spec (CommRingCat.of P.field.k₀))) (f₀ : X₀ ⟶ Y₀) (d : ℕ)
    [LocallyOfFiniteType f₀.left] [QuasiCompact f₀.left] [IsSeparated f₀.left]
    [SmoothOfRelativeDimension d (P.frobeniusMap f₀)] :
    proEtaleConstantRingDerivedPullback P.Ring (P.frobeniusSchemeMap Y₀) ⋙
        proEtaleConstantRingDerivedPullback P.Ring (P.frobeniusMap f₀) ≅
      proEtaleConstantRingDerivedPullback P.Ring (P.frobeniusMap f₀) ⋙
        proEtaleConstantRingDerivedPullback P.Ring (P.frobeniusSchemeMap X₀) :=
  (P.frobeniusDerivedComposition (P.frobeniusMap f₀) (P.frobeniusSchemeMap Y₀)).symm ≪≫
    eqToIso (congrArg (proEtaleConstantRingDerivedPullback P.Ring)
      (P.schemeGeometricFrobenius_squares X₀ Y₀ f₀ d).2.2.2.2.1.symm) ≪≫
    P.frobeniusDerivedComposition (P.frobeniusSchemeMap X₀) (P.frobeniusMap f₀)



set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

-- Keep the selected comparisons folded during the square calculations.
attribute [local irreducible] frobeniusDerivedComposition frobeniusOrdinaryComposition

attribute [local semireducible] selectedComp selectedTau

attribute [local implicit_reducible] Scheme.IsCharacteristic

private theorem morphism_pasting
    {C : Type*} [Category C] (H : C ⥤ C) (tx : H ≅ 𝟭 C)
    {Q R S T U V B E : C} (α : Q ≅ R) (δ : V ≅ S) (β : B ≅ T)
    (a : R ⟶ S) (b : S ⟶ T) (l : Q ⟶ V) (d : V ⟶ H.obj T)
    (r : Q ⟶ H.obj B) (γ : B ⟶ U) (s : Q ⟶ E) (t : E ⟶ H.obj U)
    (ha : α.hom ≫ a = l ≫ δ.hom)
    (hb : r ≫ H.map β.hom = l ≫ d) (hc : r ≫ H.map γ = s ≫ t)
    (ht : δ.inv ≫ d ≫ tx.hom.app T = b) :
    a ≫ b ≫ β.inv ≫ γ = α.inv ≫ s ≫ t ≫ tx.hom.app U := by
  have ht' : δ.hom ≫ b = d ≫ tx.hom.app T := by
    rw [← ht]
    simp only [Iso.hom_inv_id_assoc]
  have nt := tx.hom.naturality (β.inv ≫ γ)
  simp only [Functor.id_map] at nt
  apply (cancel_epi α.hom).mp
  simp only [Iso.hom_inv_id_assoc]
  rw [reassoc_of% ha, reassoc_of% ht', ← reassoc_of% hb]
  rw [← nt, ← reassoc_of% (H.map_comp _ _)]
  rw [Iso.hom_inv_id_assoc, reassoc_of% hc]

private def selectedCompTo (p : ℕ) (hp : p.Prime) (A : Type u)
    [instA : CommRing A] [finA : Finite A] {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (fg : X ⟶ Z) (w : fg = f ≫ g) :
    proEtaleConstantRingDerivedPullback A fg ≅
      proEtaleConstantRingDerivedPullback A g ⋙ proEtaleConstantRingDerivedPullback A f :=
  eqToIso (congrArg (proEtaleConstantRingDerivedPullback A) w) ≪≫
    selectedDerivedComp p hp A f g

private def compositionObject
    {C D E : Type*} [Category C] [Category D] [Category E]
    (F : C ⥤ D) (G : D ⥤ E) (H : C ⥤ E) (e : H ≅ F ⋙ G) (M : C) :
    H.obj M ≅ G.obj (F.obj M) := e.app M

private def trivializationObject {C : Type*} [Category C]
    (F : C ⥤ C) (e : F ≅ 𝟭 C) (M : C) : F.obj M ≅ M := e.app M

private theorem square_object_components
    {C D : Type*} [Category C] [Category D]
    (L : C ⥤ D) (P : C ⥤ C) (S : D ⥤ D) (F G : C ⥤ D)
    (c1 : F ≅ P ⋙ L) (e : F ≅ G) (c2 : G ≅ L ⋙ S)
    (tx : S ≅ 𝟭 D) (ty : P ≅ 𝟭 C)
    (h : c1.inv ≫ e.hom ≫ c2.hom ≫ Functor.whiskerLeft L tx.hom ≫
      (Functor.rightUnitor L).hom =
      Functor.whiskerRight ty.hom L ≫ (Functor.leftUnitor L).hom) :
    ∀ N : C, (compositionObject P L F c1 N).inv ≫
      (compositionObject L S F (e ≪≫ c2) N).hom ≫
      (trivializationObject S tx (L.obj N)).hom =
      L.map (trivializationObject P ty N).hom := by
  intro N
  simpa [compositionObject, trivializationObject] using NatTrans.congr_app h N

private def selectedCompObject (p : ℕ) (hp : p.Prime) (A : Type u)
    [instA : CommRing A] [finA : Finite A] {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (fg : X ⟶ Z) (w : fg = f ≫ g)
    (M : proEtaleDerivedCategory Z A) :
    (proEtaleConstantRingDerivedPullback A fg).obj M ≅
      (proEtaleConstantRingDerivedPullback A f).obj
        ((proEtaleConstantRingDerivedPullback A g).obj M) :=
  compositionObject (proEtaleConstantRingDerivedPullback A g)
    (proEtaleConstantRingDerivedPullback A f)
    (proEtaleConstantRingDerivedPullback A fg) (selectedCompTo p hp A f g fg w) M

private theorem selected_transport_coherence (p : ℕ) (hp : p.Prime) (A : Type u)
    [instA : CommRing A] [finA : Finite A] {X Y Z W : Scheme.{u}}
    (j : W ⟶ Z) (h : Z ⟶ Y) (k : Y ⟶ X)
    (jh : W ⟶ Y) (hk : Z ⟶ X) (jhk : W ⟶ X)
    (w1 : jh = j ≫ h) (w2 : hk = h ≫ k) (w3 : jhk = j ≫ hk)
    (w4 : jhk = jh ≫ k) (M : proEtaleDerivedCategory X A) :
    (selectedCompTo p hp A j hk jhk w3).hom.app M ≫
        (proEtaleConstantRingDerivedPullback A j).map
          ((selectedCompTo p hp A h k hk w2).hom.app M) =
      (selectedCompTo p hp A jh k jhk w4).hom.app M ≫
        (selectedCompTo p hp A j h jh w1).hom.app
          ((proEtaleConstantRingDerivedPullback A k).obj M) := by
  subst jh
  subst hk
  cases w3
  simpa only [selectedCompTo, eqToIso_refl, Iso.refl_trans] using
    proEtaleNormalizedDerivedComp_coherence A (@selectedComp p hp A instA finA)
      (absoluteFrobenius_proEtale_trivialization_pullback p hp A).choose_spec.2.choose_spec.1
      j h k M

private theorem selected_object_coherence (p : ℕ) (hp : p.Prime) (A : Type u)
    [instA : CommRing A] [finA : Finite A] {X Y Z W : Scheme.{u}}
    (j : W ⟶ Z) (h : Z ⟶ Y) (k : Y ⟶ X)
    (jh : W ⟶ Y) (hk : Z ⟶ X) (jhk : W ⟶ X)
    (w1 : jh = j ≫ h) (w2 : hk = h ≫ k) (w3 : jhk = j ≫ hk)
    (w4 : jhk = jh ≫ k) (M : proEtaleDerivedCategory X A) :
    (selectedCompObject p hp A j hk jhk w3 M).hom ≫
        (proEtaleConstantRingDerivedPullback A j).map
          (selectedCompObject p hp A h k hk w2 M).hom =
      (selectedCompObject p hp A jh k jhk w4 M).hom ≫
        (selectedCompObject p hp A j h jh w1
          ((proEtaleConstantRingDerivedPullback A k).obj M)).hom := by
  simpa only [selectedCompObject, compositionObject, Iso.app_hom] using
    selected_transport_coherence p hp A j h k jh hk jhk w1 w2 w3 w4 M


private def selectedTauObject (p : ℕ) (hp : p.Prime) (A : Type u)
    [instA : CommRing A] [finA : Finite A] (X : Scheme.{u}) (hX : X.IsCharacteristic p)
    (b : ℕ) (M : proEtaleDerivedCategory X A) :
    (proEtaleConstantRingDerivedPullback A (X.iterateFrobenius hp (hX.2 ⊤) b)).obj M ≅ M :=
  trivializationObject
    (proEtaleConstantRingDerivedPullback A (X.iterateFrobenius hp (hX.2 ⊤) b))
    (selectedDerivedTau p hp A X hX b) M

attribute [local semireducible] selectedDerivedComp selectedDerivedTau

attribute [local implicit_reducible] selectedCompObject selectedTauObject
  compositionObject trivializationObject selectedDerivedComp selectedDerivedTau

private theorem selected_object_components (p : ℕ) (hp : p.Prime) (A : Type u)
    [instA : CommRing A] [finA : Finite A] (X Y : Scheme.{u})
    (hX : X.IsCharacteristic p) (hY : Y.IsCharacteristic p) (f : X ⟶ Y) (b : ℕ) :
    ∃ w : X.iterateFrobenius hp (hX.2 ⊤) b ≫ f =
        f ≫ Y.iterateFrobenius hp (hY.2 ⊤) b,
      ∀ N : proEtaleDerivedCategory Y A,
        (selectedCompObject p hp A f (Y.iterateFrobenius hp (hY.2 ⊤) b)
          (f ≫ Y.iterateFrobenius hp (hY.2 ⊤) b) rfl N).inv ≫
          (selectedCompObject p hp A (X.iterateFrobenius hp (hX.2 ⊤) b) f
            (f ≫ Y.iterateFrobenius hp (hY.2 ⊤) b) w.symm N).hom ≫
          (selectedTauObject p hp A X hX b
            ((proEtaleConstantRingDerivedPullback A f).obj N)).hom =
        (proEtaleConstantRingDerivedPullback A f).map
          (selectedTauObject p hp A Y hY b N).hom := by
  have h := (absoluteFrobenius_proEtale_trivialization_pullback
    p hp A).choose_spec.2.choose_spec.2.choose_spec.2.1
  have hh := h X Y hX hY f b
  let w := hh.choose
  have hw := hh.choose_spec
  refine ⟨w, ?_⟩
  simpa only [selectedCompObject, selectedCompTo, selectedTauObject,
    eqToIso_refl, Iso.refl_trans] using square_object_components
    (proEtaleConstantRingDerivedPullback A f)
    (proEtaleConstantRingDerivedPullback A (Y.iterateFrobenius hp (hY.2 ⊤) b))
    (proEtaleConstantRingDerivedPullback A (X.iterateFrobenius hp (hX.2 ⊤) b))
    _ _
    (selectedDerivedComp p hp A f (Y.iterateFrobenius hp (hY.2 ⊤) b))
    (eqToIso (congrArg (proEtaleConstantRingDerivedPullback A) w.symm))
    (selectedDerivedComp p hp A (X.iterateFrobenius hp (hX.2 ⊤) b) f)
    (selectedDerivedTau p hp A X hX b) (selectedDerivedTau p hp A Y hY b) hw


private def compositeApp
    {C D₁ D₂ E : Type*} [Category C] [Category D₁] [Category D₂] [Category E]
    (F₁ : C ⥤ D₁) (G₁ : D₁ ⥤ E) (F₂ : C ⥤ D₂) (G₂ : D₂ ⥤ E)
    (η : F₁ ⋙ G₁ ⟶ F₂ ⋙ G₂) (M : C) :
    G₁.obj (F₁.obj M) ⟶ G₂.obj (F₂.obj M) := η.app M

private theorem composite_ext
    {C D₁ D₂ E : Type*} [Category C] [Category D₁] [Category D₂] [Category E]
    {F₁ : C ⥤ D₁} {G₁ : D₁ ⥤ E} {F₂ : C ⥤ D₂} {G₂ : D₂ ⥤ E}
    {η θ : F₁ ⋙ G₁ ⟶ F₂ ⋙ G₂}
    (h : ∀ M, compositeApp F₁ G₁ F₂ G₂ η M = compositeApp F₁ G₁ F₂ G₂ θ M) :
    η = θ := by
  apply NatTrans.ext
  funext M
  exact h M

private theorem compositeApp_comp
    {C D₁ D₂ D₃ E : Type*} [Category C] [Category D₁] [Category D₂]
    [Category D₃] [Category E]
    {F₁ : C ⥤ D₁} {G₁ : D₁ ⥤ E} (F₂ : C ⥤ D₂) (G₂ : D₂ ⥤ E)
    {F₃ : C ⥤ D₃} {G₃ : D₃ ⥤ E}
    (η : F₁ ⋙ G₁ ⟶ F₂ ⋙ G₂) (θ : F₂ ⋙ G₂ ⟶ F₃ ⋙ G₃) (M : C) :
    compositeApp F₁ G₁ F₃ G₃ (η ≫ θ) M =
      compositeApp F₁ G₁ F₂ G₂ η M ≫ compositeApp F₂ G₂ F₃ G₃ θ M := rfl

private theorem compositeApp_whiskerRight
    {C D E : Type*} [Category C] [Category D] [Category E]
    {F G : C ⥤ D} (η : F ⟶ G) (L : D ⥤ E) (M : C) :
    compositeApp F L G L (Functor.whiskerRight η L) M = L.map (η.app M) := rfl

private theorem compositeApp_whiskerLeft
    {C D E : Type*} [Category C] [Category D] [Category E]
    (L : C ⥤ D) {F G : D ⥤ E} (η : F ⟶ G) (M : C) :
    compositeApp L F L G (Functor.whiskerLeft L η) M = η.app (L.obj M) := rfl

private theorem comparison_square_app
    {C D₁ D₂ E : Type*} [Category C] [Category D₁] [Category D₂] [Category E]
    (F₁ : C ⥤ D₁) (G₁ : D₁ ⥤ E) (F₂ : C ⥤ D₂) (G₂ : D₂ ⥤ E)
    (H H' : C ⥤ E) (a : H ≅ F₁ ⋙ G₁) (e : H ≅ H') (b : H' ≅ F₂ ⋙ G₂)
    (M : C) :
    compositeApp F₁ G₁ F₂ G₂ (a.symm ≪≫ e ≪≫ b).hom M =
      (compositionObject F₁ G₁ H a M).inv ≫
        (compositionObject F₂ G₂ H (e ≪≫ b) M).hom := by
  simp [compositeApp, compositionObject]

private theorem trivialization_comparison_app
    {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) (G : D ⥤ D) (H H' : C ⥤ D)
    (e : H ≅ H') (c : H' ≅ F ⋙ G) (t : G ≅ 𝟭 D) (M : C) :
    (e ≪≫ c ≪≫ Functor.isoWhiskerLeft F t ≪≫ Functor.rightUnitor F).hom.app M =
      (compositionObject F G H (e ≪≫ c) M).hom ≫
        (trivializationObject G t (F.obj M)).hom := by
  simp [compositionObject, trivializationObject, Category.assoc]


private theorem selected_derived_naturality (p : ℕ) (hp : p.Prime) (A : Type u)
    [instA : CommRing A] [finA : Finite A] (X Y : Scheme.{u}) (hX : X.IsCharacteristic p)
    (hY : Y.IsCharacteristic p) (f : X ⟶ Y) (b : ℕ) (gx sx : X ⟶ X)
    (gy sy : Y ⟶ Y) (hg : gx ≫ f = f ≫ gy)
    (hsX : sx = X.iterateFrobenius hp (hX.2 ⊤) b ≫ gx)
    (hsY : sy = Y.iterateFrobenius hp (hY.2 ⊤) b ≫ gy)
    (hs : sx ≫ f = f ≫ sy) :
    Functor.whiskerRight
      (eqToIso (congrArg (proEtaleConstantRingDerivedPullback A) hsY) ≪≫
        selectedDerivedComp p hp A (Y.iterateFrobenius hp (hY.2 ⊤) b) gy ≪≫
        Functor.isoWhiskerLeft (proEtaleConstantRingDerivedPullback A gy)
          (selectedDerivedTau p hp A Y hY b) ≪≫ Functor.rightUnitor _).hom
      (proEtaleConstantRingDerivedPullback A f) ≫
      ((selectedDerivedComp p hp A f gy).symm ≪≫
        eqToIso (congrArg (proEtaleConstantRingDerivedPullback A) hg.symm) ≪≫
        selectedDerivedComp p hp A gx f).hom =
    ((selectedDerivedComp p hp A f sy).symm ≪≫
        eqToIso (congrArg (proEtaleConstantRingDerivedPullback A) hs.symm) ≪≫
        selectedDerivedComp p hp A sx f).hom ≫
      Functor.whiskerLeft (proEtaleConstantRingDerivedPullback A f)
      (eqToIso (congrArg (proEtaleConstantRingDerivedPullback A) hsX) ≪≫
        selectedDerivedComp p hp A (X.iterateFrobenius hp (hX.2 ⊤) b) gx ≪≫
        Functor.isoWhiskerLeft (proEtaleConstantRingDerivedPullback A gx)
          (selectedDerivedTau p hp A X hX b) ≪≫ Functor.rightUnitor _).hom := by
  obtain ⟨hF, ht⟩ := selected_object_components p hp A X Y hX hY f b
  apply composite_ext
    (F₁ := proEtaleConstantRingDerivedPullback A sy)
    (G₁ := proEtaleConstantRingDerivedPullback A f)
    (F₂ := proEtaleConstantRingDerivedPullback A f)
    (G₂ := proEtaleConstantRingDerivedPullback A gx)
  intro M
  rw [compositeApp_comp (proEtaleConstantRingDerivedPullback A gy)
      (proEtaleConstantRingDerivedPullback A f),
    compositeApp_comp (proEtaleConstantRingDerivedPullback A f)
      (proEtaleConstantRingDerivedPullback A sx)]
  rw [compositeApp_whiskerRight, compositeApp_whiskerLeft]
  rw [comparison_square_app, comparison_square_app]
  rw [trivialization_comparison_app, trivialization_comparison_app]
  let FX := X.iterateFrobenius hp (hX.2 ⊤) b
  let FY := Y.iterateFrobenius hp (hY.2 ⊤) b
  let tx := selectedDerivedTau p hp A X hX b
  let F := proEtaleConstantRingDerivedPullback A f
  let H := proEtaleConstantRingDerivedPullback A FX
  let G := proEtaleConstantRingDerivedPullback A gy
  have w : f ≫ sy = FX ≫ (f ≫ gy) := by
    rw [hsY, ← Category.assoc, ← hF, Category.assoc]
  have a := selected_object_coherence p hp A f FY gy (f ≫ FY) sy (f ≫ sy)
    rfl hsY rfl (by rw [hsY, Category.assoc]) M
  have hab := selected_object_coherence p hp A FX f gy (f ≫ FY) (f ≫ gy) (f ≫ sy)
    hF.symm rfl w (by rw [w, ← Category.assoc, hF]) M
  have cc := selected_object_coherence p hp A FX gx f sx (f ≫ gy) (f ≫ sy)
    hsX hg.symm w hs.symm M
  have result := morphism_pasting H tx
    (selectedCompObject p hp A f sy (f ≫ sy) rfl M)
    (selectedCompObject p hp A f FY (f ≫ FY) rfl (G.obj M))
    (selectedCompObject p hp A f gy (f ≫ gy) rfl M)
    (F.map (selectedCompObject p hp A FY gy sy hsY M).hom)
    (F.map (selectedTauObject p hp A Y hY b (G.obj M)).hom)
    (selectedCompObject p hp A (f ≫ FY) gy (f ≫ sy)
      (by rw [hsY, Category.assoc]) M).hom
    (selectedCompObject p hp A FX f (f ≫ FY) hF.symm (G.obj M)).hom
    (selectedCompObject p hp A FX (f ≫ gy) (f ≫ sy) w M).hom
    (selectedCompObject p hp A gx f (f ≫ gy) hg.symm M).hom
    (selectedCompObject p hp A sx f (f ≫ sy) hs.symm M).hom
    (selectedCompObject p hp A FX gx sx hsX (F.obj M)).hom a hab cc (ht (G.obj M))
  simp only [selectedCompObject, selectedTauObject, selectedCompTo,
    eqToIso_refl, Iso.refl_trans, F, G, H, tx, FX, FY,
    Functor.map_comp, Category.assoc] at result ⊢
  exact result


/-- The two paths c_g after Lf*kappa_Y and kappa_X Lf* after c_Phi agree.
Source: blueprint order 2579, final displayed equality of natural transformations
(blueprint: def-pur-scheme-geometric-frobenius).
Proof: use the previously proved factorization Phi_T = F_T followed by g_T and
both commuting square identities. The Frobenius trivialization theorem supplies the
same selected ordinary composition family and tau used in the comparison definitions.
Its section normalization gives associativity by site pullback associativity,
adjunction mates and exact derived descent
(lem-pur-normalized-derived-pullback-coherence). Transport that equality across the
specified equal composite arrows, and apply it to the triples (f,F_Y,g_Y),
(F_X,f,g_Y), and (F_X,g_X,f). The arbitrary-pullback identity for tau, evaluated at
Lg_Y(M), replaces Lf(tau_Y) by tau_X after the absolute-Frobenius square comparison.
Naturality of tau_X with the Galois-square comparison and cancellation of invertible
composition comparisons give the required two paths, on each derived object M.
Thus the equality is for the explicitly specified kappa. -/
theorem schemeGeometricFrobenius_naturality (P : PurityFiniteSetting.{u})
    (X₀ Y₀ : Over (Spec (CommRingCat.of P.field.k₀))) (f₀ : X₀ ⟶ Y₀) (d : ℕ)
    [LocallyOfFiniteType f₀.left] [QuasiCompact f₀.left] [IsSeparated f₀.left]
    [SmoothOfRelativeDimension d (P.frobeniusMap f₀)] :
    Functor.whiskerRight (P.schemeGeometricFrobeniusComparison Y₀).hom
        (proEtaleConstantRingDerivedPullback P.Ring (P.frobeniusMap f₀)) ≫
      (P.frobeniusGaloisSquareComparison X₀ Y₀ f₀ d).hom =
    (P.frobeniusSchemeSquareComparison X₀ Y₀ f₀ d).hom ≫
      Functor.whiskerLeft (proEtaleConstantRingDerivedPullback P.Ring (P.frobeniusMap f₀))
        (P.schemeGeometricFrobeniusComparison X₀).hom := by
  let : Finite P.Ring := coefficient_ring_finite P
  unfold schemeGeometricFrobeniusComparison frobeniusGaloisSquareComparison
    frobeniusSchemeSquareComparison frobeniusDerivedComposition
    frobeniusAbsoluteTrivialization frobeniusAbsoluteMap
  exact selected_derived_naturality P.field.p P.field.prime P.Ring
    (P.frobeniusFiber X₀).left (P.frobeniusFiber Y₀).left
    (P.frobeniusFiber_characteristic X₀) (P.frobeniusFiber_characteristic Y₀)
    (P.frobeniusMap f₀) P.field.a
    (P.frobeniusGaloisMap X₀) (P.frobeniusSchemeMap X₀)
    (P.frobeniusGaloisMap Y₀) (P.frobeniusSchemeMap Y₀)
    (P.schemeGeometricFrobenius_squares X₀ Y₀ f₀ d).2.2.2.1
    (P.schemeGeometricFrobenius_factorization X₀).2.2
    (P.schemeGeometricFrobenius_factorization Y₀).2.2
    (P.schemeGeometricFrobenius_squares X₀ Y₀ f₀ d).2.2.2.2.1

end WeilConjectures.PurityFiniteSetting
