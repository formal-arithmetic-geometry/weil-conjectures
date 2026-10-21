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
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
import Sheaf.AlgebraicGeometry.ProEtaleCanonicalPullbackComposition
import Sheaf.AlgebraicGeometry.AbsoluteFrobeniusUniversalHomeomorphism
public import WeilConjectures.AlgebraicGeometry.UniversalHomeomorphismInvariance
import Sheaf.SixFunctors.FrobeniusSquareCartesian
import Mathlib.AlgebraicGeometry.Pullbacks
import Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations
import Sheaf.Paper.IntegralFinitePullbackComposition
import WeilConjectures.AlgebraicGeometry.AbsoluteFrobenius
import WeilConjectures.AlgebraicGeometry.BaseChangeConventions

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

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures.PurityFiniteSetting

/-- Scalar extension of an arbitrary model, without an absolute finite-type assumption.
This abbreviates the recorded base-change functor, rather than introducing another fibre.
Source: blueprint order 2579 (blueprint: def-pur-scheme-geometric-frobenius). -/
abbrev frobeniusFiber (P : PurityFiniteSetting.{u})
    (T₀ : Over (Spec (CommRingCat.of P.field.k₀))) :
    Over (Spec (CommRingCat.of P.field.k)) :=
  (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap P.field.k₀ P.field.k)))).obj T₀

/-- Base change of the given model morphism using `def-pc-base-change`.
Source: blueprint order 2579 (blueprint: def-pur-scheme-geometric-frobenius). -/
abbrev frobeniusMap (P : PurityFiniteSetting.{u})
    {X₀ Y₀ : Over (Spec (CommRingCat.of P.field.k₀))} (f₀ : X₀ ⟶ Y₀) :
    (P.frobeniusFiber X₀).left ⟶ (P.frobeniusFiber Y₀).left :=
  ((Over.pullback
    (Spec.map (CommRingCat.ofHom (algebraMap P.field.k₀ P.field.k)))).map f₀).left

/-- The existing semilinear coefficient action at geometric Frobenius gamma.
Source: blueprint order 2579 (blueprint: def-pur-scheme-geometric-frobenius). -/
abbrev frobeniusGaloisMap (P : PurityFiniteSetting.{u})
    (T₀ : Over (Spec (CommRingCat.of P.field.k₀))) :
    (P.frobeniusFiber T₀).left ⟶ (P.frobeniusFiber T₀).left :=
  P.field.galoisMap T₀.hom
    (@FiniteField.geometricFrobeniusAlgEquivOfAlgebraic P.field.k₀ P.field.k _
      (Fintype.ofFinite P.field.k₀) _ _ _)

/-- The inverse coefficient action, at arithmetic Frobenius sigma.
Source: blueprint order 2579 (blueprint: def-pur-scheme-geometric-frobenius). -/
abbrev frobeniusArithmeticMap (P : PurityFiniteSetting.{u})
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

/-- Absolute q-power Frobenius on the scalar extension, distinct from its k-linear Phi.
Source: blueprint order 2579 (blueprint: def-pur-scheme-geometric-frobenius). -/
def frobeniusAbsoluteMap (P : PurityFiniteSetting.{u})
    (T₀ : Over (Spec (CommRingCat.of P.field.k₀))) :
    (P.frobeniusFiber T₀).left ⟶ (P.frobeniusFiber T₀).left :=
  (P.frobeniusFiber T₀).left.iterateFrobenius P.field.prime
    (P.field.model_characteristic
      (pullback.fst T₀.hom
        (Spec.map (CommRingCat.ofHom (algebraMap P.field.k₀ P.field.k))) ≫ T₀.hom)) P.field.a

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
      rw [hF₁, Category.assoc, hS₁, ← Category.assoc, hA.1]
    · change _ ≫ ρ = (_ ≫ _) ≫ ρ
      rw [hF₂, Category.assoc, hS₂]
      exact hA.2.symm
  have h₂ : P.frobeniusAbsoluteMap T₀ =
      P.frobeniusSchemeMap T₀ ≫ P.frobeniusArithmeticMap T₀ := by
    apply pullback.hom_ext
    · change _ ≫ π = (_ ≫ _) ≫ π
      rw [hF₁, Category.assoc, hA.1, hS₁]
    · change _ ≫ ρ = (_ ≫ _) ≫ ρ
      rw [hF₂, Category.assoc, hA.2, ← Category.assoc, hS₂]
  refine ⟨h₁, h₂, ?_⟩
  rw [h₂, Category.assoc, (P.field.galoisMap_inverse T₀.hom σ).2]
  exact (Category.comp_id (P.frobeniusSchemeMap T₀)).symm

/-- Select the ordinary composition family fixed by the dependency's section equation
for the conjugate direct-image comparison. That equation and the fixed adjunctions
uniquely determine this family; exact descent is the K-flat-normalized derived comparison.
Source: blueprint order 2579; Stacks 0D6D
(blueprint: def-pur-scheme-geometric-frobenius). -/
def frobeniusOrdinaryComposition (P : PurityFiniteSetting.{u})
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    proEtaleConstantRingPullback P.Ring (f ≫ g) ≅
      proEtaleConstantRingPullback P.Ring g ⋙ proEtaleConstantRingPullback P.Ring f :=
  letI : Finite P.Ring := Padic.finite_coefficientExtensionRing
    P.coefficients.l P.extension P.level P.level_pos
  (absoluteFrobenius_proEtale_trivialization_pullback
    P.field.p P.field.prime P.Ring).choose_spec.2.choose f g

/-- Exact descent of the normalized ordinary comparison, with the canonical derived
composition identification of the dependency. Source: blueprint order 2579; Stacks 0D6D
(blueprint: def-pur-scheme-geometric-frobenius). -/
def frobeniusDerivedComposition (P : PurityFiniteSetting.{u})
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    proEtaleConstantRingDerivedPullback P.Ring (f ≫ g) ≅
      proEtaleConstantRingDerivedPullback P.Ring g ⋙
        proEtaleConstantRingDerivedPullback P.Ring f :=
  proEtaleFrobeniusDerivedComp P.Ring f g (P.frobeniusOrdinaryComposition f g)

/-- The canonical relative-Frobenius trivialization at exponent a, followed by exact
termwise descent. The dependency's relative-Frobenius projection equation fixes r;
its section-unit equation then uniquely fixes tau, so this chooses no arbitrary data.
Source: blueprint order 2579, explicit kappa formula; Stacks 0F6W
(blueprint: def-pur-scheme-geometric-frobenius). -/
def frobeniusAbsoluteTrivialization (P : PurityFiniteSetting.{u})
    (T₀ : Over (Spec (CommRingCat.of P.field.k₀))) :
    proEtaleConstantRingDerivedPullback P.Ring (P.frobeniusAbsoluteMap T₀) ≅
      𝟭 (proEtaleDerivedCategory (P.frobeniusFiber T₀).left P.Ring) :=
  letI : Finite P.Ring := Padic.finite_coefficientExtensionRing
    P.coefficients.l P.extension P.level P.level_pos
  proEtaleFrobeniusDerivedIso P.Ring
    ((absoluteFrobenius_proEtale_trivialization_pullback
      P.field.p P.field.prime P.Ring).choose_spec.2.choose_spec.2.choose (P.frobeniusFiber T₀).left
        ⟨P.field.prime, natCast_eq_zero_of_natCast_top_eq_zero
          (P.field.model_characteristic (pullback.fst T₀.hom
            (Spec.map (CommRingCat.ofHom (algebraMap P.field.k₀ P.field.k))) ≫ T₀.hom))⟩
        P.field.a)

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
  Functor.isoWhiskerLeft (proEtaleConstantRingDerivedPullback P.Ring (P.frobeniusGaloisMap T₀))
    (P.frobeniusAbsoluteTrivialization T₀) ≪≫ Functor.rightUnitor _

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

/-- The two paths c_g after Lf*kappa_Y and kappa_X Lf* after c_Phi agree.
Source: blueprint order 2579, final displayed equality of natural transformations
(blueprint: def-pur-scheme-geometric-frobenius).
Proof: the Cartesian Galois square is the first square of
lem-weil-frobenius-square-cartesian. Naturality of the absolute q-power section maps
makes the scheme square commute. On tensor-product affine charts, arithmetic coefficient
Frobenius and the model Frobenius act on the two factors, proving the factorization.
The absolute maps are universal homeomorphisms by
lem-pur-absolute-frobenius-universal-homeomorphism; the etale equivalence is a separate
consequence of thm-weil-pbc-universal-homeomorphism-invariance. For the actual pro-etale
comparison use the canonically normalized tau of
lem-pur-frobenius-trivialization-pullback at exponent a. Its arbitrary-pullback identity
with u=f, followed by naturality of tau_X with the Galois square comparison, gives the
claimed equality. All remaining arrows are the exact descents of normalized composition
comparisons of lem-weil-pbc-proetale-derived-pullback-composition. Their K-flat termwise
normalization implies coherence: on a flat K-flat representative both paths have the
same module comparison, and localization then identifies them on every derived object.
Thus this is the explicitly specified kappa, not an arbitrary comparison isomorphism. -/
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
  sorry

end WeilConjectures.PurityFiniteSetting
