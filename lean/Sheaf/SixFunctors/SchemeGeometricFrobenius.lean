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
public import Sheaf.AlgebraicGeometry.UniversalHomeomorphismInvariance
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
  sorry

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
  sorry

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
