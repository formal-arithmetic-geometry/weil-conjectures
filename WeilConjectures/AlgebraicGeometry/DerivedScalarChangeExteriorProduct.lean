/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.KunnethGlobalSections
public import WeilConjectures.AlgebraicGeometry.FieldRestrictionExteriorProduct
public import WeilConjectures.AlgebraicGeometry.EtaleDerivedScalarTensor
public import WeilConjectures.Algebra.Homology.OrdinaryDerivedChangeOfRings
public import WeilConjectures.AlgebraicGeometry.Sites.TorsionEtaleCohomologicalDimension
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.GroupTheory.Torsion
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

/-!
# Derived scalar change and the exterior product

Source: literature/stacks-project/etale-cohomology.tex, Tag 0F12
(blueprint: lem-pur-exterior-product-derived-scalar-change).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

/-- The scalar-unit equation fixing the B-linear sections comparison through the
canonical restriction/sections mate. Source: Stacks 0F12 and 0FPI
(blueprint: lem-pur-exterior-product-derived-scalar-change). -/
def scalarSectionsUnitNormalization
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (T : Scheme.{u})
    (a : ModuleCat.ordinaryDerivedExtendScalars φ ⊣ ModuleCat.derivedRestrictScalars φ)
    (β : rightDerivedGlobalSections (ModuleCat.{u + 1} A) T ⋙
        ModuleCat.ordinaryDerivedExtendScalars φ ≅
      scalarExtension φ T ⋙ rightDerivedGlobalSections (ModuleCat.{u + 1} B) T) : Prop :=
  ∀ H : DerivedCategoryModule A T,
    a.unit.app ((rightDerivedGlobalSections (ModuleCat.{u + 1} A) T).obj H) ≫
        (ModuleCat.derivedRestrictScalars φ).map (β.hom.app H) ≫
        (fieldRestrictionSectionsMap φ T).app ((scalarExtension φ T).obj H) =
      (rightDerivedGlobalSections (ModuleCat.{u + 1} A) T).map
        ((Adjunction.ofIsRightAdjoint
          (Sheaf.derivedRestrictScalars T.smallEtaleTopology φ)).unit.app H)

/-- The normalized data asserting that derived extension of scalars commutes with
unbounded etale global sections and with the counit-defined exterior product.
Source: Stacks Project, Tag 0F12 (blueprint: lem-pur-exterior-product-derived-scalar-change).
The beta fields are natural isomorphisms, and the tensor comparison fields are the
canonical comparisons normalized on derived scalar-extension representatives. -/
structure DerivedScalarChangeExteriorProductData
    (A B : Type (u + 1)) [CommRing A] [CommRing B]
    (φ : A →+* B) {k : Type u} [Field k] [IsSepClosed k]
    {X Y : Scheme.{u}} (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k))
    [CompactSpace X] [QuasiSeparatedSpace X]
    [CompactSpace Y] [QuasiSeparatedSpace Y]
    [CompactSpace (pullback f g : Scheme.{u})]
    [QuasiSeparatedSpace (pullback f g : Scheme.{u})] where
  pointAdjunction :
    ModuleCat.ordinaryDerivedExtendScalars φ ⊣ ModuleCat.derivedRestrictScalars φ
  pointAdjunction_normalization : ∀ P : CochainComplex (ModuleCat.{u + 1} A) ℤ,
    (HomologicalComplex.quasiIso (ModuleCat.{u + 1} A) (.up ℤ)).kFlat P →
      (ModuleCat.ordinaryDerivedChangeOfRings φ).counit.app P =
        scalarAdjunctionRepresentativeMap
          (ModuleCat.extendScalars.{u + 1, u + 1, u + 1} φ)
          (ModuleCat.restrictScalars.{u + 1} φ)
          (ModuleCat.extendRestrictScalarsAdj.{u + 1, u + 1, u + 1} φ)
          (ModuleCat.ordinaryDerivedExtendScalars φ) pointAdjunction P
  betaX :
    (rightDerivedGlobalSections (ModuleCat.{u + 1} A) X ⋙
      ModuleCat.ordinaryDerivedExtendScalars φ) ≅
      (scalarExtension φ X ⋙
        rightDerivedGlobalSections (ModuleCat.{u + 1} B) X)
  betaY :
    (rightDerivedGlobalSections (ModuleCat.{u + 1} A) Y ⋙
      ModuleCat.ordinaryDerivedExtendScalars φ) ≅
      (scalarExtension φ Y ⋙
        rightDerivedGlobalSections (ModuleCat.{u + 1} B) Y)
  betaW :
    (rightDerivedGlobalSections (ModuleCat.{u + 1} A) (pullback f g) ⋙
      ModuleCat.ordinaryDerivedExtendScalars φ) ≅
      (scalarExtension φ (pullback f g) ⋙
        rightDerivedGlobalSections (ModuleCat.{u + 1} B) (pullback f g))
  betaX_normalization : scalarSectionsUnitNormalization φ X pointAdjunction betaX
  betaY_normalization : scalarSectionsUnitNormalization φ Y pointAdjunction betaY
  betaW_normalization :
    scalarSectionsUnitNormalization φ (pullback f g) pointAdjunction betaW
  tensor0 : ∀ (M N : DerivedCategory (ModuleCat.{u + 1} A)),
    (ModuleCat.ordinaryDerivedExtendScalars φ).obj (M ⊗ N) ≅
      (ModuleCat.ordinaryDerivedExtendScalars φ).obj M ⊗
        (ModuleCat.ordinaryDerivedExtendScalars φ).obj N
  tensor0_canonical : ∀ (M N : DerivedCategory (ModuleCat.{u + 1} A)),
    tensor0 M N = (Functor.Monoidal.μIso
      (ModuleCat.ordinaryDerivedExtendScalars φ) M N).symm
  restrictionTensorW : RestrictionTensorData
    (Sheaf.restrictScalars (pullback f g).smallEtaleTopology φ)
    (sheafComposeLaxMonoidal (pullback f g).smallEtaleTopology
      (ModuleCat.restrictScalars φ))
  tensorW : ∀ (K : DerivedCategoryModule A X) (L : DerivedCategoryModule A Y),
    (scalarExtension φ (pullback f g)).obj
        (((derivedTensor (ModuleCat.{u + 1} A) (pullback f g)).obj
          ((upperStar (ModuleCat.{u + 1} A) (pullback.fst f g)).leftDerivedFunctor.obj K)).obj
          ((upperStar (ModuleCat.{u + 1} A) (pullback.snd f g)).leftDerivedFunctor.obj L)) ≅
      ((derivedTensor (ModuleCat.{u + 1} B) (pullback f g)).obj
        ((upperStar (ModuleCat.{u + 1} B) (pullback.fst f g)).leftDerivedFunctor.obj
          ((scalarExtension φ X).obj K))).obj
        ((upperStar (ModuleCat.{u + 1} B) (pullback.snd f g)).leftDerivedFunctor.obj
          ((scalarExtension φ Y).obj L))
  tensorW_normalization : ∀ (K : DerivedCategoryModule A X) (L : DerivedCategoryModule A Y),
    (Adjunction.ofIsRightAdjoint
        (Sheaf.derivedRestrictScalars (pullback f g).smallEtaleTopology φ)).unit.app
          (((upperStar (ModuleCat.{u + 1} A) (pullback.fst f g)).leftDerivedFunctor.obj K) ⊗
            ((upperStar (ModuleCat.{u + 1} A) (pullback.snd f g)).leftDerivedFunctor.obj L)) ≫
      (Sheaf.derivedRestrictScalars (pullback f g).smallEtaleTopology φ).map
        (tensorW K L).hom =
    (((upperStar (ModuleCat.{u + 1} A) (pullback.fst f g)).leftDerivedFunctor.map
          ((Adjunction.ofIsRightAdjoint
            (Sheaf.derivedRestrictScalars X.smallEtaleTopology φ)).unit.app K) ≫
        (scalarRestrictionPullbackIso φ (pullback.fst f g)).hom.app
          ((scalarExtension φ X).obj K)) ⊗ₘ
      ((upperStar (ModuleCat.{u + 1} A) (pullback.snd f g)).leftDerivedFunctor.map
          ((Adjunction.ofIsRightAdjoint
            (Sheaf.derivedRestrictScalars Y.smallEtaleTopology φ)).unit.app L) ≫
        (scalarRestrictionPullbackIso φ (pullback.snd f g)).hom.app
          ((scalarExtension φ Y).obj L))) ≫
      restrictionTensorW.map
        ((upperStar (ModuleCat.{u + 1} B) (pullback.fst f g)).leftDerivedFunctor.obj
          ((scalarExtension φ X).obj K))
        ((upperStar (ModuleCat.{u + 1} B) (pullback.snd f g)).leftDerivedFunctor.obj
          ((scalarExtension φ Y).obj L))
  square : ∀ (K : DerivedCategoryModule A X) (L : DerivedCategoryModule A Y),
    (ModuleCat.ordinaryDerivedExtendScalars φ).map
        (kunnethGlobalSectionsMap A (pullback.fst f g) (pullback.snd f g)
          f g pullback.condition.symm K L) ≫
      betaW.hom.app _ ≫
      (rightDerivedGlobalSections (ModuleCat.{u + 1} B) (pullback f g)).map
        (tensorW K L).hom =
    (tensor0
        ((rightDerivedGlobalSections (ModuleCat.{u + 1} A) X).obj K)
        ((rightDerivedGlobalSections (ModuleCat.{u + 1} A) Y).obj L)).hom ≫
      (betaX.hom.app K ⊗ₘ betaY.hom.app L) ≫
      kunnethGlobalSectionsMap B (pullback.fst f g) (pullback.snd f g) f g
        pullback.condition.symm ((scalarExtension φ X).obj K) ((scalarExtension φ Y).obj L)

/-- Derived extension of scalars preserves the exterior product under the canonical
constant-sheaf comparisons. Source: Stacks Project, Tag 0F12
(blueprint: lem-pur-exterior-product-derived-scalar-change).

Proof.
1. For each `T ∈ {X, Y, W}` and `H`, `β_{T,H}` is the scalar-unit adjunct of
   lem-pur-scalar-adjunction-beta-unbounded (the `beta*_normalization` fields); its
   restriction followed by `ρ_{T, S_T H}` is `PF_{T,A}(H, B)`. By lem-kun-0f12
   (`T` qcqs of finite torsion etale dimension, `A` torsion, `B` an arbitrary object of
   `D(A)`) this is invertible. Restriction of scalars is exact and does not change the
   underlying modules (lem-pur-sheaf-ring-derived-coefficient-adjunction), so it
   reflects isomorphisms and `β` is an isomorphism in `D(B)`, natural in `H`.
2. Put `E = K`, `Q_A = RΓ_A(Y, L)`, `Q_B = RΓ_B(Y, S_Y L)`, `N_A = p^*E ⊗ q^*L`,
   `N_B = p^*S_X E ⊗ q^*S_Y L`, `d = (1 ⊗ c_{X,B} β_{Y,L}) τ_{E,Q_A}` and
   `t = Rp_{*,B}(σ_N) σ_{p,N_A}`. The two equations of
   lem-pur-kunneth-mate-scalar-compatibility are `t S_X φ_A = φ_B d` and
   `RΓ_B(W, σ_N) β_{W,N_A} S_0 ℓ_{A,N_A} = ℓ_{B,N_B} RΓ_B(X, t) β_{X, Rp_{*,A} N_A}`,
   with `σ_N = s_W` by the normalization. lem-pur-projection-formula-scalar-compatibility
   gives `RΓ_B(X, τ) β_{X,D_A} S_0 P_A = P_B^0 (β_{X,E} ⊗ 1) s_0`, and
   lem-sf-ring-kunneth-factorization gives `κ_A = ℓ_{A,N_A} RΓ_A(X, φ_A) P_A` and
   `κ_B = ℓ_{B,N_B} RΓ_B(X, φ_B) P_B`.
3. Substitute the factorization of `κ_A` and the Leray equation, use naturality of `β`
   at `φ_A`, then the relative-mate equation and the projection equation. Naturality of
   the counit-defined projection morphism in its constant argument
   (def-kun-constant-projection-morphism) gives
   `RΓ_B(X, 1 ⊗ c_{X,B} β_{Y,L}) P_B^0 = P_B (1 ⊗ β_{Y,L})`; bifunctoriality of the
   tensor product and the factorization of `κ_B` give
   `RΓ_B(W, s_W) β_{W, K ⊠ L} S_0 κ_A = κ_B (β_{X,K} ⊗ β_{Y,L}) s_0`.
No boundedness, constructibility, finite Tor dimension or flatness is used, and no
Kunneth map is asserted invertible. -/
theorem derivedScalarChangeExteriorProduct
    (A B : Type (u + 1)) [CommRing A] [CommRing B]
    (φ : A →+* B) (hA : IsAddTorsion A)
    {k : Type u} [Field k] [IsSepClosed k]
    {X Y : Scheme.{u}} (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k))
    [CompactSpace X] [QuasiSeparatedSpace X]
    [CompactSpace Y] [QuasiSeparatedSpace Y]
    [CompactSpace (pullback f g : Scheme.{u})]
    [QuasiSeparatedSpace (pullback f g : Scheme.{u})]
    (hcdX : X.torsionEtaleCohomologicalDimension < ⊤)
    (hcdY : Y.torsionEtaleCohomologicalDimension < ⊤)
    (hcdW : (pullback f g : Scheme.{u}).torsionEtaleCohomologicalDimension < ⊤) :
    Nonempty (DerivedScalarChangeExteriorProductData A B φ f g) := by
  sorry

end AlgebraicGeometry.Etale
