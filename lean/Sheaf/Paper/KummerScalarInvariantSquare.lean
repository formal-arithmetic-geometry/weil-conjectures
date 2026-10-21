/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Sheaf.Paper.KummerInvariantScalarMap
public import Sheaf.Paper.KummerLocalSource

/-! # The actual scalar arrow on derived invariants
Source: direct-image proof (3), scalar restriction and the insertion-of-one arrow.
(blueprint: def-sfb-kummer-scalar-invariant-square).
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory Limits Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.CondensedRing
open CategoryTheory.CondensedBar
/-- The coefficient square with the actual tensor unit and exact derived restriction.
All source objects and comparison maps are fixed before the equation is formed.
Source: direct-image proof (3), simultaneous coefficient compatibility
(blueprint: def-sfb-kummer-scalar-invariant-square). -/
def KummerCoefficientSquare (ℓ : ℕ) [Fact ℓ.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ℓ) {W Y S : Scheme.{u}}
    (a : W ⟶ Y) (s : S ⟶ Y)
    (L : KummerModules (kummerCoefficientRing.{u} E.1).X W)
    (ME : DerivedCategory (KummerModules (kummerCoefficientRing.{u} E.1).X S))
    (MO : DerivedCategory (KummerModules (kummerCoefficientRing.{u} (PadicAlgCl ℓ)).X S))
    (eE : kummerOpenImage (kummerCoefficientRing.{u} E.1).X a s L ≅ ME)
    (eO : kummerOpenImage (kummerCoefficientRing.{u} (PadicAlgCl ℓ)).X a s
      (kummerOmegaModuleForRing ℓ E W L) ≅ MO)
    (r : ME ⟶ (kummerDerivedRestriction ℓ E S).obj MO) : Prop :=
  kummerSourceScalarMap ℓ E a s L ≫ (kummerDerivedRestriction ℓ E S).map eO.hom =
    eE.hom ≫ r

variable (A A' : Ring.{u}) (a : A ⟶ A')
  (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
  [ActionAbelian A G] [ActionAbelian A' G]
  [IsGrothendieckAbelian.{u + 1} (Equivariant A G)]
  [IsGrothendieckAbelian.{u + 1} (Equivariant A' G)]
  [HasDerivedCategory.{u + 2} (Equivariant A G)]
  [HasDerivedCategory.{u + 2} (Equivariant A' G)]
  [HasDerivedCategory.{u + 2} (Modules A)]
  [HasDerivedCategory.{u + 2} (Modules A')]

/-- Actual exact restriction on the stratum's module-derived category.
Source: direct-image proof (3), scalar restriction
(blueprint: def-sfb-kummer-scalar-invariant-square). -/
def kummerScalarDerivedRestriction (S : Scheme.{u}) :
    DerivedCategory (KummerModules A'.X S) ⥤ DerivedCategory (KummerModules A.X S) :=
  (Mod.comap (coefficientMap a.hom.hom S)).mapDerivedCategory

/-- The published invariant scalar chain after the canonical point comparison.
Source: direct-image proof (3), scalar restriction on the internal bar
(blueprint: def-sfb-kummer-scalar-invariant-square). -/
def kummerScalarInvariantChain (BE : Model A G) (BO : Model A' G)
    (b : ScalarModel a BE BO) (S : Scheme.{u})
    (JO : CochainComplex (Equivariant A' G) ℕ)
    (K : CochainComplex (Equivariant A G) ℕ)
    (β : (b.restriction.functor.mapHomologicalComplex (.up ℕ)).obj JO ⟶ K) :
    ((Mod.comap (coefficientMap a.hom.hom S)).mapHomologicalComplex (.up ℕ)).obj
      (kummerInvariantComplex A' G BO S JO) ⟶ kummerInvariantComplex A G BE S K := by
  let CΩ : CochainComplex (Modules A') ℕ :=
    (BO.invariants.functor.mapHomologicalComplex (.up ℕ)).obj JO
  let CE : CochainComplex (Modules A) ℕ :=
    (BE.invariants.functor.mapHomologicalComplex (.up ℕ)).obj K
  let γ : ((Mod.comap a.hom.hom).mapHomologicalComplex (.up ℕ)).obj CΩ ⟶ CE :=
    scalarInvariantChain a b JO K β
  let δ : ((Mod.comap (coefficientMap a.hom.hom S)).mapHomologicalComplex (.up ℕ)).obj
      (kummerInvariantComplex A' G BO S JO) ⟶
      (((upperStarFromPoint S).mapMod A.X).mapHomologicalComplex (.up ℕ)).obj
        (((Mod.comap a.hom.hom).mapHomologicalComplex (.up ℕ)).obj CΩ) :=
    (NatIso.mapHomologicalComplex
      ((upperStarFromPoint S).mapModComapIso a.hom.hom) (.up ℕ)).inv.app CΩ
  exact δ ≫ (((upperStarFromPoint S).mapMod A.X).mapHomologicalComplex (.up ℕ)).map γ

/-- The point-pulled invariant lift on actual resolution complexes.
Source: direct-image proof (3), invariant lift normalization
(blueprint: def-sfb-kummer-scalar-invariant-square). -/
def kummerInvariantLiftMap (B : Model A G) (S : Scheme.{u})
    (J K : CochainComplex (Equivariant A G) ℕ) (β : J ⟶ K) :
    DerivedCategory.Q.obj ((kummerInvariantComplex A G B S J).extend
      ComplexShape.embeddingUpNat) ⟶
      DerivedCategory.Q.obj ((kummerInvariantComplex A G B S K).extend
        ComplexShape.embeddingUpNat) :=
  DerivedCategory.Q.map (HomologicalComplex.extendMap
    ((((upperStarFromPoint S).mapMod A.X).mapHomologicalComplex (.up ℕ)).map
      ((B.invariants.functor.mapHomologicalComplex (.up ℕ)).map β))
    ComplexShape.embeddingUpNat)

/-- The scalar resolution map after the exact restriction comparison.
Source: direct-image proof (3), right-hand coefficient normalization
(blueprint: def-sfb-kummer-scalar-invariant-square). -/
def kummerScalarResolutionMap (BE : Model A G) (BO : Model A' G)
    (b : ScalarModel a BE BO) (S : Scheme.{u})
    (JO : CochainComplex (Equivariant A' G) ℕ)
    (K : CochainComplex (Equivariant A G) ℕ)
    (β : (b.restriction.functor.mapHomologicalComplex (.up ℕ)).obj JO ⟶ K) :
    (kummerScalarDerivedRestriction A A' a S).obj
      (DerivedCategory.Q.obj ((kummerInvariantComplex A' G BO S JO).extend
        ComplexShape.embeddingUpNat)) ⟶
      DerivedCategory.Q.obj ((kummerInvariantComplex A G BE S K).extend
        ComplexShape.embeddingUpNat) :=
  ((Mod.comap (coefficientMap a.hom.hom S)).mapDerivedCategoryFactors.app
    ((kummerInvariantComplex A' G BO S JO).extend ComplexShape.embeddingUpNat)).hom ≫
    DerivedCategory.Q.map
      ((HomologicalComplex.mapExtendIso (kummerInvariantComplex A' G BO S JO)
        ComplexShape.embeddingUpNat (Mod.comap (coefficientMap a.hom.hom S))).hom ≫
      HomologicalComplex.extendMap (kummerScalarInvariantChain A A' a G BE BO b S JO K β)
        ComplexShape.embeddingUpNat)

/-- The scalar arrow is fixed by actual resolution augmentations and the published
scalar-invariant chain. It is the arrow induced by c after ordinary derived invariants.
Source: direct-image proof (3), right-hand coefficient map
(blueprint: def-sfb-kummer-scalar-invariant-square). -/
structure KummerInvariantScalarArrow (BE : Model A G) (BO : Model A' G)
    (b : ScalarModel a BE BO) (S : Scheme.{u})
    (NE : Equivariant A G) (NO : Equivariant A' G)
    (c : NE ⟶ b.restriction.functor.obj NO)
    (JE : InjectiveResolution NE) (JO : InjectiveResolution NO) where
  restrictedResolution : InjectiveResolution (b.restriction.functor.obj NO)
  unitLift : JE.cocomplex ⟶ restrictedResolution.cocomplex
  unitLift_normalized : JE.ι.f 0 ≫ unitLift.f 0 = c ≫ restrictedResolution.ι.f 0
  scalarLift : (b.restriction.functor.mapHomologicalComplex (.up ℕ)).obj JO.cocomplex ⟶
    restrictedResolution.cocomplex
  scalarLift_normalized : b.restriction.functor.map (JO.ι.f 0) ≫ scalarLift.f 0 =
    restrictedResolution.ι.f 0
  scalarLift_quasiIso : QuasiIso
    (kummerScalarInvariantChain A A' a G BE BO b S JO.cocomplex
      restrictedResolution.cocomplex scalarLift)
  arrow : kummerInvariantObject A G BE S NE ⟶
    (kummerScalarDerivedRestriction A A' a S).obj (kummerInvariantObject A' G BO S NO)
  normalization :
    (kummerInvariantResolutionIso A G BE S JE).hom ≫
      kummerInvariantLiftMap A G BE S JE.cocomplex restrictedResolution.cocomplex unitLift =
    arrow ≫ (kummerScalarDerivedRestriction A A' a S).map
      (kummerInvariantResolutionIso A' G BO S JO).hom ≫
      kummerScalarResolutionMap A A' a G BE BO b S JO.cocomplex
        restrictedResolution.cocomplex scalarLift

end AlgebraicGeometry.ProEtale.CondensedRing
