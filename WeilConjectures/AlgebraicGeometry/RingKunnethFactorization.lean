/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.Algebra.Homology.Additive
public import WeilConjectures.SixFunctors.Etale.Derived.Tensor
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import WeilConjectures.AlgebraicGeometry.KunnethGlobalSections
public import WeilConjectures.AlgebraicGeometry.EtaleConstantProjectionMap
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.AlgebraicGeometry.Sites.PointConstantSheaf
public import WeilConjectures.AlgebraicGeometry.KInjectiveResolutions
public import WeilConjectures.CategoryTheory.KInjectiveTotalDerived
public import WeilConjectures.AlgebraicGeometry.KInjectiveResolutionsExist
import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Comparison
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
import WeilConjectures.SixFunctors.Etale.Derived.UnitCompVanishing
import WeilConjectures.AlgebraicGeometry.DerivedLerayComp
import WeilConjectures.Mathlib.CategoryTheory.Functor.Derived.Adjunction
import WeilConjectures.AlgebraicGeometry.RingKunnethNormalizationData
import WeilConjectures.AlgebraicGeometry.RingKunnethFormalTransport
import WeilConjectures.AlgebraicGeometry.RingKunnethAdjunctionNormalization
import WeilConjectures.AlgebraicGeometry.RingKunnethTensorNormalization

/-!
# Coefficient-independent factorization of the ordinary Künneth map

Source: Stacks Project, Tag 0F1E, `remark-define-kunneth-map`, and the canonical
constant projection and K-injective Leray constructions
(blueprint: lem-sf-ring-kunneth-factorization).

The point comparison and the transported tensor-base-change map below have explicit data.
The final equality imposes no boundedness, finiteness, torsion, or invertibility condition.
-/

@[expose] public section

universe u uA

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace AlgebraicGeometry.Etale

attribute [local implicit_reducible] derivedTensorRightDerivedLowerStar
  rightDerivedLowerStarDerivedTensorLeftDerivedUpperStar

/-- The existing constant projection map, with its target written using `derivedTensor`.
This is a definitional interface, with exactly the data of `constantDerivedProjectionMap`.
Source: Stacks Tags 0F12 and 0F1E (blueprint: lem-sf-ring-kunneth-factorization).
-/
noncomputable def ringKunnethConstantProjection
    (A : Type uA) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [HasSmallSiteSheafify A]
    [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
    [Abelian.HasFunctorialFlatResolution A] (X : Scheme.{u})
    [(constantSheaf X.smallEtaleTopology A).Monoidal]
    [(constantSheaf X.smallEtaleTopology A).PreservesFlat]
    (E : DerivedCategory (Sheaf X.smallEtaleTopology A)) (Q : DerivedCategory A) :
    (rightDerivedGlobalSections A X).obj E ⊗ Q ⟶
      (rightDerivedGlobalSections A X).obj
        (((derivedTensor A X).obj E).obj
          ((constantSheaf X.smallEtaleTopology A).leftDerivedFunctor.obj Q)) :=
  constantDerivedProjectionMap A X E Q

variable (Λ : Type (u + 1)) [CommRing Λ]
  {k : Type u} [Field k] [IsSepClosed k]

private theorem ringKunnethAdjunctionEq {X Y : Scheme.{u}} (f : X ⟶ Y) :
    derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f =
      (mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f).ofNatIsoLeft
        (upperStar (ModuleCat.{u + 1} Λ) f).leftDerivedFunctorIsoMapDerivedCategory.symm := by
  exact ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f).mapHomotopyCategory
    (.up ℤ)).derived_eq_ofNatIsoLeft
      (HomotopyCategory.quasiIso _ (.up ℤ)) (HomotopyCategory.quasiIso _ (.up ℤ))
      (upperStar (ModuleCat.{u + 1} Λ) f).leftDerivedFunctorCounit
      (upperStar (ModuleCat.{u + 1} Λ) f).mapDerivedCategoryFactorsh.hom
      (lowerStar (ModuleCat.{u + 1} Λ) f).rightDerivedFunctorUnit
      (upperStar (ModuleCat.{u + 1} Λ) f).leftDerivedFunctorIsoMapDerivedCategory
      (upperStar (ModuleCat.{u + 1} Λ) f).leftDerivedFunctorIsoMapDerivedCategory_hom_fac.symm

private theorem ringKunnethCompositorEq {X Y Z : Scheme.{u}} (f : Y ⟶ X) (g : Z ⟶ Y) :
    (rightDerivedLowerStarCompIsoOfComp (ModuleCat.{u + 1} Λ) g f (g ≫ f) rfl).hom =
      (rightDerivedLowerStarComp (ModuleCat.{u + 1} Λ) g f).hom := by
  ext M
  simp only [rightDerivedLowerStarCompIsoOfComp, conjugateIsoEquiv_apply_hom,
    rightDerivedLowerStarComp, Iso.symm_hom, conjugateIsoEquiv_apply_inv, Iso.symm_inv]
  rw [ringKunnethAdjunctionEq, ringKunnethAdjunctionEq, ringKunnethAdjunctionEq]
  simp [conjugateEquiv_apply_app, Adjunction.ofNatIsoLeft_unit,
    Adjunction.ofNatIsoLeft_counit, Adjunction.comp_counit_app,
    leftDerivedUpperStarComp, Functor.leftDerivedFunctorNatIso,
    Functor.leftDerivedFunctorCompIso, Category.assoc, ← Functor.map_comp]
  simp only [← Functor.map_comp, ← Category.assoc, Iso.inv_hom_id_app, Category.id_comp]

/-- The canonical identification of `a⁻¹ Rb_* K` with the constant complex on `RΓ(Y,K)`.
Use the inverse derived point counit, exact global sections at the point, Leray for `b`,
and pullback of constants; the last comparison identifies exact and derived constants.
Source: Stacks Tag 0F1E and the separably closed point equivalence
(blueprint: lem-sf-ring-kunneth-factorization).
-/
noncomputable def ringKunnethPointPullbackIso
    {X Y : Scheme.{u}} (a : X ⟶ Spec (.of k)) (b : Y ⟶ Spec (.of k))
    (K : DerivedCategoryModule Λ Y) :
    (upperStar (ModuleCat.{u + 1} Λ) a).leftDerivedFunctor.obj
        ((lowerStar (ModuleCat.{u + 1} Λ) b).rightDerivedFunctor.obj K) ≅
      (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).leftDerivedFunctor.obj
        ((rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) Y).obj K) :=
  let F := constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)
  let P := constantSheafEquivalenceOfIsSepClosed Λ (k := k)
  letI : P.functor.Additive := additive_constantSheaf Λ _
  letI : P.inverse.Additive := additive_sheafSections_obj Λ _
  let C := (lowerStar (ModuleCat.{u + 1} Λ) b).rightDerivedFunctor.obj K
  let c : C ≅ (constantFunctor Λ (Spec (.of k))).obj
      ((rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) Y).obj K) :=
    (P.mapDerivedCategory.counitIso.app C).symm ≪≫
      (constantFunctor Λ _).mapIso ((rightDerivedGlobalSectionsIsoOfIsSepClosed Λ).app C).symm ≪≫
      (constantFunctor Λ _).mapIso
        ((rightDerivedLowerStarCompRightDerivedGlobalSectionsIso
          (ModuleCat.{u + 1} Λ) b).app K)
  (upperStar (ModuleCat.{u + 1} Λ) a).leftDerivedFunctor.mapIso c ≪≫
    (constantFunctorCompLeftDerivedUpperStarIso Λ a).app _ ≪≫
    (F.leftDerivedFunctorIsoMapDerivedCategory.app _).symm

/-- The relative tensor-base-change map with identity left square, transported by the
specified point identification. Its adjunct is the canonical pullback tensor comparison
followed by `1 ⊗ q⁻¹ ε_b`; neither this map nor the projection map is inverted.
Source: Stacks Tag 0F1E and the map of Tag 0F1N
(blueprint: lem-sf-ring-kunneth-factorization).
-/
noncomputable def ringKunnethTensorBaseChange
    {X Y : Scheme.{u}} (a : X ⟶ Spec (.of k)) (b : Y ⟶ Spec (.of k))
    (E : DerivedCategoryModule Λ X) (K : DerivedCategoryModule Λ Y) :
    ((derivedTensor (ModuleCat.{u + 1} Λ) X).obj E).obj
        ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).leftDerivedFunctor.obj
          ((rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) Y).obj K)) ⟶
      (lowerStar (ModuleCat.{u + 1} Λ) (pullback.fst a b)).rightDerivedFunctor.obj
        (((derivedTensor (ModuleCat.{u + 1} Λ) (pullback a b)).obj
          ((upperStar (ModuleCat.{u + 1} Λ) (pullback.fst a b)).leftDerivedFunctor.obj E)).obj
          ((upperStar (ModuleCat.{u + 1} Λ) (pullback.snd a b)).leftDerivedFunctor.obj K)) :=
  ((derivedTensor (ModuleCat.{u + 1} Λ) X).obj E).map
      (ringKunnethPointPullbackIso Λ a b K).inv ≫
    tensorBaseChangeMap (ModuleCat.{u + 1} Λ) (pullback.fst a b) (pullback.snd a b)
      a b pullback.condition E K

set_option maxHeartbeats 1000000 in
-- The point counit and exact/derived comparisons have large reducible data.
/-- Transport the point Künneth tensor and projection component to the constant projection map.
Source: Stacks Tag 0F1E (blueprint: lem-sf-ring-kunneth-factorization).
-/
private theorem ringKunnethProjectionTransport
    {X Y : Scheme.{u}} (a : X ⟶ Spec (.of k)) (b : Y ⟶ Spec (.of k))
    (E : DerivedCategoryModule Λ X) (K : DerivedCategoryModule Λ Y) :
    ((rightDerivedLowerStarCompRightDerivedGlobalSectionsIso
        (ModuleCat.{u + 1} Λ) a).inv.app E ⊗ₘ
      (rightDerivedLowerStarCompRightDerivedGlobalSectionsIso
        (ModuleCat.{u + 1} Λ) b).inv.app K) ≫
      (pointGlobalSectionsTensorIso Λ
        ((a)_*[ModuleCat.{u + 1} Λ].rightDerivedFunctor.obj E)
        ((b)_*[ModuleCat.{u + 1} Λ].rightDerivedFunctor.obj K)).hom ≫
      (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) (Spec (.of k))).map
        (((rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} Λ) a).app E).app
          ((b)_*[ModuleCat.{u + 1} Λ].rightDerivedFunctor.obj K)) =
    ringKunnethConstantProjection (ModuleCat.{u + 1} Λ) X E
        ((rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) Y).obj K) ≫
      (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) X).map
        (((derivedTensor (ModuleCat.{u + 1} Λ) X).obj E).map
          (ringKunnethPointPullbackIso Λ a b K).inv) ≫
      (rightDerivedLowerStarCompRightDerivedGlobalSectionsIso
        (ModuleCat.{u + 1} Λ) a).inv.app _ := by
  rw [ringKunnethPointTensorTranspose]
  let C := (lowerStar (ModuleCat.{u + 1} Λ) b).rightDerivedFunctor.obj K
  let R := rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) (Spec (.of k))
  let H := (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).leftDerivedFunctor
  let L := (upperStar (ModuleCat.{u + 1} Λ) a).leftDerivedFunctor
  let q := (rightDerivedLowerStarCompRightDerivedGlobalSectionsIso
    (ModuleCat.{u + 1} Λ) b).app K
  have ht : H.map q.inv ≫ (ringKunnethConstantComparison Λ a).hom.app (R.obj C) ≫
      L.map ((ringKunnethPointAdjunction Λ).counit.app C) =
      (ringKunnethPointPullbackIso Λ a b K).inv := by
    rw [reassoc_of% (ringKunnethConstantComparison Λ a).hom.naturality q.inv]
    simp [ringKunnethConstantComparison, ringKunnethPointAdjunction,
      ringKunnethPointPullbackIso, Adjunction.ofNatIsoRight_counit,
      q, H, L, R, C, Functor.map_comp, Category.assoc]
  have h := Adjunction.ringKunnethProjectionTransportFormal
    (ringKunnethPointAdjunction Λ)
    (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) a)
    (derivedConstantGlobalSectionsAdjunction (ModuleCat.{u + 1} Λ) X)
    (ringKunnethConstantComparison Λ a)
    (rightDerivedLowerStarCompRightDerivedGlobalSectionsIso (ModuleCat.{u + 1} Λ) a)
    (ringKunnethPointTensorComparison Λ)
    (leftDerivedUpperStarTensorComparison (ModuleCat.{u + 1} Λ) a)
    (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).cachedDerivedTensorComparison
    (ringKunnethAdjunctionNormalization Λ a) (ringKunnethTensorNormalization Λ a)
    E C _ q
  rw [ht] at h
  simpa only [ringKunnethConstantProjection, constantDerivedProjectionMap,
    rightDerivedLowerStarProjectionMap, MonoidalCategory.tensorHom_def, id_whiskerRight,
    Category.id_comp, C, q, Functor.comp_obj, Functor.id_obj, Iso.app_inv,
    derivedTensor, curriedTensor_obj_obj, curriedTensor_map_app, curriedTensor_obj_map,
    rightDerivedLowerStarDerivedTensorLeftDerivedUpperStar, Category.assoc] using h

omit [IsSepClosed k] in
/-- The normalized Leray comparison is compatible with the composition comparison for
`R a_* R p_*` and `R (p ≫ a)_*`.
Source: Stacks Tags 08BJ and 09T5 (blueprint: lem-sf-ring-kunneth-factorization).
-/
private theorem ringKunnethLerayCompatibility
    {X Y : Scheme.{u}} (a : X ⟶ Spec (.of k)) (b : Y ⟶ Spec (.of k))
    (E : DerivedCategoryModule Λ X) (K : DerivedCategoryModule Λ Y) :
    (rightDerivedLowerStarCompRightDerivedGlobalSectionsIso
        (ModuleCat.{u + 1} Λ) a).inv.app _ ≫
      (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) (Spec (.of k))).map
        ((a)_*[ModuleCat.{u + 1} Λ].rightDerivedFunctor.map
          (tensorBaseChangeMap (ModuleCat.{u + 1} Λ) (pullback.fst a b)
            (pullback.snd a b) a b pullback.condition E K)) ≫
      (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) (Spec (.of k))).map
        ((rightDerivedLowerStarCompIsoOfComp (ModuleCat.{u + 1} Λ)
          (pullback.fst a b) a (pullback.fst a b ≫ a) rfl).hom.app _) ≫
      (rightDerivedLowerStarCompRightDerivedGlobalSectionsIso
        (ModuleCat.{u + 1} Λ) (pullback.fst a b ≫ a)).hom.app _ =
    (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) X).map
        (tensorBaseChangeMap (ModuleCat.{u + 1} Λ) (pullback.fst a b)
          (pullback.snd a b) a b pullback.condition E K) ≫
      (rightDerivedLowerStarCompRightDerivedGlobalSectionsIso
        (ModuleCat.{u + 1} Λ) (pullback.fst a b)).hom.app _ := by
  rw [rightDerivedGlobalSections_map_rightDerivedLowerStar_map]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc]
  rw [ringKunnethCompositorEq, derivedLeray_comp]
  simp only [Iso.inv_hom_id_app_assoc]

/-- The counit-defined Künneth morphism factors through the constant projection map,
derived global sections of the transported tensor-base-change map, and canonical Leray.
Source: Stacks Tag 0F1E, `remark-define-kunneth-map`
(blueprint: lem-sf-ring-kunneth-factorization).

Proof: Expand the native Künneth map using its proved projection/base-change factorization.
The explicit point tensor is the adjunct of the tensor of point counits. Normalize the
constant/pullback tensor and adjunction comparisons, then apply the proved formal
projection-transport calculation. Naturality identifies its second-factor transport with
the inverse of ringKunnethPointPullbackIso. Exact-left-adjoint normalization identifies
the two native direct-image compositors. The proved general-coefficient Leray composition
identity and naturality then collapse the remaining compositor/Leray factors. Functoriality
combines the inverse point comparison and tensor base change into the displayed map.
No inverse of φ or of the constant projection map is used in any step.
-/
theorem ringKunnethFactorization
    {X Y : Scheme.{u}} (a : X ⟶ Spec (.of k)) (b : Y ⟶ Spec (.of k))
    (E : DerivedCategoryModule Λ X) (K : DerivedCategoryModule Λ Y) :
    kunnethGlobalSectionsMap Λ (pullback.fst a b) (pullback.snd a b)
        a b pullback.condition.symm E K =
      ringKunnethConstantProjection (ModuleCat.{u + 1} Λ) X E
          ((rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) Y).obj K) ≫
        (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) X).map
          (ringKunnethTensorBaseChange Λ a b E K) ≫
        (rightDerivedLowerStarCompRightDerivedGlobalSectionsIso
          (ModuleCat.{u + 1} Λ) (pullback.fst a b)).hom.app _   := by
  unfold kunnethGlobalSectionsMap
  rw [kunnethMap_eq]
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% ringKunnethProjectionTransport Λ a b E K]
  erw [ringKunnethLerayCompatibility Λ a b E K]
  simp [ringKunnethTensorBaseChange, Functor.map_comp, Category.assoc]

end AlgebraicGeometry.Etale
