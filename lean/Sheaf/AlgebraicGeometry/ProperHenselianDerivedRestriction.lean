module

public import WeilConjectures.Mathlib.RingTheory.Henselian
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Pullbacks
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import WeilConjectures.AlgebraicGeometry.EtaleInverseImageExact
public import WeilConjectures.CategoryTheory.KInjectiveBridge
public import Sheaf.AlgebraicGeometry.ModuleDerivedCohomologyPullback

import WeilConjectures.AlgebraicGeometry.DerivedUnitClassicalPullbackCoherence
import WeilConjectures.AlgebraicGeometry.AbelianDerivedGlobalExtPullback
import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper
import Sheaf.CategoryTheory.HeartTestBoundedBelow
import Sheaf.AlgebraicGeometry.QcqsHigherImagesPrimeTorsion
import WeilConjectures.AlgebraicGeometry.TorsionSheafCharacterizations

/-! # Derived restriction to the closed fibre of a proper henselian scheme

Source: Stacks Project, Tags 09ZI, 0DDE and 0DDD
(blueprint: lem-per-proper-henselian-derived-restriction).

The restriction map is the published canonical derived cohomological pullback.
The auxiliary constructions specify the induced fibre map and its coefficient map.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- The canonical map of closed fibres induced by a morphism of pairs and a compatible
scheme map. It is constructed by the universal property of the scheme fibre product.
Source: Stacks, Tags 01JO and 01F8
(blueprint: lem-per-proper-henselian-derived-restriction). -/
def henselianClosedFibreMap
    {A B : Type u} [CommRing A] [CommRing B] (I : Ideal A) (J : Ideal B)
    (φ : A →+* B) (hIJ : I ≤ J.comap φ)
    {Y V : Scheme.{u}} (f : Y ⟶ Spec (.of A)) (g : V ⟶ Spec (.of B))
    (h : V ⟶ Y) (hh : h ≫ f = g ≫ Spec.map (CommRingCat.ofHom φ)) :
    pullback g (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) ⟶
      pullback f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) :=
  pullback.map g (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))
    f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))
    h (Spec.map (CommRingCat.ofHom (Ideal.quotientMap J φ hIJ)))
    (Spec.map (CommRingCat.ofHom φ)) hh.symm
    ((Spec.map_comp (CommRingCat.ofHom φ)
        (CommRingCat.ofHom (Ideal.Quotient.mk J))).symm.trans
      ((congrArg (fun ψ : A →+* B ⧸ J ↦ Spec.map (CommRingCat.ofHom ψ))
        (Ideal.quotientMap_comp_mk hIJ).symm).trans
          (Spec.map_comp (CommRingCat.ofHom (Ideal.Quotient.mk I))
            (CommRingCat.ofHom (Ideal.quotientMap J φ hIJ)))))

/-- The canonical identification of the two iterated inverse images in a commutative
square, obtained by deriving the ordinary inverse-image compositors.
Source: Stacks, Tags 01F8 and 015M
(blueprint: lem-per-proper-henselian-derived-restriction). -/
def abelianDerivedSquareInverseImageIso
    {Y V Y₀ V₀ : Scheme.{u}} (i : Y₀ ⟶ Y) (j : V₀ ⟶ V)
    (h : V ⟶ Y) (h₀ : V₀ ⟶ Y₀) (w : h₀ ≫ i = j ≫ h) :
    (upperStar AddCommGrpCat.{u + 1} i).mapDerivedCategoryPlus ⋙
        (upperStar AddCommGrpCat.{u + 1} h₀).mapDerivedCategoryPlus ≅
      (upperStar AddCommGrpCat.{u + 1} h).mapDerivedCategoryPlus ⋙
        (upperStar AddCommGrpCat.{u + 1} j).mapDerivedCategoryPlus :=
  (Functor.mapDerivedCategoryPlusCompIso
    (upperStar AddCommGrpCat.{u + 1} i) (upperStar AddCommGrpCat.{u + 1} h₀)).symm ≪≫
  Functor.mapDerivedCategoryPlusNatIso
    ((upperStarComp AddCommGrpCat.{u + 1} h₀ i (j ≫ h) w.symm).symm ≪≫
      upperStarComp AddCommGrpCat.{u + 1} j h) ≪≫
  Functor.mapDerivedCategoryPlusCompIso
    (upperStar AddCommGrpCat.{u + 1} h) (upperStar AddCommGrpCat.{u + 1} j)

/-- The coefficient map on closed fibres, with the canonical inverse-image identification.
Source: Stacks, Tags 01F8 and 015M
(blueprint: lem-per-proper-henselian-derived-restriction). -/
def abelianDerivedSquareCoefficientMap
    {Y V Y₀ V₀ : Scheme.{u}} (i : Y₀ ⟶ Y) (j : V₀ ⟶ V)
    (h : V ⟶ Y) (h₀ : V₀ ⟶ Y₀) (w : h₀ ≫ i = j ≫ h)
    (K : _root_.DerivedCategory.Plus (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}))
    (L : _root_.DerivedCategory.Plus (Sheaf V.smallEtaleTopology AddCommGrpCat.{u + 1}))
    (a : (upperStar AddCommGrpCat.{u + 1} h).mapDerivedCategoryPlus.obj K ⟶ L) :
    (upperStar AddCommGrpCat.{u + 1} h₀).mapDerivedCategoryPlus.obj
        ((upperStar AddCommGrpCat.{u + 1} i).mapDerivedCategoryPlus.obj K) ⟶
      (upperStar AddCommGrpCat.{u + 1} j).mapDerivedCategoryPlus.obj L :=
  (abelianDerivedSquareInverseImageIso i j h h₀ w).hom.app K ≫
    (upperStar AddCommGrpCat.{u + 1} j).mapDerivedCategoryPlus.map a

private theorem lowerStarCompGlobalSectionsIso_comp_comp
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (P : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    (Sheaf.Γ Z.smallEtaleTopology AddCommGrpCat.{u + 1}).map
        ((lowerStarComp AddCommGrpCat.{u + 1} f g (f ≫ g) rfl).hom.app P) ≫
      (lowerStarCompGlobalSectionsIso AddCommGrpCat.{u + 1} (f ≫ g)).hom.app P =
    (lowerStarCompGlobalSectionsIso AddCommGrpCat.{u + 1} g).hom.app
        (((f)_*[AddCommGrpCat.{u + 1}]).obj P) ≫
      (lowerStarCompGlobalSectionsIso AddCommGrpCat.{u + 1} f).hom.app P := by
  apply (cancel_mono ((Sheaf.ΓNatIsoSheafSections _ _ terminalIsTerminal).hom.app P)).1
  simp only [lowerStarCompGlobalSectionsIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Category.assoc,
    Iso.inv_hom_id_app, Iso.inv_hom_id_app_assoc, Category.comp_id]
  rw [reassoc_of% ((Sheaf.ΓNatIsoSheafSections Z.smallEtaleTopology
    AddCommGrpCat.{u + 1} terminalIsTerminal).hom.naturality
    ((lowerStarComp AddCommGrpCat.{u + 1} f g (f ≫ g) rfl).hom.app P))]
  simp only [lowerStarCompSheafSectionsTerminalIso, NatIso.ofComponents_hom_app,
    Functor.mapIso_hom, Iso.symm_hom, Iso.op_inv]
  congr 1
  change ((lowerStarComp AddCommGrpCat.{u + 1} f g (f ≫ g) rfl).hom.app P).hom.app
    (Opposite.op (⊤_ Z.Etale)) ≫ P.obj.map (PreservesTerminal.iso (f ≫ g).Etale).inv.op = _
  simp only [lowerStarComp, Functor.sheafPushforwardContinuousComp'_hom_app_hom_app,
    Iso.symm_inv, lowerStar_obj_val_map, ← Functor.map_comp, ← op_comp]
  congr 2
  exact ((terminalIsTerminal.isTerminalObj g.Etale).isTerminalObj f.Etale).hom_ext _ _

private lemma pullback_eq {X Y : Scheme.{u}} (f : Y ⟶ X)
    (K : _root_.DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})) :
    abelianDerivedCohomologyPullback f K = etaleDerivedRestriction f K := by
  unfold abelianDerivedCohomologyPullback etaleDerivedRestriction
  exact derivedCohomologyPullback_eq_derivedUnit f K

private lemma restriction_naturality {X Y : Scheme.{u}} (f : Y ⟶ X)
    {K L : _root_.DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})}
    (a : K ⟶ L) :
    (Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{u + 1}).rightDerivedFunctorPlus.map a ≫
        etaleDerivedRestriction f L = etaleDerivedRestriction f K ≫
      (Sheaf.Γ Y.smallEtaleTopology AddCommGrpCat.{u + 1}).rightDerivedFunctorPlus.map
        ((upperStar AddCommGrpCat.{u + 1} f).mapDerivedCategoryPlus.map a) := by
  simp only [← pullback_eq]
  unfold abelianDerivedCohomologyPullback
  exact NatTrans.naturality _ a

private instance lowerStarPreservesInjectives {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (lowerStar AddCommGrpCat.{u + 1} f).PreservesInjectiveObjects :=
  Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f)

private lemma leray_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (K : _root_.DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})) :
    (Sheaf.Γ Z.smallEtaleTopology AddCommGrpCat.{u + 1}).rightDerivedFunctorPlus.map
        ((Functor.rightDerivedFunctorPlusCompIso'
          (lowerStar AddCommGrpCat.{u + 1} f) (lowerStar AddCommGrpCat.{u + 1} g)
          (lowerStarComp AddCommGrpCat.{u + 1} f g)).hom.app K) ≫
      (etaleLerayPlus (f ≫ g)).hom.app K =
    (etaleLerayPlus g).hom.app
        ((lowerStar AddCommGrpCat.{u + 1} f).rightDerivedFunctorPlus.obj K) ≫
      (etaleLerayPlus f).hom.app K := by
  exact NatTrans.congr_app
    (Functor.rightDerivedFunctorPlusCompIso'_assoc
      (lowerStar AddCommGrpCat.{u + 1} f) (lowerStar AddCommGrpCat.{u + 1} g)
      (Sheaf.Γ Z.smallEtaleTopology AddCommGrpCat.{u + 1})
      (lowerStar AddCommGrpCat.{u + 1} (f ≫ g))
      (Sheaf.Γ Y.smallEtaleTopology AddCommGrpCat.{u + 1})
      (Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{u + 1})
      (lowerStarComp AddCommGrpCat.{u + 1} f g)
      (lowerStarCompGlobalSectionsIso AddCommGrpCat.{u + 1} g)
      (lowerStarCompGlobalSectionsIso AddCommGrpCat.{u + 1} (f ≫ g))
      (lowerStarCompGlobalSectionsIso AddCommGrpCat.{u + 1} f)
      (by
        apply NatTrans.ext
        funext P
        exact lowerStarCompGlobalSectionsIso_comp_comp f g P)) K

private lemma restriction_comp {X Y Z : Scheme.{u}} (f : Y ⟶ X) (g : Z ⟶ Y)
    (K : _root_.DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})) :
    etaleDerivedRestriction (g ≫ f) K ≫
      (Sheaf.Γ Z.smallEtaleTopology AddCommGrpCat.{u + 1}).rightDerivedFunctorPlus.map
        ((upperStarCompDerivedPlus AddCommGrpCat.{u + 1} g f).hom.app K) =
    etaleDerivedRestriction f K ≫
      etaleDerivedRestriction g
        ((upperStar AddCommGrpCat.{u + 1} f).mapDerivedCategoryPlus.obj K) := by
  let C := upperStarCompDerivedPlus AddCommGrpCat.{u + 1} g f
  let G := (Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{u + 1}).rightDerivedFunctorPlus
  have hn := (etaleLerayPlus (g ≫ f)).hom.naturality (C.hom.app K)
  dsimp only [Functor.comp_map] at hn
  have hu := congrArg G.map
    (derivedPlus_unit_comp_upperStarCompDerivedPlus AddCommGrpCat.{u + 1} g f (Z := K))
  have hl := leray_comp g f
    ((upperStar AddCommGrpCat.{u + 1} g).mapDerivedCategoryPlus.obj
      ((upperStar AddCommGrpCat.{u + 1} f).mapDerivedCategoryPlus.obj K))
  have ht := (etaleLerayPlus f).hom.naturality
    ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} g).derivedPlus.unit.app
      ((upperStar AddCommGrpCat.{u + 1} f).mapDerivedCategoryPlus.obj K))
  dsimp only [Functor.comp_map] at ht
  unfold etaleDerivedRestriction
  rw [Category.assoc, ← hn, ← G.map_comp_assoc, hu]
  simp only [Functor.map_comp, Category.assoc]
  erw [hl]
  erw [reassoc_of% ht]

private lemma derived_iso_comp
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    {F G H : C ⥤ D} [F.Additive] [G.Additive] [H.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    (e : F ≅ G) (d : G ≅ H) :
    Functor.mapDerivedCategoryPlusNatIso (e ≪≫ d) =
      Functor.mapDerivedCategoryPlusNatIso e ≪≫ Functor.mapDerivedCategoryPlusNatIso d := by
  apply Iso.ext
  apply Localization.natTrans_ext DerivedCategory.Plus.Qh (HomotopyCategory.Plus.quasiIso C)
  intro N
  apply (cancel_mono (H.mapDerivedCategoryPlusFactorsh.hom.app N)).1
  simp only [Iso.trans_hom, NatTrans.comp_app, Category.assoc,
    Functor.mapDerivedCategoryPlusNatIso_hom_app_factorsh]
  rw [Functor.mapDerivedCategoryPlusNatIso_hom_app_factorsh_assoc]
  simp only [NatTrans.mapHomotopyCategoryPlus_comp, NatTrans.comp_app, Functor.map_comp]

private lemma derived_iso_symm
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    {F G : C ⥤ D} [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (e : F ≅ G) :
    Functor.mapDerivedCategoryPlusNatIso e.symm =
      (Functor.mapDerivedCategoryPlusNatIso e).symm := by
  apply Iso.ext
  apply Localization.natTrans_ext DerivedCategory.Plus.Qh (HomotopyCategory.Plus.quasiIso C)
  intro N
  simp only [Iso.symm_hom]
  apply (cancel_epi ((Functor.mapDerivedCategoryPlusNatIso e).hom.app
    (DerivedCategory.Plus.Qh.obj N))).1
  rw [Iso.hom_inv_id_app]
  apply (cancel_mono (F.mapDerivedCategoryPlusFactorsh.hom.app N)).1
  rw [Category.assoc, Functor.mapDerivedCategoryPlusNatIso_hom_app_factorsh,
    Functor.mapDerivedCategoryPlusNatIso_hom_app_factorsh_assoc]
  simp only [← Functor.map_comp, ← NatTrans.comp_app,
    ← NatTrans.mapHomotopyCategoryPlus_comp, Iso.symm_hom, Iso.hom_inv_id,
    NatTrans.mapHomotopyCategoryPlus_id, NatTrans.id_app, CategoryTheory.Functor.map_id,
    Category.comp_id, Category.id_comp]

private lemma square_iso_eq
    {Y V Y₀ V₀ : Scheme.{u}} (i : Y₀ ⟶ Y) (j : V₀ ⟶ V)
    (h : V ⟶ Y) (h₀ : V₀ ⟶ Y₀) (w : h₀ ≫ i = j ≫ h) :
    abelianDerivedSquareInverseImageIso i j h h₀ w =
      (upperStarCompDerivedPlus AddCommGrpCat.{u + 1} h₀ i (j ≫ h) w.symm).symm ≪≫
        upperStarCompDerivedPlus AddCommGrpCat.{u + 1} j h := by
  unfold abelianDerivedSquareInverseImageIso upperStarCompDerivedPlus
  rw [derived_iso_comp, derived_iso_symm]
  simp only [Iso.trans_symm, Iso.trans_assoc]

private lemma restriction_comp_of_eq {X Y Z : Scheme.{u}} (f : Y ⟶ X) (g : Z ⟶ Y)
    (gf : Z ⟶ X) (w : gf = g ≫ f)
    (K : _root_.DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})) :
    etaleDerivedRestriction gf K ≫
      (Sheaf.Γ Z.smallEtaleTopology AddCommGrpCat.{u + 1}).rightDerivedFunctorPlus.map
        ((upperStarCompDerivedPlus AddCommGrpCat.{u + 1} g f gf w).hom.app K) =
    etaleDerivedRestriction f K ≫
      etaleDerivedRestriction g
        ((upperStar AddCommGrpCat.{u + 1} f).mapDerivedCategoryPlus.obj K) := by
  subst gf
  exact restriction_comp f g K

private lemma restriction_square
    {Y V Y₀ V₀ : Scheme.{u}} (i : Y₀ ⟶ Y) (j : V₀ ⟶ V)
    (h : V ⟶ Y) (h₀ : V₀ ⟶ Y₀) (w : h₀ ≫ i = j ≫ h)
    (K : _root_.DerivedCategory.Plus (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})) :
    etaleDerivedRestriction i K ≫
        etaleDerivedRestriction h₀
          ((upperStar AddCommGrpCat.{u + 1} i).mapDerivedCategoryPlus.obj K) ≫
        (Sheaf.Γ V₀.smallEtaleTopology AddCommGrpCat.{u + 1}).rightDerivedFunctorPlus.map
          ((abelianDerivedSquareInverseImageIso i j h h₀ w).hom.app K) =
      etaleDerivedRestriction h K ≫
        etaleDerivedRestriction j
          ((upperStar AddCommGrpCat.{u + 1} h).mapDerivedCategoryPlus.obj K) := by
  rw [square_iso_eq]
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Functor.map_comp]
  rw [← Category.assoc, ← restriction_comp_of_eq i h₀ (j ≫ h) w.symm K]
  simp only [Category.assoc, ← Functor.map_comp_assoc, Iso.hom_inv_id_app]
  erw [CategoryTheory.Functor.map_id, Category.id_comp]
  exact restriction_comp h j K

private def restrictionNat {X Y : Scheme.{u}} (f : Y ⟶ X) :
    (Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{u + 1}).rightDerivedFunctorPlus ⋙
        (𝟭 AddCommGrpCat.{u + 1}).mapDerivedCategoryPlus ⟶
      (upperStar AddCommGrpCat.{u + 1} f).mapDerivedCategoryPlus ⋙
        (Sheaf.Γ Y.smallEtaleTopology AddCommGrpCat.{u + 1}).rightDerivedFunctorPlus :=
  Functor.rightDerivedFunctorPlusBaseChange
      ((Functor.rightUnitor _).hom ≫ (Functor.leftUnitor _).inv ≫
        Functor.whiskerRight (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).unit
          (Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{u + 1}) ≫
        (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft (upperStar AddCommGrpCat.{u + 1} f)
          (lowerStarCompGlobalSectionsIso AddCommGrpCat.{u + 1} f).hom)

private instance restrictionNatCommShift {X Y : Scheme.{u}} (f : Y ⟶ X) :
    NatTrans.CommShift (restrictionNat f) ℤ := by
  unfold restrictionNat
  infer_instance

private lemma restrictionNat_app {X Y : Scheme.{u}} (f : Y ⟶ X)
    (K : _root_.DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})) :
    (restrictionNat f).app K =
      (Functor.mapDerivedCategoryPlusIdIso AddCommGrpCat.{u + 1}).hom.app
          ((Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{u + 1}).rightDerivedFunctorPlus.obj K) ≫
        etaleDerivedRestriction f K := by
  apply (cancel_epi ((Functor.mapDerivedCategoryPlusIdIso AddCommGrpCat.{u + 1}).inv.app
    ((Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{u + 1}).rightDerivedFunctorPlus.obj K))).1
  rw [Iso.inv_hom_id_app_assoc]
  exact (derivedUnit_classicalPullback_coherence f K).symm

private lemma sections_lower_bound (X : Scheme.{u})
    (M : _root_.DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}))
    (n : ℤ) (hM : ∀ q : ℤ, q < n → IsZero
      ((_root_.DerivedCategory.Plus.homologyFunctor _ q).obj M)) :
    ∀ q : ℤ, q < n → IsZero
      ((_root_.DerivedCategory.Plus.homologyFunctor _ q).obj
        ((Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{u + 1}).rightDerivedFunctorPlus.obj M)) := by
  have : M.obj.IsGE n := (_root_.DerivedCategory.isGE_iff M.obj n).2 hM
  have : M.IsGE n := (_root_.DerivedCategory.Plus.isGE_ι_obj_iff M n).1 ‹M.obj.IsGE n›
  intro q hq
  exact Functor.isZero_homologyFunctor_rightDerivedFunctorPlus_obj_of_isGE _ M n hq

private lemma restriction_heart_test {X Y : Scheme.{u}} (f : Y ⟶ X)
    (K : _root_.DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}))
    (hH : ∀ q : ℤ, IsIso (etaleDerivedRestriction f
      ((_root_.DerivedCategory.Plus.singleFunctor _ 0).obj
        ((_root_.DerivedCategory.Plus.homologyFunctor _ q).obj K)))) :
    IsIso (etaleDerivedRestriction f K) := by
  have hη (M : _root_.DerivedCategory.Plus
      (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})) :
      IsIso ((restrictionNat f).app M) ↔ IsIso (etaleDerivedRestriction f M) := by
    rw [restrictionNat_app]
    exact isIso_comp_left_iff _ _
  apply (hη K).1
  apply (_root_.DerivedCategory.Plus.heart_test_bounded_below _ _ (restrictionNat f)
    (fun M ↦ (NatTrans.shift_app_comm (restrictionNat f) (1 : ℤ) M).symm)
    ?_ ?_ K ?_).1
  · intro M n hM q hq
    exact (𝟭 AddCommGrpCat.{u + 1}).isZero_homologyFunctor_mapDerivedCategory_obj
      (sections_lower_bound X M n hM q hq)
  · intro M n hM
    apply sections_lower_bound Y _ n
    intro q hq
    exact (upperStar AddCommGrpCat.{u + 1} f).isZero_homologyFunctor_mapDerivedCategory_obj
      (hM q hq)
  · intro q
    exact (hη _).2 (hH q)

private lemma restriction_single {X Y : Scheme.{u}} (f : Y ⟶ X)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hF : ∀ q : ℕ, Function.Bijective (cohomologyMap f F q)) :
    IsIso (etaleDerivedRestriction f
      ((_root_.DerivedCategory.Plus.singleFunctor _ 0).obj F)) := by
  rw [_root_.DerivedCategory.Plus.isIso_iff]
  intro n
  by_cases hn : 0 ≤ n
  · obtain ⟨q, rfl⟩ := Int.eq_ofNat_of_zero_le hn
    obtain ⟨b₁, b₂, hb⟩ := exists_addEquiv_derivedGlobal_ext_pullback f F q
    apply (ConcreteCategory.isIso_iff_bijective _).2
    have hp : Function.Bijective (fun x ↦ b₂
        (((_root_.DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).map
          (etaleDerivedRestriction f
            ((_root_.DerivedCategory.Plus.singleFunctor _ 0).obj F))).hom x)) := by
      convert (hF q).comp b₁.bijective using 1
      funext x
      exact hb x
    exact (Function.Bijective.of_comp_iff' b₂.bijective _).1 hp
  · have hsrc := sections_lower_bound X
      ((_root_.DerivedCategory.Plus.singleFunctor _ 0).obj F) 0
      (fun q hq ↦ _root_.DerivedCategory.Plus.isZero_homology_of_isGE _ 0 q hq)
      n (lt_of_not_ge hn)
    have htgt := sections_lower_bound Y
      ((upperStar AddCommGrpCat.{u + 1} f).mapDerivedCategoryPlus.obj
        ((_root_.DerivedCategory.Plus.singleFunctor _ 0).obj F)) 0
      (fun q hq ↦ Functor.isZero_homologyFunctor_mapDerivedCategory_obj
        (upperStar AddCommGrpCat.{u + 1} f)
          (_root_.DerivedCategory.Plus.isZero_homology_of_isGE
            ((_root_.DerivedCategory.Plus.singleFunctor _ 0).obj F) 0 q hq))
      n (lt_of_not_ge hn)
    exact ⟨⟨0, hsrc.eq_of_src _ _, htgt.eq_of_src _ _⟩⟩

private lemma gabber_abelian (A : Type u) [CommRing A] (I : Ideal A) [HenselianRing A I]
    (F : Sheaf (Spec (.of A)).smallEtaleTopology AddCommGrpCat.{u + 1})
    (hF : F.IsTorsion) (q : ℕ) :
    Function.Bijective
      (cohomologyMap (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) F q) := by
  let Φ := sheafCompose (Spec (.of A)).smallEtaleTopology
    (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) AddCommGrpCat.{u + 1})
  let G := Φ.objPreimage F
  let e := Φ.objObjPreimageIso F
  have : Scheme.IsTorsionSheaf (Φ.obj G) :=
    (Scheme.isTorsionSheaf_iff_isTorsion _).2 (hF.of_iso e.symm)
  have : Scheme.IsTorsionModuleSheaf G :=
    (Scheme.isTorsionSheaf_sheafCompose_forget₂_obj_iff _ G).1 inferInstance
  exact bijective_cohomologyMap_of_iso _ e q
    (bijective_cohomologyMap_of_henselianRing (ULift.{u + 1} ℤ) I G q)

private lemma gabber_derived (A : Type u) [CommRing A] (I : Ideal A) [HenselianRing A I]
    (K : _root_.DerivedCategory.Plus
      (Sheaf (Spec (.of A)).smallEtaleTopology AddCommGrpCat.{u + 1}))
    (hK : (Spec (.of A)).HasTorsionEtaleCohomology K.obj) :
    IsIso (etaleDerivedRestriction
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) K) := by
  apply restriction_heart_test
  intro q
  exact restriction_single _ _ (gabber_abelian A I _ (hK q))

private theorem torsionHomology_directImage_single
    {X Y : Scheme.{u}} (h : X ⟶ Y) [QuasiCompact h] [QuasiSeparated h]
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (hG : G.IsTorsion) :
    DerivedCategory.Plus.torsionHomology Y
      ((rightDerivedLowerStarPlus AddCommGrpCat.{u + 1} h).obj
        ((_root_.DerivedCategory.Plus.singleFunctor _ 0).obj G)) := by
  intro n
  apply (Scheme.isTorsionSheaf_iff_isTorsion _).2
  by_cases hn : 0 ≤ n
  · obtain ⟨q, rfl⟩ := Int.eq_ofNat_of_zero_le hn
    apply (Scheme.isTorsionAbelianSheaf_characterizations _).1.mp
    apply (Scheme.isTorsionAbelianSheaf_characterizations _).2.mpr
    intro Ω _ _ s x
    obtain ⟨m, hm, hmx, -⟩ := qcqs_higherDirectImages_prime_torsion h Set.univ G
      (fun Ω _ _ s x ↦ by
        obtain ⟨m, hm, hmx⟩ := isOfFinAddOrder_iff_nsmul_eq_zero.mp
          ((Scheme.isTorsion_iff_isAddTorsion_sheafFiber G).mp hG Ω s x)
        exact ⟨m, hm, hmx, fun _ _ _ ↦ Set.mem_univ _⟩) q Ω s x
    exact isOfFinAddOrder_iff_nsmul_eq_zero.mpr ⟨m, hm, hmx⟩
  · have hz : IsZero ((_root_.DerivedCategory.Plus.homologyFunctor _ n).obj
        ((rightDerivedLowerStarPlus AddCommGrpCat.{u + 1} h).obj
          ((_root_.DerivedCategory.Plus.singleFunctor _ 0).obj G))) :=
      Functor.isZero_homologyFunctor_rightDerivedFunctorPlus_obj_of_isGE
      (lowerStar AddCommGrpCat.{u + 1} h)
      ((_root_.DerivedCategory.Plus.singleFunctor _ 0).obj G) 0 (lt_of_not_ge hn)
    exact Scheme.isTorsion_of_nsmul_id_eq_zero (N := 1) (by decide)
      (by
        simpa only [one_smul] using hz.eq_of_src (𝟙 _) 0)

private lemma restriction_counit {X Y : Scheme.{u}} (f : Y ⟶ X)
    (K : _root_.DerivedCategory.Plus (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})) :
    etaleDerivedRestriction f
        ((lowerStar AddCommGrpCat.{u + 1} f).rightDerivedFunctorPlus.obj K) ≫
      (Sheaf.Γ Y.smallEtaleTopology AddCommGrpCat.{u + 1}).rightDerivedFunctorPlus.map
        ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).derivedPlus.counit.app K) =
      (etaleLerayPlus f).hom.app K := by
  unfold etaleDerivedRestriction
  have hn := (etaleLerayPlus f).hom.naturality
    ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).derivedPlus.counit.app K)
  dsimp only [Functor.comp_map] at hn
  erw [Category.assoc, ← hn]
  rw [← Functor.map_comp_assoc]
  simp only [Adjunction.right_triangle_components, CategoryTheory.Functor.map_id, Category.id_comp]
  rfl

private lemma restriction_baseChange
    {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {g : Y' ⟶ Y}
    {f' : X' ⟶ Y'} {g' : X' ⟶ X} (sq : CommSq g' f' f g)
    (K : _root_.DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})) :
    etaleDerivedRestriction g
        ((lowerStar AddCommGrpCat.{u + 1} f).rightDerivedFunctorPlus.obj K) ≫
      (Sheaf.Γ Y'.smallEtaleTopology AddCommGrpCat.{u + 1}).rightDerivedFunctorPlus.map
        ((baseChange AddCommGrpCat.{u + 1} sq).app K) ≫
      (etaleLerayPlus f').hom.app
        ((upperStar AddCommGrpCat.{u + 1} g').mapDerivedCategoryPlus.obj K) =
    (etaleLerayPlus f).hom.app K ≫ etaleDerivedRestriction g' K := by
  rw [baseChange_app, baseChangeUnitStep_app, baseChangeSquareStep_hom_app,
    baseChangeCounitStep_app, derivedUpperStarLowerStarAdjunctionPlus_eq_derivedPlus,
    derivedUpperStarLowerStarAdjunctionPlus_eq_derivedPlus]
  simp only [Functor.map_comp, Category.assoc]
  have hnε := (etaleLerayPlus f').hom.naturality
    ((upperStar AddCommGrpCat.{u + 1} g').mapDerivedCategoryPlus.map
      ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).derivedPlus.counit.app K))
  have hnθ := (etaleLerayPlus f').hom.naturality
    ((pullbackSquareComparison AddCommGrpCat.{u + 1} sq).hom.app
      ((lowerStar AddCommGrpCat.{u + 1} f).rightDerivedFunctorPlus.obj K))
  dsimp only [Functor.comp_map] at hnε hnθ
  erw [hnε, reassoc_of% hnθ]
  have he : abelianDerivedSquareInverseImageIso g g' f f' sq.w.symm =
      pullbackSquareComparison AddCommGrpCat.{u + 1} sq := by
    rw [square_iso_eq, pullbackSquareComparison_eq]
  have hs := restriction_square g g' f f' sq.w.symm
    ((lowerStar AddCommGrpCat.{u + 1} f).rightDerivedFunctorPlus.obj K)
  rw [he] at hs
  have hs' := congrArg
    (fun a ↦ a ≫
      (Sheaf.Γ X'.smallEtaleTopology AddCommGrpCat.{u + 1}).rightDerivedFunctorPlus.map
        ((upperStar AddCommGrpCat.{u + 1} g').mapDerivedCategoryPlus.map
          ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).derivedPlus.counit.app K))) hs
  simp only [Category.assoc] at hs'
  trans etaleDerivedRestriction f
      ((lowerStar AddCommGrpCat.{u + 1} f).rightDerivedFunctorPlus.obj K) ≫
    etaleDerivedRestriction g'
      ((upperStar AddCommGrpCat.{u + 1} f).mapDerivedCategoryPlus.obj
        ((lowerStar AddCommGrpCat.{u + 1} f).rightDerivedFunctorPlus.obj K)) ≫
    (Sheaf.Γ X'.smallEtaleTopology AddCommGrpCat.{u + 1}).rightDerivedFunctorPlus.map
      ((upperStar AddCommGrpCat.{u + 1} g').mapDerivedCategoryPlus.map
        ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).derivedPlus.counit.app K))
  · simpa only [etaleDerivedRestriction, Category.assoc, Functor.comp_obj,
      Functor.id_obj] using hs'
  · erw [← restriction_naturality]
    rw [← Category.assoc, restriction_counit]

/-- The canonical closed-fibre restriction is an isomorphism in D+(Ab), hence in D(Ab).
There are no finiteness conditions on I, on the base ring, or on the torsion primes.

Source: Stacks Project, Tags 09ZI, 0DDD and 0DDE
(blueprint: lem-per-proper-henselian-derived-restriction).

Proof:
1. The canonical restriction is the natural right-derived section pullback. It differs
   from the shift-compatible exact base-change transformation by the canonical identity
   comparison on its source. Derived sections and exact inverse image preserve every
   lower cohomology bound. The heart test reduces the assertion to K = F[0], for each
   torsion cohomology sheaf F.
2. Properness gives quasi-compactness and quasi-separatedness. For E = Rf_*F[0], the
   qcqs higher-image torsion theorem gives torsion in every nonnegative degree. In
   negative degrees E has zero cohomology, by preservation of the lower bound zero.
3. Gabber comparison applies to every torsion abelian sheaf on Spec A, after the
   canonical equivalence with sheaves of ULift ℤ-modules. The Ext/global-derived
   comparison identifies its classical cohomology maps with the homology of the
   canonical derived restriction. Negative homology vanishes on both sides. Thus
   restriction is invertible on torsion sheaves in degree zero. The heart test applied
   to E proves that restriction along Spec(A/I) -> Spec A is invertible on E.
4. Proper base change identifies the pullback of E with Rf₀_*i⁻¹F[0]. Applying derived
   sections and the two Leray isomorphisms gives an invertible map for F[0].
5. Expand the exchange map as its derived adjunction unit, inverse-image square
   comparison, and pulled-back counit. Naturality of Leray, restriction composition,
   restriction naturality, and the adjunction triangle identity show that this map is
   precisely the canonical restriction along i. This completes the heart reduction.
The proof uses no upper bound, uniform annihilator, or finiteness condition on I. -/
theorem proper_henselian_derived_restriction
    (A : Type u) [CommRing A] (I : Ideal A) [HenselianRing A I]
    {Y : Scheme.{u}} (f : Y ⟶ Spec (.of A)) [IsProper f]
    (K : _root_.DerivedCategory.Plus (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}))
    (hK : Y.HasTorsionEtaleCohomology K.obj) :
    IsIso (abelianDerivedCohomologyPullback
      (pullback.fst f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))) K) := by
  rw [pullback_eq]
  apply restriction_heart_test
  intro q
  let F := (_root_.DerivedCategory.Plus.homologyFunctor _ q).obj K
  let M := (_root_.DerivedCategory.Plus.singleFunctor _ 0).obj F
  let z := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))
  let i : pullback f z ⟶ Y := pullback.fst f z
  let f₀ : pullback f z ⟶ Spec (.of (A ⧸ I)) := pullback.snd f z
  let sq : IsPullback i f₀ f z := IsPullback.of_hasPullback f z
  have hM : DerivedCategory.Plus.torsionHomology Y M := by
    intro n
    apply (Scheme.isTorsionSheaf_iff_isTorsion _).2
    by_cases hn : n = 0
    · subst n
      exact (hK q).of_iso
        ((_root_.DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).app F).symm
    · have hz : IsZero ((_root_.DerivedCategory.Plus.homologyFunctor _ n).obj M) :=
        IsZero.of_iso (HomologicalComplex.isZero_single_obj_homology _ _ _ _ hn)
          ((_root_.DerivedCategory.homologyFunctorFactors _ n).app _)
      exact Scheme.isTorsion_of_nsmul_id_eq_zero (N := 1) (by decide)
        (by simpa only [one_smul] using hz.eq_of_src (𝟙 _) 0)
  have ht : (Spec (.of A)).HasTorsionEtaleCohomology
      ((lowerStar AddCommGrpCat.{u + 1} f).rightDerivedFunctorPlus.obj M).obj := by
    intro n
    exact (Scheme.isTorsionSheaf_iff_isTorsion _).1
      (torsionHomology_directImage_single f F (hK q) n)
  have := gabber_derived A I _ ht
  have := isIso_baseChange_of_isProper sq M hM
  have hi := restriction_baseChange sq.toCommSq M
  have hc : IsIso ((etaleLerayPlus f).hom.app M ≫ etaleDerivedRestriction i M) := by
    rw [← hi]
    infer_instance
  exact (isIso_comp_left_iff ((etaleLerayPlus f).hom.app M) _).1 hc

/-- Naturality of proper henselian restriction in the bounded-below torsion complex.
Source: Stacks Project, Tags 01F8 and 015M
(blueprint: lem-per-proper-henselian-derived-restriction).

Proof: unfold the canonical pullback as the component of its right-derived descent
natural transformation, and apply naturality to the given derived coefficient map.
The naturality identity holds for arbitrary bounded-below complexes. -/
theorem proper_henselian_derived_restriction_naturality
    (A : Type u) [CommRing A] (I : Ideal A) [HenselianRing A I]
    {Y : Scheme.{u}} (f : Y ⟶ Spec (.of A)) [IsProper f]
    (K L : _root_.DerivedCategory.Plus
      (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}))
    (hK : Y.HasTorsionEtaleCohomology K.obj) (hL : Y.HasTorsionEtaleCohomology L.obj)
    (a : K ⟶ L) :
    (Sheaf.Γ Y.smallEtaleTopology AddCommGrpCat.{u + 1}).rightDerivedFunctorPlus.map a ≫
      abelianDerivedCohomologyPullback
        (pullback.fst f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))) L =
    abelianDerivedCohomologyPullback
        (pullback.fst f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))) K ≫
      (Sheaf.Γ (pullback f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))).smallEtaleTopology
        AddCommGrpCat.{u + 1}).rightDerivedFunctorPlus.map
          ((upperStar AddCommGrpCat.{u + 1}
            (pullback.fst f
              (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))))).mapDerivedCategoryPlus.map
                a) := by
  have _ := hK
  have _ := hL
  unfold abelianDerivedCohomologyPullback
  exact NatTrans.naturality _ a

/-- The restriction square for a morphism of henselian pairs, a compatible map of
proper schemes, and a specified derived coefficient morphism commutes.
Source: Stacks Project, Tags 01F8 and 015M
(blueprint: lem-per-proper-henselian-derived-restriction).

Proof (step 7 of the node): the fibre-product projection identity supplies the
commutative square. The exact derived square compositor is the inverse compositor
along one diagonal followed by the compositor along the other. The derived adjunction
unit composition law and associativity of the Leray comparison prove that canonical
restriction respects composition. Apply that law to both diagonals, then naturality
along the given coefficient morphism. These identities require neither properness nor
torsion; those hypotheses ensure invertibility by the first theorem. -/
theorem proper_henselian_derived_restriction_pairs
    {A B : Type u} [CommRing A] [CommRing B]
    (I : Ideal A) (J : Ideal B) [HenselianRing A I] [HenselianRing B J]
    (φ : A →+* B) (hIJ : I ≤ J.comap φ)
    {Y V : Scheme.{u}} (f : Y ⟶ Spec (.of A)) (g : V ⟶ Spec (.of B))
    [IsProper f] [IsProper g]
    (h : V ⟶ Y) (hh : h ≫ f = g ≫ Spec.map (CommRingCat.ofHom φ))
    (K : _root_.DerivedCategory.Plus (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}))
    (L : _root_.DerivedCategory.Plus (Sheaf V.smallEtaleTopology AddCommGrpCat.{u + 1}))
    (hK : Y.HasTorsionEtaleCohomology K.obj) (hL : V.HasTorsionEtaleCohomology L.obj)
    (a : (upperStar AddCommGrpCat.{u + 1} h).mapDerivedCategoryPlus.obj K ⟶ L) :
    abelianDerivedCohomologyPullback
        (pullback.fst f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))) K ≫
      abelianDerivedCohomologyPullback (henselianClosedFibreMap I J φ hIJ f g h hh)
        ((upperStar AddCommGrpCat.{u + 1}
          (pullback.fst f
            (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))))).mapDerivedCategoryPlus.obj K) ≫
      (Sheaf.Γ (pullback g (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))).smallEtaleTopology
        AddCommGrpCat.{u + 1}).rightDerivedFunctorPlus.map
          (abelianDerivedSquareCoefficientMap
            (pullback.fst f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))))
            (pullback.fst g (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))))
            h (henselianClosedFibreMap I J φ hIJ f g h hh)
            (pullback.lift_fst _ _ _) K L a) =
    abelianDerivedCohomologyPullback h K ≫
      (Sheaf.Γ V.smallEtaleTopology AddCommGrpCat.{u + 1}).rightDerivedFunctorPlus.map a ≫
      abelianDerivedCohomologyPullback
        (pullback.fst g (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))) L := by
  have _ := hK
  have _ := hL
  simp only [pullback_eq, abelianDerivedSquareCoefficientMap, Functor.map_comp]
  erw [reassoc_of% restriction_square
    (pullback.fst f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))))
    (pullback.fst g (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))))
    h (henselianClosedFibreMap I J φ hIJ f g h hh) (pullback.lift_fst _ _ _) K]
  erw [← restriction_naturality]

end AlgebraicGeometry.Etale
