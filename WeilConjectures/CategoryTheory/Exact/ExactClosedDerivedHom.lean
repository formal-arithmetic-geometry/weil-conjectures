/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.DualizableTransfer
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralResidueDerivedMonoidal
import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.ClosedTriangulated
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
import all WeilConjectures.CategoryTheory.ExactMonoidalEquivalenceDerived.ExactMonoidalEquivalenceDerived
/-! # Exact closed functors preserve unbounded derived internal Hom -/
@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
universe u c d
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed
namespace CategoryTheory
namespace Functor
/-- The canonical internal-Hom comparison component, shared without unfolding the closed
adjunction. Source: the tensor-Hom evaluation transpose
(blueprint: lem-sf-exact-closed-derived-hom). -/
@[irreducible]
def closedComparison {C D : Type*} [Category C] [Category D]
    [MonoidalCategory C] [MonoidalCategory D] [MonoidalClosed C] [MonoidalClosed D]
    (F : C ⥤ D) [F.LaxMonoidal] (K M : C) :
    F.obj ((ihom K).obj M) ⟶ (ihom (F.obj K)).obj (F.obj M) :=
  (LaxMonoidal.ihomComparison F K).natTrans.app M
end Functor
section Square
open Category Functor.LaxMonoidal
variable {A B E H : Type*} [Category A] [Category B] [Category E] [Category H]
  [MonoidalCategory A] [MonoidalCategory B] [MonoidalCategory E] [MonoidalCategory H]
  [MonoidalClosed A] [MonoidalClosed B] [MonoidalClosed E] [MonoidalClosed H]
  (Q : A ⥤ B) (R : E ⥤ H) (F : A ⥤ E) (G : B ⥤ H)
  [Q.LaxMonoidal] [R.LaxMonoidal] [F.LaxMonoidal] [G.LaxMonoidal]
  (e : Q ⋙ G ≅ F ⋙ R) [NatTrans.IsMonoidal e.hom] (K M : A)
private theorem comparison_square :
    G.map ((ihomComparison Q K).natTrans.app M) ≫
        (ihomComparison G (Q.obj K)).natTrans.app (Q.obj M) ≫
        (pre (e.inv.app K)).app (G.obj (Q.obj M)) ≫
        (ihom (R.obj (F.obj K))).map (e.hom.app M) =
      e.hom.app ((ihom K).obj M) ≫
        R.map ((ihomComparison F K).natTrans.app M) ≫
        (ihomComparison R (F.obj K)).natTrans.app (F.obj M) := by
  have q := ihomComparison_app_comp_map_app e.inv K M
  have q' := congrArg (fun f ↦ e.hom.app ((ihom K).obj M) ≫ f ≫
    (ihom (R.obj (F.obj K))).map (e.hom.app M)) q
  simp only [Functor.comp_obj, ihomComparison_comp_app] at q'
  simp only [← Functor.map_comp, Iso.inv_hom_id_app, Category.assoc,
    Iso.hom_inv_id_app_assoc] at q'
  erw [Functor.map_id, Category.comp_id] at q'
  exact q'.symm

/-- Canonical closed comparisons commute with a monoidal square.
Source: naturality and composition of the evaluation transpose
(blueprint: lem-sf-exact-closed-derived-hom). -/
theorem closedComparison_square :
    G.map (Functor.closedComparison Q K M) ≫
        Functor.closedComparison G (Q.obj K) (Q.obj M) ≫
        (pre (e.inv.app K)).app (G.obj (Q.obj M)) ≫
        (ihom (R.obj (F.obj K))).map (e.hom.app M) =
      e.hom.app ((ihom K).obj M) ≫
        R.map (Functor.closedComparison F K M) ≫
        Functor.closedComparison R (F.obj K) (F.obj M) := by
  unfold Functor.closedComparison
  exact comparison_square Q R F G e K M

private theorem comparison_isIso_of_square
    [IsIso ((ihomComparison Q K).natTrans.app M)]
    [IsIso ((ihomComparison F K).natTrans.app M)]
    [IsIso ((ihomComparison R (F.obj K)).natTrans.app (F.obj M))] :
    IsIso ((ihomComparison G (Q.obj K)).natTrans.app (Q.obj M)) := by
  let t := (pre (e.inv.app K)).app (G.obj (Q.obj M)) ≫
    (ihom (R.obj (F.obj K))).map (e.hom.app M)
  have : IsIso t := by dsimp [t]; infer_instance
  have ht : IsIso (G.map ((ihomComparison Q K).natTrans.app M) ≫
      (ihomComparison G (Q.obj K)).natTrans.app (Q.obj M) ≫ t) := by
    dsimp only [t]
    rw [comparison_square Q R F G e K M]
    infer_instance
  have := IsIso.of_isIso_comp_left (G.map ((ihomComparison Q K).natTrans.app M))
    ((ihomComparison G (Q.obj K)).natTrans.app (Q.obj M) ≫ t)
  exact IsIso.of_isIso_comp_right _ t

include e in
include e in
end Square
end CategoryTheory
namespace CategoryTheory.Functor
variable {C : Type c} [Category.{u + 1} C] [Abelian C]
  [IsGrothendieckAbelian.{u + 1} C] [MonoidalCategory C] [MonoidalPreadditive C]
  [MonoidalClosed C] [BraidedCategory C] [Abelian.HasFunctorialFlatResolution C]
  {D : Type d} [Category.{u + 1} D] [Abelian D]
  [IsGrothendieckAbelian.{u + 1} D] [MonoidalCategory D] [MonoidalPreadditive D]
  [MonoidalClosed D] [BraidedCategory D] [Abelian.HasFunctorialFlatResolution D]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [F.PreservesFlat] [F.IsLeftAdjoint] [F.Monoidal]
@[instance_reducible]
private noncomputable def homotopyClosed :
    MonoidalClosed (HomotopyCategory C (.up ℤ)) where
  closed P := ⟨HomotopyCategory.internalHom P, HomotopyCategory.tensorHomAdjunction P⟩

private theorem qh_comparison_isIso (P I : CochainComplex C ℤ) [I.IsKInjective] :
    IsIso ((Functor.LaxMonoidal.ihomComparison DerivedCategory.Qh
      ((HomotopyCategory.quotient C (.up ℤ)).obj P)).natTrans.app
        ((HomotopyCategory.quotient C (.up ℤ)).obj I)) := by
  rw [Functor.LaxMonoidal.ihomComparison_app_eq_curry]
  change IsIso (MonoidalClosed.curry (_ ≫ DerivedCategory.Qh.map
    ((HomotopyCategory.tensorHomAdjunction
      ((HomotopyCategory.quotient C (.up ℤ)).obj P)).counit.app
        ((HomotopyCategory.quotient C (.up ℤ)).obj I))))
  rw [HomotopyCategory.tensorHomAdjunction_counit_app]
  exact DerivedCategory.isIso_qhInternalHomToIhom P I

attribute [local instance] homotopyClosed
@[instance_reducible]
private noncomputable def mapHomotopyMonoidal :
    (F.mapHomotopyCategory (.up ℤ)).Monoidal := by
  letI : (F.mapHomotopyCategory (.up ℤ)).OplaxMonoidal :=
    Functor.mapHomotopyCategoryOplaxMonoidal F
  have : IsIso (Functor.OplaxMonoidal.η (F.mapHomotopyCategory (.up ℤ))) := by
    rw [Functor.mapHomotopyCategory_η]
    infer_instance
  have (X Y : HomotopyCategory C (.up ℤ)) :
      IsIso (Functor.OplaxMonoidal.δ (F.mapHomotopyCategory (.up ℤ)) X Y) :=
    inferInstanceAs (IsIso (((Functor.OplaxMonoidal.mapHomotopyCategoryδNatTrans
      (.up ℤ) F).app X).app Y))
  exact .ofOplaxMonoidal _

attribute [local instance] mapHomotopyMonoidal

omit [Abelian.HasFunctorialFlatResolution C] [Abelian.HasFunctorialFlatResolution D]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F] [F.PreservesFlat] in
private theorem mapHomotopyFactors_monoidal :
    NatTrans.IsMonoidal (F.mapHomotopyCategoryFactors (.up ℤ)).hom := by
  apply ExactMonoidalEquivalenceDerived.monoidal_of_oplax
  · change 𝟙 _ ≫ (HomotopyCategory.quotient D (.up ℤ)).map
        (OplaxMonoidal.η (F.mapHomologicalComplex (.up ℤ))) ≫ 𝟙 _ =
      (F.mapHomotopyCategory (.up ℤ)).map (𝟙 _) ≫
        (HomotopyCategory.quotient D (.up ℤ)).map
          (OplaxMonoidal.η (F.mapHomologicalComplex (.up ℤ)))
    rw [Category.id_comp, Category.comp_id, CategoryTheory.Functor.map_id, Category.id_comp]
  · intro K L
    change 𝟙 _ ≫ (HomotopyCategory.quotient D (.up ℤ)).map
        (OplaxMonoidal.δ (F.mapHomologicalComplex (.up ℤ)) K L) ≫ 𝟙 _ =
      ((F.mapHomotopyCategory (.up ℤ)).map (𝟙 _) ≫
        (HomotopyCategory.quotient D (.up ℤ)).map
          (((Functor.OplaxMonoidal.mapHomologicalComplexδNatTrans (.up ℤ) F).app K).app L)) ≫
        (𝟙 _ ⊗ₘ 𝟙 _)
    rw [Category.id_comp, Category.comp_id, CategoryTheory.Functor.map_id,
      Category.id_comp]
    erw [tensorHom_id, id_whiskerRight, Category.comp_id]
    rfl

private theorem quotient_comparison_isIso (P I : CochainComplex C ℤ) :
    IsIso ((Functor.LaxMonoidal.ihomComparison
      (HomotopyCategory.quotient C (.up ℤ)) P).natTrans.app I) := by
  rw [Functor.LaxMonoidal.ihomComparison_app_eq_curry]
  have hμ : Functor.LaxMonoidal.μ (HomotopyCategory.quotient C (.up ℤ)) P
      ((ihom P).obj I) = 𝟙 _ := rfl
  rw [hμ, Category.id_comp]
  change IsIso (MonoidalClosed.curry
    ((HomotopyCategory.quotient C (.up ℤ)).map
      ((CochainComplex.tensorHomAdjunction P).counit.app I)))
  erw [← HomotopyCategory.tensorHomAdjunction_counit_app
    ((HomotopyCategory.quotient C (.up ℤ)).obj P) I]
  change IsIso (MonoidalClosed.curry ((ihom.ev
    ((HomotopyCategory.quotient C (.up ℤ)).obj P)).app
      ((HomotopyCategory.quotient C (.up ℤ)).obj I)))
  rw [← MonoidalClosed.uncurry_id_eq_ev, MonoidalClosed.curry_uncurry]
  infer_instance

attribute [local instance] CochainComplex.monoidalClosed
omit [Abelian.HasFunctorialFlatResolution C] in
/-- The canonical strong tensor structure on an exact derived functor, transported from
its K-flat left derived functor. Source: Stacks 07A4
(blueprint: lem-sf-exact-closed-derived-hom). -/
@[irreducible]
noncomputable def exactClosedDerivedMonoidal : F.mapDerivedCategory.Monoidal :=
  letI := F.residueDerivedMonoidal
  Functor.Monoidal.transport F.leftDerivedFunctorIsoMapDerivedCategory
attribute [local instance] exactClosedDerivedMonoidal
private theorem derivedFactorsh_monoidal :
    NatTrans.IsMonoidal F.mapDerivedCategoryFactorsh.hom := by
  unfold exactClosedDerivedMonoidal
  letI := F.residueDerivedMonoidal
  letI := Functor.Monoidal.transport F.leftDerivedFunctorIsoMapDerivedCategory
  have hc : NatTrans.IsMonoidal F.leftDerivedFunctorCounit := by
    have := DerivedCategory.isIso_ε_Qh D
    apply ExactMonoidalEquivalenceDerived.square_monoidal DerivedCategory.Qh DerivedCategory.Qh
      (F.mapHomotopyCategory (.up ℤ)) F.leftDerivedFunctor F.leftDerivedFunctorCounit
    · rfl
    · exact F.residueDerivedMonoidal_counit
  have hm : NatTrans.IsMonoidal F.leftDerivedFunctorIsoMapDerivedCategory.hom :=
    Functor.Monoidal.natTransIsMonoidal_of_transport F.leftDerivedFunctorIsoMapDerivedCategory
  have hi : NatTrans.IsMonoidal F.leftDerivedFunctorIsoMapDerivedCategory.inv := inferInstance
  have h : F.mapDerivedCategoryFactorsh.hom =
      (Functor.isoWhiskerLeft DerivedCategory.Qh
        F.leftDerivedFunctorIsoMapDerivedCategory.symm).hom ≫
          F.leftDerivedFunctorCounit := by
    apply NatTrans.ext
    funext K
    have hf := NatTrans.congr_app F.leftDerivedFunctorIsoMapDerivedCategory_hom_fac K
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app] at hf
    simp only [NatTrans.comp_app, Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
      Iso.symm_hom, ← hf, Iso.inv_hom_id_app_assoc]
  rw [h]
  dsimp only [Functor.isoWhiskerLeft_hom, Iso.symm_hom]
  apply NatTrans.IsMonoidal.comp

private theorem homotopy_comparison_isIso (P I : CochainComplex C ℤ) :
    IsIso ((Functor.LaxMonoidal.ihomComparison (F.mapHomotopyCategory (.up ℤ))
      ((HomotopyCategory.quotient C (.up ℤ)).obj P)).natTrans.app
        ((HomotopyCategory.quotient C (.up ℤ)).obj I)) := by
  have := mapHomotopyFactors_monoidal F
  have := DerivedCategory.isIso_ihomComparison_mapHomologicalComplex F adj P
  have := quotient_comparison_isIso P I
  have := quotient_comparison_isIso
    ((F.mapHomologicalComplex (.up ℤ)).obj P)
    ((F.mapHomologicalComplex (.up ℤ)).obj I)
  exact CategoryTheory.comparison_isIso_of_square
    (HomotopyCategory.quotient C (.up ℤ)) (HomotopyCategory.quotient D (.up ℤ))
    (F.mapHomologicalComplex (.up ℤ)) (F.mapHomotopyCategory (.up ℤ))
    (F.mapHomotopyCategoryFactors (.up ℤ)) P I

private theorem derived_comparison_isIso_Qh (P I : CochainComplex C ℤ) [I.IsKInjective] :
    IsIso ((Functor.LaxMonoidal.ihomComparison F.mapDerivedCategory
      (DerivedCategory.Qh.obj ((HomotopyCategory.quotient C (.up ℤ)).obj P))).natTrans.app
        (DerivedCategory.Qh.obj ((HomotopyCategory.quotient C (.up ℤ)).obj I))) := by
  have := derivedFactorsh_monoidal F
  have := CochainComplex.isKInjective_map_of_adjunction F adj I
  have := qh_comparison_isIso P I
  have : IsIso ((Functor.LaxMonoidal.ihomComparison DerivedCategory.Qh
      ((F.mapHomotopyCategory (.up ℤ)).obj
        ((HomotopyCategory.quotient C (.up ℤ)).obj P))).natTrans.app
      ((F.mapHomotopyCategory (.up ℤ)).obj
        ((HomotopyCategory.quotient C (.up ℤ)).obj I))) :=
    qh_comparison_isIso ((F.mapHomologicalComplex (.up ℤ)).obj P)
      ((F.mapHomologicalComplex (.up ℤ)).obj I)
  have := homotopy_comparison_isIso F adj P I
  exact CategoryTheory.comparison_isIso_of_square DerivedCategory.Qh DerivedCategory.Qh
    (F.mapHomotopyCategory (.up ℤ)) F.mapDerivedCategory
    F.mapDerivedCategoryFactorsh
    ((HomotopyCategory.quotient C (.up ℤ)).obj P)
    ((HomotopyCategory.quotient C (.up ℤ)).obj I)

/-- Exact closed pullback with an exact left adjoint preserves unbounded derived internal Hom.
Source: Stacks Project, Tags 08JB and 07A4.

Represent the target by a K-injective complex; the exact left adjoint makes its image
K-injective. The ordinary closed comparison induces an isomorphism on Hom complexes, by
the degreewise projection formula. The monoidal localization squares identify its image
with the canonical derived evaluation transpose. Transport along representatives finishes.
(blueprint: lem-sf-exact-closed-derived-hom) -/
theorem isIso_ihomComparison_exactDerived (K : DerivedCategory C) :
    letI := exactClosedDerivedMonoidal F
    IsIso (Functor.LaxMonoidal.ihomComparison F.mapDerivedCategory K).natTrans := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro M
  let P := DerivedCategory.Q.objPreimage K
  let eP := (DerivedCategory.quotientCompQhIso C).app P ≪≫
    DerivedCategory.Q.objObjPreimageIso K
  obtain ⟨I, hI, ⟨eM⟩⟩ := DerivedCategory.exists_iso_Q_obj_of_isKInjective M
  let eI := (DerivedCategory.quotientCompQhIso C).app I
  have hPM : IsIso ((Functor.LaxMonoidal.ihomComparison F.mapDerivedCategory
      (DerivedCategory.Qh.obj ((HomotopyCategory.quotient C (.up ℤ)).obj P))).natTrans.app M) := by
    rw [NatTrans.isIso_app_iff_of_iso _ (eM ≪≫ eI.symm)]
    exact derived_comparison_isIso_Qh F adj P I
  have h := Functor.LaxMonoidal.map_pre_app_comp_ihomComparison_app
    F.mapDerivedCategory eP.hom M
  have : IsIso ((Functor.LaxMonoidal.ihomComparison F.mapDerivedCategory K).natTrans.app M ≫
      (pre (F.mapDerivedCategory.map eP.hom)).app (F.mapDerivedCategory.obj M)) := by
    rw [← h]
    have : IsIso ((Functor.LaxMonoidal.ihomComparison F.mapDerivedCategory
        ((HomotopyCategory.quotient C (.up ℤ) ⋙ DerivedCategory.Qh).obj P)).natTrans.app M) :=
      hPM
    infer_instance
  exact IsIso.of_isIso_comp_right _
    ((pre (F.mapDerivedCategory.map eP.hom)).app (F.mapDerivedCategory.obj M))

private theorem isIso_ihomComparison_exactDerived_app (K M : DerivedCategory C) :
    letI := exactClosedDerivedMonoidal F
    IsIso ((Functor.LaxMonoidal.ihomComparison F.mapDerivedCategory K).natTrans.app M) := by
  exact @NatIso.isIso_app_of_isIso _ _ _ _ _ _
    (Functor.LaxMonoidal.ihomComparison F.mapDerivedCategory K).natTrans
    (isIso_ihomComparison_exactDerived F adj K) M

/-- The shared comparison component is invertible for an exact closed derived pullback.
Source: Stacks 08JB, 07A4; the preceding derived comparison theorem
(blueprint: lem-sf-exact-closed-derived-hom). -/
theorem isIso_closedComparison_exactDerived (K M : DerivedCategory C) :
    letI := exactClosedDerivedMonoidal F
    IsIso (Functor.closedComparison F.mapDerivedCategory K M) := by
  unfold Functor.closedComparison
  exact isIso_ihomComparison_exactDerived_app F adj K M

variable {L : D ⥤ C} [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
  (adj : L ⊣ F) [∀ P : C, IsIso (Functor.LaxMonoidal.ihomComparison F P).natTrans]
omit [PreservesFiniteLimits L] [PreservesFiniteColimits L]
  [Abelian.HasFunctorialFlatResolution C] [Abelian.HasFunctorialFlatResolution D]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F] [F.PreservesFlat] in
include adj in
include adj in
include adj in
include adj in
include adj in
end CategoryTheory.Functor
