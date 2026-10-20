/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NO
-/
module

public import Sheaf.AlgebraicGeometry.KInjectiveResolutions
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.GlobalSections
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective

public import Sheaf.AlgebraicGeometry.ClosedSupportHomSequence
import WeilConjectures.Algebra.Homology.KernelShiftedMappingCone

/-!
# Closed support as a relative section complex

Source: literature/blueprint/master/blueprint/sec-smooth-purity/sk-prop-sf-cbc/
lem-amb-closed-support-hom.md (blueprint: lem-amb-closed-support-hom).
-/

@[expose] public section

attribute [local instance 200000] CategoryTheory.Abelian.toPreadditive
attribute [local instance 200000] CategoryTheory.Preadditive.preadditiveHasZeroMorphisms
attribute [local instance 200000] AlgebraicGeometry.Etale.closedSupportEtaleHasSheafify
attribute [local instance 200000] AlgebraicGeometry.Etale.closedSupportEtaleHasWeakSheafify
attribute [local instance 200000] AlgebraicGeometry.Etale.closedSupportEtaleHasGlobalSections
attribute [local instance 200000] AlgebraicGeometry.Etale.closedSupportEtaleAbelian
attribute [local instance 200000] AlgebraicGeometry.Etale.closedSupportEtaleLinear

universe w v u v' u'

open CategoryTheory CategoryTheory.Limits Opposite HomologicalComplex

namespace CochainComplex
/-- The canonical closed-support construction and its normalization.
Source: Stacks, Tags 0A45, 095L (blueprint: lem-amb-closed-support-hom). -/
noncomputable def closedConeLift
    {C : Type u} [Category.{v} C] [Abelian C]
    {S P Q : CochainComplex C ℤ} (f : P ⟶ Q) (a : S ⟶ P) (ha : a ≫ f = 0) :
    S ⟶ (mappingCone f)⟦(-1 : ℤ)⟧ where
  f p := a.f p ≫
    homotopyCofiber.inlX f p (p + (-1)) (ComplexShape.up_mk _ _ (by omega))
  comm' p q hpq := by
    obtain rfl : q = p + 1 := by simpa using hpq.symm
    rw [shiftFunctor_obj_d', Category.assoc]
    change a.f p ≫ homotopyCofiber.inlX f p (p + (-1)) _ ≫
      ((-1 : ℤ).negOnePow • (mappingCone f).d (p + (-1)) (p + 1 + (-1))) =
      S.d p (p + 1) ≫ a.f (p + 1) ≫
        homotopyCofiber.inlX f (p + 1) (p + 1 + (-1)) (ComplexShape.up_mk _ _ (by omega))
    dsimp only [mappingCone, homotopyCofiber_d]
    simp only [Int.negOnePow_neg, Int.negOnePow_one, Units.neg_smul, one_smul,
      Preadditive.comp_neg]
    have h : -( a.f p ≫ homotopyCofiber.inlX f p (p + (-1))
        (ComplexShape.up_mk _ _ (by omega)) ≫ homotopyCofiber.d f (p + (-1)) p) =
        S.d p (p + 1) ≫ a.f (p + 1) ≫
          homotopyCofiber.inlX f (p + 1) p (ComplexShape.up_mk _ _ rfl) := by
      rw [homotopyCofiber.inlX_d f (p + (-1)) p (p + 1)
        (ComplexShape.up_mk _ _ (by omega)) (ComplexShape.up_mk _ _ rfl)]
      simp only [Preadditive.comp_add, Preadditive.comp_neg]
      have hz : a.f p ≫ f.f p = 0 := by
        simpa only [comp_f, zero_f] using congrArg (fun g ↦ g.f p) ha
      simp only [reassoc_of% hz, zero_comp, add_zero, neg_neg]
      rw [reassoc_of% (a.comm p (p + 1))]
    convert h using 1
    · simp only [show p + 1 + (-1) = p by omega, homotopyCofiber_X]
    · congr! 10 <;> omega
    · congr! 10 <;> omega


/-- The canonical closed-support construction and its normalization.
Source: Stacks, Tags 0A45, 095L (blueprint: lem-amb-closed-support-hom). -/
lemma closedConeLift_projections
    {C : Type u} [Category.{v} C] [Abelian C]
    {S P Q : CochainComplex C ℤ} (f : P ⟶ Q) (a : S ⟶ P) (ha : a ≫ f = 0)
    (p r : ℤ) (hr : r = p + (-1)) :
    (closedConeLift f a ha).f p ≫
        ((mappingCone f).shiftFunctorObjXIso (-1) p r hr).hom ≫
          homotopyCofiber.sndX f r = 0 ∧
    (closedConeLift f a ha).f p ≫
        ((mappingCone f).shiftFunctorObjXIso (-1) p r hr).hom ≫
          homotopyCofiber.fstX f r p (by change r + 1 = p; omega) = a.f p := by
  subst r
  dsimp only [closedConeLift, shiftFunctorObjXIso]
  simp

/-- The canonical closed-support construction and its normalization.
Source: Stacks, Tags 0A45, 095L (blueprint: lem-amb-closed-support-hom). -/
lemma closedConeLift_quasiIso
    {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    (S : ShortComplex (CochainComplex C ℤ)) (hS : S.ShortExact) :
    QuasiIso (closedConeLift S.g S.f S.zero) := by
  classical
  have hf (p : ℤ) : Epi (S.g.f p) := by
    have := hS.epi_g
    infer_instance
  obtain ⟨κ, hκ, hqκ, _⟩ := exists_kernel_to_shifted_mappingCone_of_degreewise_epi S.g hf
  let e := hS.fIsKernel.conePointUniqueUpToIso (kernelIsKernel S.g)
  have he : e.hom ≫ kernel.ι S.g = S.f :=
    hS.fIsKernel.conePointUniqueUpToIso_hom_comp (kernelIsKernel S.g) WalkingParallelPair.zero
  have h : closedConeLift S.g S.f S.zero = e.hom ≫ κ := by
    ext p
    apply (cancel_mono
      ((mappingCone S.g).shiftFunctorObjXIso (-1) p (p - 1) (by omega)).hom).mp
    apply homotopyCofiber.ext_to_X S.g (p - 1) p (by change p - 1 + 1 = p; omega)
    · simp only [Category.assoc, comp_f, closedConeLift_projections S.g S.f S.zero p
        (p - 1) (by omega) |>.2, hκ p |>.2]
      exact congrArg (fun t ↦ t.f p) he.symm
    · simp only [Category.assoc, comp_f, closedConeLift_projections S.g S.f S.zero p
        (p - 1) (by omega) |>.1, hκ p |>.1, comp_zero]
  rw [h]
  have := hqκ
  infer_instance

/-- The canonical closed-support construction and its normalization.
Source: Stacks, Tags 0A45, 095L (blueprint: lem-amb-closed-support-hom). -/
lemma closedConeLift_naturality
    {C : Type u} [Category.{v} C] [Abelian C]
    {S P Q S' P' Q' : CochainComplex C ℤ}
    (q : P ⟶ Q) (q' : P' ⟶ Q') (a : S ⟶ P) (a' : S' ⟶ P')
    (ha : a ≫ q = 0) (ha' : a' ≫ q' = 0)
    (s : S ⟶ S') (p : P ⟶ P') (b : Q ⟶ Q')
    (hs : s ≫ a' = a ≫ p) (hp : p ≫ q' = q ≫ b) :
    s ≫ closedConeLift q' a' ha' = closedConeLift q a ha ≫
      (mappingCone.map q q' p b hp.symm)⟦(-1 : ℤ)⟧' := by
  ext n
  dsimp only [comp_f, closedConeLift, shiftFunctor_map_f]
  rw [← Category.assoc, ← comp_f, hs, comp_f, Category.assoc]
  rw [Category.assoc]
  apply congrArg (fun t ↦ a.f n ≫ t)
  change p.f n ≫ (mappingCone.inl q').v n (n + -1) rfl =
    (mappingCone.inl q).v n (n + -1) rfl ≫
      (mappingCone.map q q' p b hp.symm).f (n + -1)
  simp [mappingCone.map]

end CochainComplex


namespace CategoryTheory.Functor
variable {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{w} C]
  {D : Type u'} [Category.{v'} D] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D]

set_option backward.isDefEq.respectTransparency false in
private lemma closedSupport_objQ_naturality (F : C ⥤ D) [F.Additive]
    {I J : CochainComplex C ℤ} [I.IsKInjective] [J.IsKInjective] (f : I ⟶ J) :
    F.rightDerivedFunctor.map (DerivedCategory.Q.map f) ≫
        (F.rightDerivedFunctorObjQIso J).hom =
      (F.rightDerivedFunctorObjQIso I).hom ≫
        DerivedCategory.Q.map ((F.mapHomologicalComplex (.up ℤ)).map f) := by
  let π := HomotopyCategory.quotient C (.up ℤ)
  let H := F.mapHomotopyCategory (.up ℤ)
  have hC : DerivedCategory.Q.map f ≫
      ((DerivedCategory.quotientCompQhIso C).app J).inv =
      ((DerivedCategory.quotientCompQhIso C).app I).inv ≫
        DerivedCategory.Qh.map (π.map f) :=
    (DerivedCategory.quotientCompQhIso C).inv.naturality f
  have hD : DerivedCategory.Qh.map (H.map (π.map f)) ≫
      ((DerivedCategory.quotientCompQhIso D).app
        ((F.mapHomologicalComplex (.up ℤ)).obj J)).hom =
      ((DerivedCategory.quotientCompQhIso D).app
        ((F.mapHomologicalComplex (.up ℤ)).obj I)).hom ≫
          DerivedCategory.Q.map ((F.mapHomologicalComplex (.up ℤ)).map f) :=
    (DerivedCategory.quotientCompQhIso D).hom.naturality
      ((F.mapHomologicalComplex (.up ℤ)).map f)
  have hU : F.rightDerivedFunctor.map (DerivedCategory.Qh.map (π.map f)) ≫
      CategoryTheory.inv (F.rightDerivedFunctorUnit.app (π.obj J)) =
      CategoryTheory.inv (F.rightDerivedFunctorUnit.app (π.obj I)) ≫
        DerivedCategory.Qh.map (H.map (π.map f)) := by
    apply (cancel_mono (F.rightDerivedFunctorUnit.app (π.obj J))).mp
    simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
    have hu := F.rightDerivedFunctorUnit.naturality (π.map f)
    change DerivedCategory.Qh.map (H.map (π.map f)) ≫
      F.rightDerivedFunctorUnit.app (π.obj J) =
      F.rightDerivedFunctorUnit.app (π.obj I) ≫
        F.rightDerivedFunctor.map (DerivedCategory.Qh.map (π.map f)) at hu
    rw [hu, IsIso.inv_hom_id_assoc]
  dsimp only [rightDerivedFunctorObjQIso, Iso.trans_hom, Functor.mapIso_hom,
    Iso.symm_hom, asIso_inv]
  simp only [Category.assoc]
  rw [← F.rightDerivedFunctor.map_comp_assoc, hC, F.rightDerivedFunctor.map_comp,
    Category.assoc, ← Category.assoc _ _
      ((DerivedCategory.quotientCompQhIso D).app
        ((F.mapHomologicalComplex (.up ℤ)).obj J)).hom, hU]
  simp only [Category.assoc]
  rw [hD]

/-- The canonical closed-support construction and its normalization.
Source: Stacks, Tags 0A45, 095L (blueprint: lem-amb-closed-support-hom). -/
noncomputable def closedSupport_resolutionIso (F : C ⥤ D) [F.Additive]
    (K : CochainComplex C ℤ) :
    F.rightDerivedFunctor.obj (DerivedCategory.Q.obj K) ≅
      DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj
        ((CochainComplex.kInjectiveResolutionFunctor.{w} C).obj K)) := by
  have : QuasiIso ((CochainComplex.toKInjectiveResolution.{w} C).app K) :=
    (CochainComplex.monoQuasiIso_toKInjectiveResolution_app C K).2
  exact F.rightDerivedFunctor.mapIso
      (asIso (DerivedCategory.Q.map ((CochainComplex.toKInjectiveResolution.{w} C).app K))) ≪≫
    F.rightDerivedFunctorObjQIso _

/-- The canonical closed-support construction and its normalization.
Source: Stacks, Tags 0A45, 095L (blueprint: lem-amb-closed-support-hom). -/
lemma closedSupport_resolutionIso_naturality (F : C ⥤ D) [F.Additive]
    {K L : CochainComplex C ℤ} (f : K ⟶ L) :
    F.rightDerivedFunctor.map (DerivedCategory.Q.map f) ≫
        (closedSupport_resolutionIso F L).hom =
      (closedSupport_resolutionIso F K).hom ≫
        DerivedCategory.Q.map ((F.mapHomologicalComplex (.up ℤ)).map
          ((CochainComplex.kInjectiveResolutionFunctor.{w} C).map f)) := by
  dsimp only [closedSupport_resolutionIso, Iso.trans_hom, Functor.mapIso_hom, asIso_hom]
  rw [← Category.assoc, ← F.rightDerivedFunctor.map_comp, ← DerivedCategory.Q.map_comp]
  rw [show f ≫ (CochainComplex.toKInjectiveResolution.{w} C).app L =
    (CochainComplex.toKInjectiveResolution.{w} C).app K ≫
      (CochainComplex.kInjectiveResolutionFunctor.{w} C).map f from
      (CochainComplex.toKInjectiveResolution.{w} C).naturality f]
  rw [DerivedCategory.Q.map_comp, F.rightDerivedFunctor.map_comp, Category.assoc,
    closedSupport_objQ_naturality]
  simp only [Category.assoc]
attribute [local irreducible] closedSupport_resolutionIso

set_option backward.isDefEq.respectTransparency false in
private theorem closedSupport_comparison
    (F E B : C ⥤ D) [F.Additive] [E.Additive] [B.Additive]
    (α : F ⟶ E) (τ : E ⟶ B) (hzero : ∀ J, α.app J ≫ τ.app J = 0)
    (hExact : ∀ J, Injective J →
      (ShortComplex.mk (α.app J) (τ.app J) (hzero J)).ShortExact) :
    let q := NatTrans.mapHomologicalComplex τ (ComplexShape.up ℤ)
    ∃ e : ∀ K : CochainComplex C ℤ,
      F.rightDerivedFunctor.obj (DerivedCategory.Q.obj K) ≅
        (DerivedCategory.Q.obj (CochainComplex.mappingCone
          (q.app ((CochainComplex.kInjectiveResolutionFunctor.{w} C).obj K))))⟦(-1 : ℤ)⟧,
      ∀ (K L : CochainComplex C ℤ) (f : K ⟶ L),
        F.rightDerivedFunctor.map (DerivedCategory.Q.map f) ≫ (e L).hom =
          (e K).hom ≫ (shiftFunctor (DerivedCategory D) (-1 : ℤ)).map
            (DerivedCategory.Q.map (CochainComplex.mappingCone.map _ _
              ((E.mapHomologicalComplex (.up ℤ)).map
                ((CochainComplex.kInjectiveResolutionFunctor.{w} C).map f))
              ((B.mapHomologicalComplex (.up ℤ)).map
                ((CochainComplex.kInjectiveResolutionFunctor.{w} C).map f))
              (q.naturality ((CochainComplex.kInjectiveResolutionFunctor.{w} C).map f)).symm)) := by
  let q := NatTrans.mapHomologicalComplex τ (ComplexShape.up ℤ)
  let R := CochainComplex.kInjectiveResolutionFunctor.{w} C
  let a := NatTrans.mapHomologicalComplex α (ComplexShape.up ℤ)
  have hz (K : CochainComplex C ℤ) :
      a.app K ≫ q.app K = 0 := by
    ext n : 1
    exact hzero (K.X n)
  let S (K : CochainComplex C ℤ) :=
    ShortComplex.mk (a.app (R.obj K)) (q.app (R.obj K)) (hz (R.obj K))
  have hS (K : CochainComplex C ℤ) :
      (S K).ShortExact := by
    apply HomologicalComplex.shortExact_of_degreewise_shortExact
    intro n
    exact hExact ((R.obj K).X n) inferInstance
  let κ (K : CochainComplex C ℤ) :=
    CochainComplex.closedConeLift (q.app (R.obj K)) (a.app (R.obj K)) (hz (R.obj K))
  have hκ (K : CochainComplex C ℤ) :
      QuasiIso (κ K) := CochainComplex.closedConeLift_quasiIso (S K) (hS K)
  let e (K : CochainComplex C ℤ) :=
    closedSupport_resolutionIso F K ≪≫
      asIso (DerivedCategory.Q.map (κ K)) ≪≫
        (DerivedCategory.Q.commShiftIso (-1 : ℤ)).app
          (CochainComplex.mappingCone (q.app (R.obj K)))
  refine ⟨e, ?_⟩
  intro K L f
  dsimp only [e, Iso.trans_hom, asIso_hom]
  rw [← Category.assoc, ← Category.assoc,
    closedSupport_resolutionIso_naturality,
    Category.assoc, Category.assoc]
  simp only [Category.assoc]
  apply congrArg (fun t ↦ (closedSupport_resolutionIso F K).hom ≫ t)
  rw [← DerivedCategory.Q.map_comp_assoc]
  have hn := CochainComplex.closedConeLift_naturality
    (q.app (R.obj K)) (q.app (R.obj L)) (a.app (R.obj K)) (a.app (R.obj L))
    (hz (R.obj K)) (hz (R.obj L))
    ((F.mapHomologicalComplex (.up ℤ)).map (R.map f))
    ((E.mapHomologicalComplex (.up ℤ)).map (R.map f))
    ((B.mapHomologicalComplex (.up ℤ)).map (R.map f))
    (a.naturality (R.map f)) (q.naturality (R.map f))
  rw [hn, DerivedCategory.Q.map_comp, Category.assoc]
  apply congrArg (fun t ↦ DerivedCategory.Q.map (κ K) ≫ t)
  exact ((DerivedCategory.Q (C := D)).commShiftIso (-1 : ℤ)).hom.naturality
    (CochainComplex.mappingCone.map (q.app (R.obj K)) (q.app (R.obj L))
      ((E.mapHomologicalComplex (.up ℤ)).map (R.map f))
      ((B.mapHomologicalComplex (.up ℤ)).map (R.map f)) (q.naturality (R.map f)).symm)


end CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

/-- The canonical closed-support construction and its normalization.
Source: Stacks, Tags 0A45, 095L (blueprint: lem-amb-closed-support-hom). -/
theorem closedSupportHom_globalSections_natural {A : Type (u + 1)} [CommRing A]
    {L K : Scheme.{u}} (m : K ⟶ L)
    {F F' : Sheaf L.smallEtaleTopology (ModuleCat.{u + 1} A)} (k : F ⟶ F') :
    (Sheaf.Γ L.smallEtaleTopology (ModuleCat.{u + 1} A)).map k ≫
      globalSectionsUpperStarMap (ModuleCat.{u + 1} A) m F' =
    globalSectionsUpperStarMap (ModuleCat.{u + 1} A) m F ≫
      (Sheaf.Γ K.smallEtaleTopology (ModuleCat.{u + 1} A)).map
        ((upperStar (ModuleCat.{u + 1} A) m).map k) := by
  unfold globalSectionsUpperStarMap
  rw [Category.assoc, Category.assoc,
    (Sheaf.ΓNatIsoSheafSections L.smallEtaleTopology (ModuleCat.{u + 1} A)
      terminalIsTerminal).hom.naturality_assoc k]
  have hn := (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) m).unit.naturality k
  simp only [Functor.id_map] at hn
  rw [← Functor.map_comp_assoc, hn, Functor.map_comp]
  simp only [Category.assoc]
  rw [← (Sheaf.ΓNatIsoSheafSections K.smallEtaleTopology (ModuleCat.{u + 1} A)
      terminalIsTerminal).inv.naturality]
  congr 1
  congr 1
  have hu := ((upperStar (ModuleCat.{u + 1} A) m).map k).hom.naturality
    (PreservesTerminal.iso m.Etale).inv.op
  simp only [Functor.comp_map, Functor.flip_obj_map, ObjectProperty.ι_map]
  erw [lowerStar_map_hom_app]
  simpa only [Category.assoc] using! congrArg (fun a ↦ a ≫
    (Sheaf.ΓNatIsoSheafSections K.smallEtaleTopology (ModuleCat.{u + 1} A)
      terminalIsTerminal).inv.app ((upperStar (ModuleCat.{u + 1} A) m).obj F')) hu.symm

/-- Pullback of global sections as a natural transformation on sheaves.
Source: Stacks, Tag 03Q1 (blueprint: lem-amb-closed-support-hom). -/
noncomputable def closedSupportSectionsPullback (A : Type (u + 1)) [CommRing A]
    {V T : Scheme.{u}} (v : V ⟶ T) :
    Sheaf.Γ T.smallEtaleTopology (ModuleCat.{u + 1} A) ⟶
      upperStar (ModuleCat.{u + 1} A) v ⋙ Sheaf.Γ V.smallEtaleTopology (ModuleCat.{u + 1} A) where
  app J := globalSectionsUpperStarMap (ModuleCat.{u + 1} A) v J
  naturality _ _ f := closedSupportHom_globalSections_natural v f

/-- The component of the canonical section-pullback transformation.
Source: Stacks, Tag 03Q1 (blueprint: lem-amb-closed-support-hom). -/
theorem closedSupportSectionsPullback_app (A : Type (u + 1)) [CommRing A]
    {V T : Scheme.{u}} (v : V ⟶ T)
    (J : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    (closedSupportSectionsPullback A v).app J =
      globalSectionsUpperStarMap (ModuleCat.{u + 1} A) v J := rfl

set_option backward.isDefEq.respectTransparency false in
/-- Ordinary global derived Hom from `i_* A_D` is the shifted cone of restriction of
ordinary derived global sections to the complementary open. The existential `q` is fixed
in every degree by the existing global-section pullback map, so is not an arbitrary arrow.
The cone is computed on the functorial K-injective resolution, and the final equation is
naturality in every map of complexes. Both sides invert quasi-isomorphisms, hence this
also expresses naturality on the derived category. No boundedness is assumed.

Source: blueprint sec-smooth-purity/sk-prop-sf-cbc/lem-amb-closed-support-hom.md
(blueprint: lem-amb-closed-support-hom).

Proof: Construct the restriction natural transformation on sheaves and map it to complexes.
The underived closed-support Hom sequence is short exact on each injective sheaf, so applying
it to the functorial resolution gives a short exact sequence of complexes. The explicit map
from its first term to the shifted cone is inclusion in the source summand. The existing
kernel-to-shifted-cone theorem proves it is a quasi-isomorphism, and the formula for cone maps
proves its naturality. The concrete K-injective computation of the right derived functor,
together with the resolution quasi-isomorphism, identifies the source with ordinary derived
Hom. Naturality of its unit, of the resolution, and of the shift comparison gives the stated
equation. This concrete formulation needs no separate derived computation of the open term.
-/
theorem closedSupportHom (A : Type (u + 1)) [CommRing A]
    {D V T : Scheme.{u}} (i : D ⟶ T) [IsClosedImmersion i]
    (v : V ⟶ T) [IsOpenImmersion v]
    (hcomp : Set.range v.base = (Set.range i.base)ᶜ) :
    ∃ q : (Sheaf.Γ T.smallEtaleTopology (ModuleCat.{u + 1} A)).mapHomologicalComplex
        (ComplexShape.up ℤ) ⟶
      (upperStar (ModuleCat.{u + 1} A) v ⋙
        Sheaf.Γ V.smallEtaleTopology (ModuleCat.{u + 1} A)).mapHomologicalComplex
          (ComplexShape.up ℤ),
      (∀ (K : CochainComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ)
        (n : ℤ), (q.app K).f n = globalSectionsUpperStarMap (ModuleCat.{u + 1} A) v (K.X n)) ∧
      ∃ e : ∀ K : CochainComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ,
        (((linearCoyoneda A (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))).obj
          (op ((lowerStar (ModuleCat.{u + 1} A) i).obj
            ((constantSheaf D.smallEtaleTopology (ModuleCat.{u + 1} A)).obj
              (ModuleCat.of A A))))).rightDerivedFunctor).obj (DerivedCategory.Q.obj K) ≅
        (DerivedCategory.Q.obj (CochainComplex.mappingCone
          (q.app ((CochainComplex.kInjectiveResolutionFunctor
            (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))).obj K))))⟦(-1 : ℤ)⟧,
      ∀ (K L : CochainComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ)
        (f : K ⟶ L),
        (((linearCoyoneda A (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))).obj
          (op ((lowerStar (ModuleCat.{u + 1} A) i).obj
            ((constantSheaf D.smallEtaleTopology (ModuleCat.{u + 1} A)).obj
              (ModuleCat.of A A))))).rightDerivedFunctor).map (DerivedCategory.Q.map f) ≫
          (e L).hom =
        (e K).hom ≫ (shiftFunctor (DerivedCategory (ModuleCat.{u + 1} A)) (-1 : ℤ)).map
          (DerivedCategory.Q.map (CochainComplex.mappingCone.map _ _
            (((Sheaf.Γ T.smallEtaleTopology (ModuleCat.{u + 1} A)).mapHomologicalComplex
              (ComplexShape.up ℤ)).map
              ((CochainComplex.kInjectiveResolutionFunctor _).map f))
            (((upperStar (ModuleCat.{u + 1} A) v ⋙
              Sheaf.Γ V.smallEtaleTopology (ModuleCat.{u + 1} A)).mapHomologicalComplex
                (ComplexShape.up ℤ)).map
                ((CochainComplex.kInjectiveResolutionFunctor _).map f))
            (q.naturality ((CochainComplex.kInjectiveResolutionFunctor _).map f)).symm)) := by
  let τ := closedSupportSectionsPullback A v
  let q : (Sheaf.Γ T.smallEtaleTopology (ModuleCat.{u + 1} A)).mapHomologicalComplex
        (ComplexShape.up ℤ) ⟶
      (upperStar (ModuleCat.{u + 1} A) v ⋙
        Sheaf.Γ V.smallEtaleTopology (ModuleCat.{u + 1} A)).mapHomologicalComplex
          (ComplexShape.up ℤ) := NatTrans.mapHomologicalComplex τ (ComplexShape.up ℤ)
  have hq : ∀ (K : CochainComplex (Sheaf T.smallEtaleTopology
      (ModuleCat.{u + 1} A)) ℤ) (n : ℤ),
      (q.app K).f n = globalSectionsUpperStarMap (ModuleCat.{u + 1} A) v (K.X n) := by
    intro K n
    exact NatTrans.mapHomologicalComplex_app_f τ (ComplexShape.up ℤ) K n
  let F := (linearCoyoneda A (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))).obj
    (op ((lowerStar (ModuleCat.{u + 1} A) i).obj
      ((constantSheaf D.smallEtaleTopology (ModuleCat.{u + 1} A)).obj (ModuleCat.of A A))))
  obtain ⟨α, hzero, hExact⟩ := closedSupportHomSequence A i v hcomp τ (fun _ ↦ rfl)
  refine ⟨q, hq, ?_⟩
  have : (Sheaf.Γ T.smallEtaleTopology (ModuleCat.{u + 1} A)).Additive :=
    (constantSheafΓAdj T.smallEtaleTopology (ModuleCat.{u + 1} A)).right_adjoint_additive
  have : (Sheaf.Γ V.smallEtaleTopology (ModuleCat.{u + 1} A)).Additive :=
    (constantSheafΓAdj V.smallEtaleTopology (ModuleCat.{u + 1} A)).right_adjoint_additive
  exact CategoryTheory.Functor.closedSupport_comparison F
    (Sheaf.Γ T.smallEtaleTopology (ModuleCat.{u + 1} A))
    (upperStar (ModuleCat.{u + 1} A) v ⋙
      Sheaf.Γ V.smallEtaleTopology (ModuleCat.{u + 1} A)) α τ hzero hExact

end AlgebraicGeometry.Etale
