/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NE
-/
module

public import Sheaf.CategoryTheory.LocallyDerivedRingedIdealComplete
public import Sheaf.CategoryTheory.LocalExtendedCechDescription
public import Sheaf.CategoryTheory.RingedCompletionUnit
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Sheaf.Algebra.Homology.HomComplexUnitEvaluationNaturality
import Sheaf.Algebra.Homology.RhomGlobalSections
import Sheaf.Algebra.Homology.DerivedInternalHom
import Sheaf.Algebra.Homology.RingedInternalHomExactRestriction
import Sheaf.CategoryTheory.RingedSiteCompleteElementsIdeal
import Sheaf.CategoryTheory.SiteCoveringAxioms
import Sheaf.CategoryTheory.SpecialCocontinuousSheafEquivalence
import Sheaf.Paper.RingComplexFunctorial
import Sheaf.Paper.RingedLocalizationRHomCalculus

/-!
# Global extended Cech model and its derived completion unit

Source: Stacks Project, algebraization.tex, Tags 099E and 099F
(blueprint: lem-weil-pbc-extended-cech-completion-model).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace CategoryTheory

set_option maxHeartbeats 1200000 in
-- Descending evaluation compares several expanded product-localization functors.
set_option backward.isDefEq.respectTransparency false in
private theorem completion_unit_natural
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (O : Sheaf J CommRingCat.{u})
    [HasDerivedCategory.{w} (ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))]
    (K : ringedSiteComplex O) (ε : K ⟶ ringedSiteRingComplex O)
    (E E' : ringedSiteDerived O) (g : E ⟶ E') :
    ringedCechCompletionUnit O K ε E ≫ (ringedCechCompletionFunctor O K).map g =
      g ≫ ringedCechCompletionUnit O K ε E' := by
  let A := ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)
  let : IsGrothendieckAbelian.{u} A := SheafOfModules.isGrothendieckAbelian _
  let Q := DerivedCategory.Q (C := A)
  let I := CochainComplex.kInjectiveResolutionFunctor.{u} A
  let η := CochainComplex.toKInjectiveResolution.{u} A
  let H := derivedInternalHom J O
  let F := ringedCechCompletionFunctor O (ringedSiteRingComplex O)
  let c := Localization.fac
    ((𝟭 _).prod I ⋙ Functor.uncurry.obj (homComplexFunctor (R := O)) ⋙ Q)
    (derivedInternalHom_inverts J O I η (fun M ↦
      ⟨(CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{u} _ M).2,
        CochainComplex.isKInjective_kInjectiveResolutionFunctor_obj.{u} _ M⟩))
    (Q.op.prod Q)
  let a : (homComplexFunctor (R := O)).obj
      (Opposite.op (ringedSiteRingComplex O)) ≅ 𝟭 _ :=
    NatIso.ofComponents (ringedHomUnitEvaluationIso O) (by
      intro M N f
      apply HomologicalComplex.hom_ext
      intro n
      exact homComplex_unit_evaluation_naturality J O f n)
  let t : Q ⋙ 𝟭 _ ⟶ Q ⋙ F :=
    { app := fun M ↦ Q.map (η.app M) ≫
        Q.map (a.inv.app (I.obj M)) ≫ (c.inv.app (Opposite.op (ringedSiteRingComplex O), M))
      naturality := by
        intro M N f
        dsimp only [Functor.comp_map, Functor.id_map, F, ringedCechCompletionFunctor]
        have hc := c.inv.naturality
          (X := (Opposite.op (ringedSiteRingComplex O), M))
          (Y := (Opposite.op (ringedSiteRingComplex O), N)) (𝟙 _, f)
        have ha := a.inv.naturality (I.map f)
        have hη := η.naturality f
        dsimp at hc ha hη
        simp only [Functor.map_id, NatTrans.id_app, Category.id_comp, op_id] at hc
        change Q.map f ≫ (Q.map (η.app N) ≫ Q.map (a.inv.app (I.obj N)) ≫
            c.inv.app (Opposite.op (ringedSiteRingComplex O), N)) =
          (Q.map (η.app M) ≫ Q.map (a.inv.app (I.obj M)) ≫
            c.inv.app (Opposite.op (ringedSiteRingComplex O), M)) ≫
              H.map
                (X := (Opposite.op (Q.obj (ringedSiteRingComplex O)), Q.obj M))
                (Y := (Opposite.op (Q.obj (ringedSiteRingComplex O)), Q.obj N))
                (𝟙 _, Q.map f)
        have hη' : Q.map f ≫ Q.map (η.app N) = Q.map (η.app M) ≫ Q.map (I.map f) := by
          simpa only [← Q.map_comp] using congrArg Q.map hη
        have ha' : Q.map (I.map f) ≫ Q.map (a.inv.app (I.obj N)) =
            Q.map (a.inv.app (I.obj M)) ≫
              Q.map ((homComplexFunctor (R := O)).obj
                (Opposite.op (ringedSiteRingComplex O)) |>.map (I.map f)) := by
          simpa only [← Q.map_comp] using congrArg Q.map ha
        rw [← Category.assoc, hη']
        simp only [Category.assoc]
        rw [← Category.assoc (Q.map (I.map f)), ha']
        simp only [Category.assoc]
        rw [hc]
        rfl }
  let W := HomologicalComplex.quasiIso A (ComplexShape.up ℤ)
  let full := Localization.fullyFaithfulWhiskeringLeft Q W (DerivedCategory A)
  let d : 𝟭 (DerivedCategory A) ⟶ F := full.preimage t
  have hd (M : CochainComplex A ℤ) : d.app (Q.obj M) = t.app M :=
    congrArg (fun z ↦ z.app M) (full.map_preimage t)
  have hu (X : ringedSiteDerived O) : ringedDerivedHomUnit O X = d.app X := by
    let e := Q.objObjPreimageIso X
    have hn := d.naturality e.hom
    dsimp at hn
    rw [← cancel_epi e.hom]
    rw [hn, hd]
    simp only [ringedDerivedHomUnit, t, a, e, Q, I, η, c,
      Category.assoc, Iso.hom_inv_id_assoc]
    rfl
  have hn := d.naturality g
  change (ringedDerivedHomUnit O E ≫ H.map
      (X := (Opposite.op (Q.obj (ringedSiteRingComplex O)), E))
      (Y := (Opposite.op (Q.obj K), E)) ((Q.map ε).op, 𝟙 E)) ≫
      H.map (X := (Opposite.op (Q.obj K), E))
        (Y := (Opposite.op (Q.obj K), E')) (𝟙 _, g) =
    g ≫ ringedDerivedHomUnit O E' ≫ H.map
      (X := (Opposite.op (Q.obj (ringedSiteRingComplex O)), E'))
      (Y := (Opposite.op (Q.obj K), E')) ((Q.map ε).op, 𝟙 E')
  have hs : H.map
      (X := (Opposite.op (Q.obj (ringedSiteRingComplex O)), E))
      (Y := (Opposite.op (Q.obj K), E)) ((Q.map ε).op, 𝟙 E) ≫
      H.map (X := (Opposite.op (Q.obj K), E))
        (Y := (Opposite.op (Q.obj K), E')) (𝟙 _, g) =
      H.map (X := (Opposite.op (Q.obj (ringedSiteRingComplex O)), E))
        (Y := (Opposite.op (Q.obj (ringedSiteRingComplex O)), E')) (𝟙 _, g) ≫
      H.map (X := (Opposite.op (Q.obj (ringedSiteRingComplex O)), E'))
        (Y := (Opposite.op (Q.obj K), E')) ((Q.map ε).op, 𝟙 E') := by
    rw [← H.map_comp, ← H.map_comp]
    congr 1
    ext <;> simp
  rw [Category.assoc, hs, ← Category.assoc, hu E, hu E']
  change (d.app E ≫ F.map g) ≫ _ = _
  rw [← hn, Category.assoc]
  rfl

set_option backward.isDefEq.respectTransparency false in
private theorem precomp_bijective_of_internalHom_isIso
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (O : Sheaf J CommRingCat.{u})
    [HasDerivedCategory.{w} (ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))]
    {X Y L : ringedSiteDerived O} (f : X ⟶ Y)
    (hf : IsIso ((derivedInternalHom J O).map
      (X := (Opposite.op Y, L)) (Y := (Opposite.op X, L)) (f.op, 𝟙 L))) :
    Function.Bijective (fun h : Y ⟶ L ↦ f ≫ h) := by
  obtain ⟨e, he⟩ := rhom_global_sections J O
  let H := derivedInternalHom J O
  let Γ := ringedSiteZerothHypercohomology J O
  let t := H.map (X := (Opposite.op Y, L)) (Y := (Opposite.op X, L)) (f.op, 𝟙 L)
  have : IsIso t := hf
  let b : (Y ⟶ L) ≃ (X ⟶ L) :=
    (e (Opposite.op Y, L)).symm.toEquiv.trans
      ((Γ.mapIso (asIso t)).addCommGroupIsoToAddEquiv.toEquiv.trans (e (Opposite.op X, L)).toEquiv)
  have hb (h : Y ⟶ L) : b h = f ≫ h := by
    have hn := he (Opposite.op Y, L) (Opposite.op X, L) (f.op, 𝟙 L)
      ((e (Opposite.op Y, L)).symm h)
    change e (Opposite.op X, L) (Γ.map t ((e (Opposite.op Y, L)).symm h)) = f ≫ h
    simpa only [Quiver.Hom.unop_op, AddEquiv.apply_symm_apply, Category.comp_id] using hn
  have : (fun h : Y ⟶ L ↦ f ≫ h) = b := funext (fun h ↦ (hb h).symm)
  rw [this]
  exact b.bijective

open CategoryTheory.Pretriangulated.Opposite in
set_option backward.isDefEq.respectTransparency false in
private theorem precomp_bijective_of_cone_internalHom_zero
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (O : Sheaf J CommRingCat.{u})
    [HasDerivedCategory.{w} (ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))]
    (T : Triangle (ringedSiteDerived O)) (hT : T ∈ distTriang (ringedSiteDerived O))
    (L : ringedSiteDerived O)
    (hz : IsZero ((derivedInternalHom J O).obj (Opposite.op T.obj₃, L))) :
    Function.Bijective (fun h : T.obj₂ ⟶ L ↦ T.mor₁ ≫ h) := by
  let F := (Functor.curry.obj (derivedInternalHom J O)).flip.obj L
  obtain ⟨s, hs⟩ := (ringedInternalHom_exact J O).2 L
  let : F.CommShift ℤ := s
  let : F.IsTriangulated := hs
  let S := (Pretriangulated.triangleOpEquivalence (ringedSiteDerived O)).functor.obj
    (Opposite.op T)
  have hS : S ∈ distTriang (ringedSiteDerived O)ᵒᵖ :=
    Pretriangulated.op_distinguished T hT
  have hz' : IsZero ((F.mapTriangle.obj S).obj₁) := hz
  have hi := (Triangle.isZero₁_iff_isIso₂ (F.mapTriangle.obj S)
    (F.map_distinguished S hS)).1 hz'
  apply precomp_bijective_of_internalHom_isIso O T.mor₁
  exact hi

private theorem unit_isIso_of_complete_universal
    {D : Type*} [Category D] (P : D → Prop) (F : D ⥤ D)
    (η : ∀ E, E ⟶ F.obj E)
    (hc : ∀ E, P (F.obj E))
    (hu : ∀ E L, P L → Function.Bijective (fun h : F.obj E ⟶ L ↦ η E ≫ h))
    (E : D) (hE : P E) : IsIso (η E) := by
  obtain ⟨r, hr⟩ := (hu E E hE).2 (𝟙 E)
  have hs : r ≫ η E = 𝟙 (F.obj E) := by
    apply (hu E (F.obj E) (hc E)).1
    simp only [← Category.assoc, hr, Category.id_comp, Category.comp_id]
  exact ⟨⟨r, hr, hs⟩⟩

/-- The global augmented model exists.
Source: Stacks Project, algebraization.tex, Tag 099E.
(blueprint: lem-weil-pbc-extended-cech-global-model).

Proof: construct on the finite-generator subsite using the functorial ring complex, then sheafify
and glue the local choices using the recorded site equivalence and exact sheafification. The
remaining comparison between sequential and fraction localization is isolated in this theorem.
-/
theorem exists_ringedExtendedCech_global_model
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    (O : Sheaf J CommRingCat.{u})
    [HasDerivedCategory.{w} (ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))]
    [∀ U : C, HasDerivedCategory.{w} (ringedSiteModules.{u}
      ((sheafCompose (J.over U) (forget₂ CommRingCat RingCat)).obj (O.over U)))]
    (I : ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))
    (ι : I ⟶ SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))
    [Mono ι] [I.IsFiniteType] :
    ∃ (K : ringedSiteComplex O) (ε : K ⟶ ringedSiteRingComplex O),
      HasLocalExtendedCechDescription O I ι K ε := by
  sorry

/-- The internal-Hom reflector properties of every local extended Cech model.
Source: Stacks Project, algebraization.tex, Tags 099B and 099F.
(blueprint: lem-weil-pbc-extended-cech-reflector-properties).

Proof: on each finite-generator slice, contract the localized extended Cech complex, filter the
augmentation cone by its positive localization terms, and use the internal-Hom tensor identity
to prove orthogonality. Globalize by restriction and use zeroth derived global sections for the
mapping bijection; the unit isomorphism follows from the resulting universal property.
-/
theorem ringedExtendedCech_reflector_properties
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    (O : Sheaf J CommRingCat.{u})
    [HasDerivedCategory.{w} (ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))]
    [∀ U : C, HasDerivedCategory.{w} (ringedSiteModules.{u}
      ((sheafCompose (J.over U) (forget₂ CommRingCat RingCat)).obj (O.over U)))]
    (I : ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))
    (ι : I ⟶ SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))
    [Mono ι] [I.IsFiniteType]
    (K : ringedSiteComplex O) (ε : K ⟶ ringedSiteRingComplex O)
    (hK : HasLocalExtendedCechDescription O I ι K ε) :
    (∀ E : ringedSiteDerived O,
      IsLocallyDerivedRingedIdealComplete O I ι ((ringedCechCompletionFunctor O K).obj E)) ∧
    (∀ (E E' : ringedSiteDerived O) (g : E ⟶ E'),
      ringedCechCompletionUnit O K ε E ≫ (ringedCechCompletionFunctor O K).map g =
        g ≫ ringedCechCompletionUnit O K ε E') ∧
    (∀ (E L : ringedSiteDerived O), IsLocallyDerivedRingedIdealComplete O I ι L →
      Function.Bijective
        (fun h : (ringedCechCompletionFunctor O K).obj E ⟶ L ↦
          ringedCechCompletionUnit O K ε E ≫ h)) ∧
    (∀ E : ringedSiteDerived O, IsLocallyDerivedRingedIdealComplete O I ι E →
      IsIso (ringedCechCompletionUnit O K ε E)) := by
  sorry

/-- Global model plus its derived completion reflector.
Source: Stacks Project, algebraization.tex, Tags 099E and 099F.
(blueprint: lem-weil-pbc-extended-cech-completion-model).
-/
theorem exists_ringedExtendedCech_completion_model
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    (O : Sheaf J CommRingCat.{u})
    [HasDerivedCategory.{w} (ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))]
    [∀ U : C, HasDerivedCategory.{w} (ringedSiteModules.{u}
      ((sheafCompose (J.over U) (forget₂ CommRingCat RingCat)).obj (O.over U)))]
    (I : ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))
    (ι : I ⟶ SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))
    [Mono ι] [I.IsFiniteType] :
    (∃ (K : ringedSiteComplex O) (ε : K ⟶ ringedSiteRingComplex O),
      HasLocalExtendedCechDescription O I ι K ε) ∧
    ∀ (K : ringedSiteComplex O) (ε : K ⟶ ringedSiteRingComplex O),
      HasLocalExtendedCechDescription O I ι K ε →
        (∀ E : ringedSiteDerived O,
          IsLocallyDerivedRingedIdealComplete O I ι ((ringedCechCompletionFunctor O K).obj E)) ∧
        (∀ (E E' : ringedSiteDerived O) (g : E ⟶ E'),
          ringedCechCompletionUnit O K ε E ≫ (ringedCechCompletionFunctor O K).map g =
            g ≫ ringedCechCompletionUnit O K ε E') ∧
        (∀ (E L : ringedSiteDerived O), IsLocallyDerivedRingedIdealComplete O I ι L →
          Function.Bijective
            (fun h : (ringedCechCompletionFunctor O K).obj E ⟶ L ↦
              ringedCechCompletionUnit O K ε E ≫ h)) ∧
        (∀ E : ringedSiteDerived O, IsLocallyDerivedRingedIdealComplete O I ι E →
          IsIso (ringedCechCompletionUnit O K ε E)) := by
  obtain ⟨K, ε, hK⟩ := exists_ringedExtendedCech_global_model J O I ι
  refine ⟨⟨K, ε, hK⟩, ?_⟩
  intro K' ε' hK'
  exact ringedExtendedCech_reflector_properties J O I ι K' ε' hK'

end CategoryTheory
