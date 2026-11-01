/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.Algebra.Homology.DerivedInternalHom
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.RingTheory.Localization.Away.Basic
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed
public import Mathlib.Algebra.Homology.Monoidal
public import WeilConjectures.Algebra.Homology.HomComplexUnitEvaluationIsIso
public import WeilConjectures.Algebra.Homology.HomComplexUnitEvaluationComm
public import WeilConjectures.Algebra.Homology.HomComplexComponents
public import WeilConjectures.Algebra.Homology.HomComplexUnitEvaluationNaturality
import WeilConjectures.Algebra.Homology.HomComplexUnitEvaluationNaturality
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.Algebra.Homology.DerivedInternalHom
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.RingTheory.Localization.Away.Basic
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed
import Mathlib.Algebra.Homology.Monoidal
import WeilConjectures.Algebra.Homology.HomComplexUnitEvaluationIsIso
import WeilConjectures.Algebra.Homology.HomComplexUnitEvaluationComm
import WeilConjectures.Algebra.Homology.HomComplexComponents
import WeilConjectures.ProperBaseChange.RingedCechCompletionUnitIdempotence
import WeilConjectures.ProperBaseChange.RingedInternalHomContravariantExact
import WeilConjectures.Algebra.Homology.DerivedInternalHomShiftLeft
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Mathlib.CategoryTheory.Sites.LocalProperties
import WeilConjectures.FromJoel.Algebra.Homology.Embedding.ComplementaryTrunc
import WeilConjectures.ProperBaseChange.ExtendedCechUnitIsoImpliesComplete
import WeilConjectures.CategoryTheory.Ringed.RingedInternalHomExactRestrictionSupplement

/-!
# Core reflector properties for the extended Cech completion

Source: Stacks Project, algebraization.tex, Tags 099B and 099F
(blueprint: lem-weil-pbc-extended-cech-reflector-core).

The remaining finite localization-filtration and orthogonality argument is isolated here.
-/

@[expose] public noncomputable section

universe u w

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory


private def homUnitOnRepresentatives
    {A D : Type*} [Category A] [Category D]
    (Q : A ⥤ D) (I : A ⥤ A) (eta : 𝟭 A ⟶ I)
    (H : Aᵒᵖ ⥤ A ⥤ A) (G : Dᵒᵖ × D ⥤ D) (U : A)
    (a : H.obj (op U) ≅ 𝟭 A)
    (c : Q.op.prod Q ⋙ G ≅ (𝟭 Aᵒᵖ).prod I ⋙ Functor.uncurry.obj H ⋙ Q) :
    Q ⋙ 𝟭 D ⟶ Q ⋙ (Functor.curry.obj G).obj (op (Q.obj U)) where
  app M := Q.map (eta.app M) ≫ Q.map (a.inv.app (I.obj M)) ≫ c.inv.app (op U, M)
  naturality {M N} f := by
    have hc := c.inv.naturality (X := (op U, M)) (Y := (op U, N)) (𝟙 _, f)
    have ha := a.inv.naturality (I.map f)
    have he := eta.naturality f
    dsimp only [Functor.comp_map, Functor.prod_map, Functor.id_map, Functor.op_map,
      Functor.curry_obj_obj_map, Functor.uncurry_obj_map] at hc ha he ⊢
    dsimp only [Functor.prod_obj, Functor.id_obj] at hc
    simp only [Functor.map_id, NatTrans.id_app, Category.id_comp, op_id, unop_id] at hc
    have he' : Q.map f ≫ Q.map (eta.app N) = Q.map (eta.app M) ≫ Q.map (I.map f) := by
      simpa only [← Q.map_comp] using congrArg Q.map he
    have ha' : Q.map (I.map f) ≫ Q.map (a.inv.app (I.obj N)) =
        Q.map (a.inv.app (I.obj M)) ≫ Q.map ((H.obj (op U)).map (I.map f)) := by
      simpa only [← Q.map_comp] using congrArg Q.map ha
    rw [← Category.assoc, he']
    simp only [Category.assoc]
    rw [← Category.assoc (Q.map (I.map f)), ha']
    simp only [Category.assoc]
    rw [hc]

set_option maxHeartbeats 1200000 in
-- Naturality compares the product-localization factorization with chosen representatives.
private theorem completion_unit_natural_core
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
    homUnitOnRepresentatives Q I η (homComplexFunctor (R := O))
      H (ringedSiteRingComplex O) a c
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
    simp only [ringedDerivedHomUnit, t, homUnitOnRepresentatives, a, e, Q, I, η, c,
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


private def derivedHomUnitIso
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (O : Sheaf J CommRingCat.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))] :
    𝟭 (ringedSiteDerived O) ≅ ringedCechCompletionFunctor O (ringedSiteRingComplex O) := by
  have hdelta (E : ringedSiteDerived O) : IsIso (ringedDerivedHomUnit O E) := by
    let A := SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)
    let : IsGrothendieckAbelian.{u} A := SheafOfModules.isGrothendieckAbelian _
    have : QuasiIso ((CochainComplex.toKInjectiveResolution.{u} A).app
        (DerivedCategory.Q.objPreimage E)) :=
      (CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{u} A _).2
    let e := DerivedCategory.Q.objObjPreimageIso E
    dsimp only [ringedDerivedHomUnit]
    repeat' apply IsIso.comp_isIso'
    all_goals first | infer_instance | skip
    change IsIso ((derivedInternalHom J O).mapIso ((Iso.refl _).prod e)).hom
    infer_instance
  refine NatIso.ofComponents (fun E ↦ @asIso _ _ _ _ (ringedDerivedHomUnit O E)
    (hdelta E)) ?_
  intro E E' g
  have hn := completion_unit_natural_core O (ringedSiteRingComplex O) (𝟙 _) E E' g
  simp only [ringedCechCompletionUnit, Functor.map_id, op_id] at hn
  change (ringedDerivedHomUnit O E ≫ (derivedInternalHom J O).map (𝟙 _)) ≫ _ =
    g ≫ ringedDerivedHomUnit O E' ≫ (derivedInternalHom J O).map (𝟙 _) at hn
  simpa only [Functor.map_id, Category.comp_id, asIso_hom, Functor.id_map] using hn.symm

attribute [local irreducible] derivedInternalHom

end CategoryTheory
