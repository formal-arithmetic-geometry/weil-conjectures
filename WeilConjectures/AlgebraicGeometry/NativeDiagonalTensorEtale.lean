/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FieldRestrictionExteriorProduct
public import Mathlib.RingTheory.TensorProduct.Maps

import all WeilConjectures.AlgebraicGeometry.FieldRestrictionExteriorProduct
import all Mathlib.RingTheory.TensorProduct.Maps
import all Mathlib.LinearAlgebra.TensorProduct.Tower
import WeilConjectures.AlgebraicGeometry.DerivedScalarRestrictionTensor
import WeilConjectures.Mathlib.CategoryTheory.Conj
import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategory
import all WeilConjectures.Algebra.Homology.Site.SiteDerivedTensorDescent
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all Mathlib.CategoryTheory.Sites.ConstantSheaf
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import all Mathlib.Algebra.Category.Ring.FilteredColimits
import all Mathlib.Algebra.Category.Ring.Limits
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import all WeilConjectures.Mathlib.Algebra.Homology.Bifunctor
import all WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.CategoryTheory.Sites.SheafComposeMonoidalPresheaf
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic

/-! # The diagonal retract of the native small-etale tensor

This is the sheaf case of the termwise separability argument in the first paragraph of
`lem-pur-ordinary-kunneth-finite-ring.proof.md`.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped TensorProduct

namespace Native
open scoped ModuleCat.Algebra
variable (F B : Type u) [Field F] [Field B] [Algebra F B]
private theorem ordinarySection_naturality₂ (e : B ⊗[F] B)
    (hd : ∀ b : B, (b ⊗ₜ[F] (1 : B) - (1 : B) ⊗ₜ[F] b) * e = 0)
    {M M' N N' : ModuleCat.{u} B} (f : M ⟶ M') (g : N ⟶ N') :
    (U F B).map (f ⊗ₘ g) ≫ ((ordinarySection F B e hd).app M').app N' =
      ((ordinarySection F B e hd).app M).app N ≫
        ((U F B).map f ⊗ₘ (U F B).map g) := by
  apply ModuleCat.hom_ext
  exact (section_naturality F B M N e hd f.hom g.hom).symm
variable {S : Type v} [Category S]
private noncomputable def presheafSection
    (e : B ⊗[F] B)
    (hd : ∀ b : B, (b ⊗ₜ[F] (1 : B) - (1 : B) ⊗ₜ[F] b) * e = 0)
    (M N : S ⥤ ModuleCat.{u} B) :
    (M ⊗ N) ⋙ U F B ⟶ (M ⋙ U F B) ⊗ (N ⋙ U F B) where
  app X := ((ordinarySection F B e hd).app (M.obj X)).app (N.obj X)
  naturality _X _Y f := ordinarySection_naturality₂ F B e hd (M.map f) (N.map f)
private theorem presheafSection_split
    (e : B ⊗[F] B) (hμ : Algebra.TensorProduct.lmul' F e = 1)
    (hd : ∀ b : B, (b ⊗ₜ[F] (1 : B) - (1 : B) ⊗ₜ[F] b) * e = 0)
    (M N : S ⥤ ModuleCat.{u} B) :
    presheafSection F B e hd M N ≫ Functor.LaxMonoidal.μ
      ((Functor.whiskeringRight S _ _).obj (U F B)) M N = 𝟙 _ := by
  apply NatTrans.ext
  funext X
  exact congr_app (congr_app (ordinarySection_split F B e hμ hd) (M.obj X)) (N.obj X)
end Native

namespace Native
open scoped ModuleCat.Algebra
variable (F B : Type (u + 1)) [Field F] [Field B] [Algebra F B]
variable {S : Type v} [Category S]
private noncomputable def presheafActionRing
    (M N : S ⥤ ModuleCat.{u + 1} B) :
    (B ⊗[F] B) →+* End
      ((M ⋙ ModuleCat.restrictScalars.{u + 1} (algebraMap F B)) ⊗
        (N ⋙ ModuleCat.restrictScalars.{u + 1} (algebraMap F B))) where
  toFun x :=
    { app X := ModuleCat.ofHom (act F B (M.obj X) (N.obj X) x)
      naturality X Y f := by
        apply ModuleCat.hom_ext
        exact (action_naturality F B (M.obj X) (N.obj X) x
          (M.map f).hom (N.map f).hom).symm }
  map_zero' := by
    apply NatTrans.ext
    funext X
    apply ModuleCat.hom_ext
    exact (act F B (M.obj X) (N.obj X)).map_zero
  map_one' := by
    apply NatTrans.ext
    funext X
    apply ModuleCat.hom_ext
    exact (action F B (M.obj X) (N.obj X)).map_one
  map_add' x y := by
    apply NatTrans.ext
    funext X
    apply ModuleCat.hom_ext
    exact (act F B (M.obj X) (N.obj X)).map_add x y
  map_mul' x y := by
    apply NatTrans.ext
    funext X
    apply ModuleCat.hom_ext
    exact act_mul F B (M.obj X) (N.obj X) x y
private theorem presheafSection_retract
    (e : B ⊗[F] B)
    (hd : ∀ b : B, (b ⊗ₜ[F] (1 : B) - (1 : B) ⊗ₜ[F] b) * e = 0)
    (M N : S ⥤ ModuleCat.{u + 1} B) :
    Functor.LaxMonoidal.μ
      ((Functor.whiskeringRight S _ _).obj
        (ModuleCat.restrictScalars.{u + 1} (algebraMap F B))) M N ≫
      presheafSection F B e hd M N = presheafActionRing F B M N e := by
  apply NatTrans.ext
  funext X
  exact congr_app (congr_app (ordinarySection_retract F B e hd) (M.obj X)) (N.obj X)
private theorem presheafAction_pure (b c : B) (M N : S ⥤ ModuleCat.{u + 1} B) :
    presheafActionRing F B M N (b ⊗ₜ[F] c) =
      ((Functor.whiskeringRight S _ _).obj
        (ModuleCat.restrictScalars.{u + 1} (algebraMap F B))).map (b • 𝟙 M) ⊗ₘ
      ((Functor.whiskeringRight S _ _).obj
        (ModuleCat.restrictScalars.{u + 1} (algebraMap F B))).map (c • 𝟙 N) := by
  apply NatTrans.ext
  funext X
  apply ModuleCat.hom_ext
  apply TensorProduct.ext
  apply LinearMap.ext
  intro m
  apply LinearMap.ext
  intro n
  rfl
end Native

namespace AlgebraicGeometry.Etale
open scoped ModuleCat.Algebra
private theorem ordinaryRetracts_natural
    {C D : Type (u + 2)} [Category.{u + 1} C] [Category.{u + 1} D]
    [Preadditive C] [Preadditive D] [MonoidalCategory C] [MonoidalCategory D]
    [MonoidalPreadditive C] [MonoidalPreadditive D]
    (F B : Type (u + 1)) [Field F] [Field B] [Algebra F B]
    [CategoryTheory.Linear B C] (G : C ⥤ D) [G.Additive] [G.LaxMonoidal]
    (e : B ⊗[F] B)
    (h : ∀ M N : C, ∃ (a : (B ⊗[F] B) →+* End (G.obj M ⊗ G.obj N))
      (s : G.obj (M ⊗ N) ⟶ G.obj M ⊗ G.obj N),
      s ≫ Functor.LaxMonoidal.μ G M N = 𝟙 _ ∧
      Functor.LaxMonoidal.μ G M N ≫ s = a e ∧
      ∀ b c : B, a (b ⊗ₜ[F] c) = G.map (b • 𝟙 M) ⊗ₘ G.map (c • 𝟙 N)) :
    let S := (((Functor.whiskeringLeft₂ D).obj G).obj G).obj (curriedTensor D)
    let T := (Functor.postcompose₂.obj G).obj (curriedTensor C)
    ∃ (a : (B ⊗[F] B) →+* End S) (s : T ⟶ S),
      s ≫ Functor.LaxMonoidal.μNatTrans G = 𝟙 _ ∧
      Functor.LaxMonoidal.μNatTrans G ≫ s = a e ∧
      ∀ (b c : B) (M N : C),
        ((a (b ⊗ₜ[F] c)).app M).app N = G.map (b • 𝟙 M) ⊗ₘ G.map (c • 𝟙 N) := by
  classical
  choose a s hs hp ha using h
  have hn {M M' N N' : C} (f : M ⟶ M') (g : N ⟶ N') (x : B ⊗[F] B) :
      (G.map f ⊗ₘ G.map g) ≫ a M' N' x = a M N x ≫ (G.map f ⊗ₘ G.map g) := by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy =>
      simp only [map_add]
      erw [Preadditive.comp_add, Preadditive.add_comp, hx, hy]
    | tmul b c =>
      rw [ha, ha, tensorHom_comp_tensorHom, tensorHom_comp_tensorHom]
      simp only [← G.map_comp, Linear.smul_comp, Linear.comp_smul, Category.comp_id,
        Category.id_comp]
  have hsn {M M' N N' : C} (f : M ⟶ M') (g : N ⟶ N') :
      G.map (f ⊗ₘ g) ≫ s M' N' = s M N ≫ (G.map f ⊗ₘ G.map g) := by
    calc
      _ = (s M N ≫ Functor.LaxMonoidal.μ G M N) ≫ G.map (f ⊗ₘ g) ≫ s M' N' := by
        rw [hs, Category.id_comp]
      _ = s M N ≫ (G.map f ⊗ₘ G.map g) ≫
          Functor.LaxMonoidal.μ G M' N' ≫ s M' N' := by
        rw [Category.assoc, ← Functor.LaxMonoidal.μ_natural_assoc]
      _ = s M N ≫ (G.map f ⊗ₘ G.map g) ≫ a M' N' e := by rw [hp]
      _ = s M N ≫ a M N e ≫ (G.map f ⊗ₘ G.map g) := by rw [hn]
      _ = s M N ≫ Functor.LaxMonoidal.μ G M N ≫ s M N ≫
          (G.map f ⊗ₘ G.map g) := by
        rw [← Category.assoc (Functor.LaxMonoidal.μ G M N), hp]
      _ = _ := by rw [← Category.assoc (s M N), hs, Category.id_comp]
  let α (x : B ⊗[F] B) : End
      ((((Functor.whiskeringLeft₂ D).obj G).obj G).obj (curriedTensor D)) :=
    { app M :=
        { app N := a M N x
          naturality N N' g := by
            change (G.obj M ◁ G.map g) ≫ a M N' x =
              a M N x ≫ (G.obj M ◁ G.map g)
            simpa only [CategoryTheory.Functor.map_id, id_tensorHom] using hn (𝟙 M) g x }
      naturality M M' f := by
        apply NatTrans.ext
        funext N
        change (G.map f ▷ G.obj N) ≫ a M' N x = a M N x ≫ (G.map f ▷ G.obj N)
        simpa only [CategoryTheory.Functor.map_id, tensorHom_id] using hn f (𝟙 N) x }
  let ar : (B ⊗[F] B) →+* End
      ((((Functor.whiskeringLeft₂ D).obj G).obj G).obj (curriedTensor D)) :=
    { toFun := α
      map_zero' := by
        apply NatTrans.ext
        funext M
        apply NatTrans.ext
        funext N
        exact (a M N).map_zero
      map_one' := by
        apply NatTrans.ext
        funext M
        apply NatTrans.ext
        funext N
        exact (a M N).map_one
      map_add' x y := by
        apply NatTrans.ext
        funext M
        apply NatTrans.ext
        funext N
        exact (a M N).map_add x y
      map_mul' x y := by
        apply NatTrans.ext
        funext M
        apply NatTrans.ext
        funext N
        exact (a M N).map_mul x y }
  let sn : (Functor.postcompose₂.obj G).obj (curriedTensor C) ⟶
      (((Functor.whiskeringLeft₂ D).obj G).obj G).obj (curriedTensor D) :=
    { app M :=
        { app N := s M N
          naturality N N' g := by
            change G.map (M ◁ g) ≫ s M N' = s M N ≫ (G.obj M ◁ G.map g)
            simpa only [CategoryTheory.Functor.map_id, id_tensorHom] using hsn (𝟙 M) g }
      naturality M M' f := by
        apply NatTrans.ext
        funext N
        change G.map (f ▷ N) ≫ s M' N = s M N ≫ (G.map f ▷ G.obj N)
        simpa only [CategoryTheory.Functor.map_id, tensorHom_id] using hsn f (𝟙 N) }
  refine ⟨ar, sn, ?_, ?_, ?_⟩
  · apply NatTrans.ext
    funext M
    apply NatTrans.ext
    funext N
    exact hs M N
  · apply NatTrans.ext
    funext M
    apply NatTrans.ext
    funext N
    exact hp M N
  · intro b c M N
    exact ha M N b c

private noncomputable def sheafTensorReflectionIso
    (A : Type (u + 1)) [Field A] (T : Scheme.{u})
    (M N : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    M ⊗ N ≅ (presheafToSheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)).obj
      (M.obj ⊗ N.obj) :=
  tensorIso (asIso ((sheafificationAdjunction T.smallEtaleTopology
      (ModuleCat.{u + 1} A)).counit.app M)).symm
    (asIso ((sheafificationAdjunction T.smallEtaleTopology
      (ModuleCat.{u + 1} A)).counit.app N)).symm ≪≫
    Functor.Monoidal.μIso (presheafToSheaf T.smallEtaleTopology
      (ModuleCat.{u + 1} A)) M.obj N.obj
private theorem sheafTensorReflectionIso_unit
    (A : Type (u + 1)) [Field A] (T : Scheme.{u})
    (M N : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    (sheafificationAdjunction T.smallEtaleTopology (ModuleCat.{u + 1} A)).unit.app
        (M.obj ⊗ N.obj) ≫
      (sheafToPresheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)).map
        (sheafTensorReflectionIso A T M N).inv =
      Functor.LaxMonoidal.μ
        (sheafToPresheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) M N := by
  rw [Adjunction.IsMonoidal.leftAdjoint_μ
    (adj := sheafificationAdjunction T.smallEtaleTopology (ModuleCat.{u + 1} A))]
  congr 2
private noncomputable def restrictionSheafTensorIso
    (F B : Type (u + 1)) [Field F] [Field B] [Algebra F B] (T : Scheme.{u})
    (M N : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} B)) :
    (Sheaf.restrictScalars T.smallEtaleTopology (algebraMap F B)).obj (M ⊗ N) ≅
      (presheafToSheaf T.smallEtaleTopology (ModuleCat.{u + 1} F)).obj
        ((M.obj ⊗ N.obj) ⋙ ModuleCat.restrictScalars.{u + 1} (algebraMap F B)) := by
  let U := ModuleCat.restrictScalars.{u + 1} (algebraMap F B)
  have : T.smallEtaleTopology.PreservesSheafification U :=
    Sheaf.preservesSheafification_of_adjunction _
      (ModuleCat.restrictCoextendScalarsAdj.{u + 1, u + 1, u + 1} (algebraMap F B))
  exact (sheafCompose T.smallEtaleTopology U).mapIso (sheafTensorReflectionIso B T M N) ≪≫
    ((sheafComposeNatIso T.smallEtaleTopology U
      (sheafificationAdjunction T.smallEtaleTopology (ModuleCat.{u + 1} B))
      (sheafificationAdjunction T.smallEtaleTopology (ModuleCat.{u + 1} F))).app
        (M.obj ⊗ N.obj)).symm
private theorem restrictionSheafTensorIso_unit
    (F B : Type (u + 1)) [Field F] [Field B] [Algebra F B] (T : Scheme.{u})
    (M N : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} B)) :
    ((Functor.whiskeringRight _ _ _).obj
        (ModuleCat.restrictScalars.{u + 1} (algebraMap F B))).map
        (Functor.LaxMonoidal.μ
          (sheafToPresheaf T.smallEtaleTopology (ModuleCat.{u + 1} B)) M N) ≫
      (sheafToPresheaf T.smallEtaleTopology (ModuleCat.{u + 1} F)).map
        (restrictionSheafTensorIso F B T M N).hom =
      (sheafificationAdjunction T.smallEtaleTopology (ModuleCat.{u + 1} F)).unit.app
        ((M.obj ⊗ N.obj) ⋙ ModuleCat.restrictScalars.{u + 1} (algebraMap F B)) := by
  let J := T.smallEtaleTopology
  let U := ModuleCat.restrictScalars.{u + 1} (algebraMap F B)
  let V := (Functor.whiskeringRight T.Etaleᵒᵖ
    (ModuleCat.{u + 1} B) (ModuleCat.{u + 1} F)).obj U
  let RF := sheafToPresheaf J (ModuleCat.{u + 1} F)
  let RB := sheafToPresheaf J (ModuleCat.{u + 1} B)
  let AF := sheafificationAdjunction J (ModuleCat.{u + 1} F)
  let AB := sheafificationAdjunction J (ModuleCat.{u + 1} B)
  have : J.PreservesSheafification U := Sheaf.preservesSheafification_of_adjunction _
    (ModuleCat.restrictCoextendScalarsAdj.{u + 1, u + 1, u + 1} (algebraMap F B))
  let σ := (sheafComposeNatIso J U AB AF).app (M.obj ⊗ N.obj)
  let b := sheafTensorReflectionIso B T M N
  have hb : Functor.LaxMonoidal.μ RB M N ≫ RB.map b.hom = AB.unit.app (M.obj ⊗ N.obj) := by
    rw [← sheafTensorReflectionIso_unit B T M N, Category.assoc, ← RB.map_comp,
      Iso.inv_hom_id, RB.map_id]
    exact Category.comp_id _
  have hc : AF.unit.app ((M.obj ⊗ N.obj) ⋙ U) ≫ RF.map σ.hom =
      V.map (AB.unit.app (M.obj ⊗ N.obj)) := by
    exact sheafComposeNatTrans_fac J U AB AF (M.obj ⊗ N.obj)
  change V.map (Functor.LaxMonoidal.μ RB M N) ≫
    V.map (RB.map b.hom) ≫ RF.map σ.inv = _
  rw [← V.map_comp_assoc, hb, ← hc, Category.assoc, ← RF.map_comp,
    Iso.hom_inv_id, RF.map_id]
  exact Category.comp_id _
private theorem restrictionSheafTensorIso_tensorator
    (F B : Type (u + 1)) [Field F] [Field B] [Algebra F B] (T : Scheme.{u})
    (M N : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} B)) :
    Functor.LaxMonoidal.μ
        (Sheaf.restrictScalars T.smallEtaleTopology (algebraMap F B)) M N ≫
      (restrictionSheafTensorIso F B T M N).hom =
      (sheafTensorReflectionIso F T
        ((Sheaf.restrictScalars T.smallEtaleTopology (algebraMap F B)).obj M)
        ((Sheaf.restrictScalars T.smallEtaleTopology (algebraMap F B)).obj N)).hom ≫
      (presheafToSheaf T.smallEtaleTopology (ModuleCat.{u + 1} F)).map
        (Functor.LaxMonoidal.μ
          ((Functor.whiskeringRight _ _ _).obj
            (ModuleCat.restrictScalars.{u + 1} (algebraMap F B))) M.obj N.obj) := by
  let J := T.smallEtaleTopology
  let U := ModuleCat.restrictScalars.{u + 1} (algebraMap F B)
  let G := Sheaf.restrictScalars J (algebraMap F B)
  let RF := sheafToPresheaf J (ModuleCat.{u + 1} F)
  let LF := presheafToSheaf J (ModuleCat.{u + 1} F)
  let AF := sheafificationAdjunction J (ModuleCat.{u + 1} F)
  let i := sheafTensorReflectionIso F T (G.obj M) (G.obj N)
  let j := restrictionSheafTensorIso F B T M N
  let q := Functor.LaxMonoidal.μ G M N
  let qpre := Functor.LaxMonoidal.μ ((Functor.whiskeringRight _ _ _).obj U) M.obj N.obj
  have h : i.inv ≫ q ≫ j.hom = LF.map qpre := by
    apply (AF.homEquiv _ _).injective
    change AF.unit.app _ ≫ RF.map (i.inv ≫ q ≫ j.hom) =
      AF.unit.app _ ≫ RF.map (LF.map qpre)
    calc
      _ = (AF.unit.app _ ≫ RF.map i.inv) ≫ RF.map q ≫ RF.map j.hom := by
        simp only [RF.map_comp, Category.assoc]
      _ = Functor.LaxMonoidal.μ RF (G.obj M) (G.obj N) ≫ RF.map q ≫ RF.map j.hom := by
        rw [sheafTensorReflectionIso_unit F T (G.obj M) (G.obj N)]
      _ = qpre ≫ ((Functor.whiskeringRight _ _ _).obj U).map
          (Functor.LaxMonoidal.μ
            (sheafToPresheaf J (ModuleCat.{u + 1} B)) M N) ≫ RF.map j.hom := by
        rw [← Category.assoc, Sheaf.μ_sheafToPresheaf_comp_map_μ_sheafCompose,
          Category.assoc]
        rfl
      _ = qpre ≫ AF.unit.app _ := by rw [restrictionSheafTensorIso_unit]
      _ = _ := AF.unit.naturality qpre
  calc
    q ≫ j.hom = i.hom ≫ (i.inv ≫ q ≫ j.hom) := by simp only [← Category.assoc,
      Iso.hom_inv_id, Category.id_comp]
    _ = i.hom ≫ LF.map qpre := by rw [h]
private theorem sheafTensorReflectionIso_conjugate
    (A : Type (u + 1)) [Field A] (T : Scheme.{u})
    (M N : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))
    (f : M ⟶ M) (g : N ⟶ N) :
    (sheafTensorReflectionIso A T M N).hom ≫
      (presheafToSheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)).map (f.hom ⊗ₘ g.hom) ≫
      (sheafTensorReflectionIso A T M N).inv = f ⊗ₘ g := by
  let L := presheafToSheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)
  let adj := sheafificationAdjunction T.smallEtaleTopology (ModuleCat.{u + 1} A)
  let i := sheafTensorReflectionIso A T M N
  change i.hom ≫ _ ≫ i.inv = _
  apply (cancel_mono i.hom).1
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  dsimp only [i, sheafTensorReflectionIso]
  simp only [Iso.trans_hom, tensorIso_hom, Iso.symm_hom, asIso_inv,
    Functor.Monoidal.μIso_hom, Category.assoc]
  rw [← Functor.LaxMonoidal.μ_natural, ← Category.assoc, ← Category.assoc]
  congr 1
  simp only [tensorHom_comp_tensorHom]
  congr 1
  · simpa only [adj, asIso_inv, NatIso.isIso_inv_app, Functor.comp_map,
      Functor.id_map, Functor.comp_obj, Functor.id_obj, sheafToPresheaf,
      ObjectProperty.ι_map, ObjectProperty.ι_obj] using
      ((asIso adj.counit).inv.naturality f).symm
  · simpa only [adj, asIso_inv, NatIso.isIso_inv_app, Functor.comp_map,
      Functor.id_map, Functor.comp_obj, Functor.id_obj, sheafToPresheaf,
      ObjectProperty.ι_map, ObjectProperty.ι_obj] using
      ((asIso adj.counit).inv.naturality g).symm


private theorem ordinarySheafRetractPair
    (F B : Type (u + 1)) [Field F] [Field B] [Algebra F B] (T : Scheme.{u})
    (e : B ⊗[F] B) (hμ : Algebra.TensorProduct.lmul' F e = 1)
    (hd : ∀ b : B, (b ⊗ₜ[F] (1 : B) - (1 : B) ⊗ₜ[F] b) * e = 0)
    (M N : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} B)) :
    let G := Sheaf.restrictScalars T.smallEtaleTopology (algebraMap F B)
    ∃ (a : (B ⊗[F] B) →+* End (G.obj M ⊗ G.obj N))
      (s : G.obj (M ⊗ N) ⟶ G.obj M ⊗ G.obj N),
      s ≫ Functor.LaxMonoidal.μ G M N = 𝟙 _ ∧
      Functor.LaxMonoidal.μ G M N ≫ s = a e ∧
      ∀ b c : B, a (b ⊗ₜ[F] c) = G.map (b • 𝟙 M) ⊗ₘ G.map (c • 𝟙 N) := by
  let U := ModuleCat.restrictScalars.{u + 1} (algebraMap F B)
  let G := Sheaf.restrictScalars T.smallEtaleTopology (algebraMap F B)
  let L := presheafToSheaf T.smallEtaleTopology (ModuleCat.{u + 1} F)
  let i := sheafTensorReflectionIso F T (G.obj M) (G.obj N)
  let j := restrictionSheafTensorIso F B T M N
  let q := Functor.LaxMonoidal.μ ((Functor.whiskeringRight _ _ _).obj U) M.obj N.obj
  let a := Native.presheafActionRing F B M.obj N.obj
  let s := Native.presheafSection F B e hd M.obj N.obj
  let ad := i.symm.conjRingEquiv.toRingHom.comp ((L.mapEndRingHom _).comp a)
  let sd := j.hom ≫ L.map s ≫ i.inv
  have ht : Functor.LaxMonoidal.μ G M N = i.hom ≫ L.map q ≫ j.inv := by
    apply (cancel_mono j.hom).1
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    exact restrictionSheafTensorIso_tensorator F B T M N
  have hs : s ≫ q = 𝟙 _ := Native.presheafSection_split F B e hμ hd M.obj N.obj
  have hp : q ≫ s = a e := Native.presheafSection_retract F B e hd M.obj N.obj
  refine ⟨ad, sd, ?_, ?_, ?_⟩
  · rw [ht]
    simp only [sd, Category.assoc, Iso.inv_hom_id_assoc, ← L.map_comp_assoc]
    rw [hs, L.map_id, Category.id_comp, Iso.hom_inv_id]
  · rw [ht]
    simp only [sd, Category.assoc, Iso.inv_hom_id_assoc, ← L.map_comp_assoc]
    change i.hom ≫ L.map (q ≫ s) ≫ i.inv = i.hom ≫ L.map (a e) ≫ i.inv
    rw [hp]
  · intro b c
    change i.hom ≫ L.map (a (b ⊗ₜ[F] c)) ≫ i.inv = _
    rw [Native.presheafAction_pure]
    exact sheafTensorReflectionIso_conjugate F T (G.obj M) (G.obj N)
      (G.map (b • 𝟙 M)) (G.map (c • 𝟙 N))

set_option maxHeartbeats 1000000 in
-- Totalization elaborates the native sheaf tensor and scalar-restriction instances.
section Localization
variable {C D : Type (u + 2)} [Category.{u + 1} C] [Category.{u + 1} D]
  [Abelian C] [Abelian D] [IsGrothendieckAbelian.{u + 1} C]
  [IsGrothendieckAbelian.{u + 1} D]
  [MonoidalCategory C] [MonoidalCategory D]
  [SymmetricCategory C] [SymmetricCategory D]
  [MonoidalClosed C] [MonoidalClosed D]
  [MonoidalPreadditive C] [MonoidalPreadditive D]
  [Abelian.HasFunctorialFlatResolution C] [Abelian.HasFunctorialFlatResolution D]
  [HasDerivedCategory.{u + 1} C] [HasDerivedCategory.{u + 1} D]
  (G : C ⥤ D) [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  (ordinary : G.LaxMonoidal) (t : RestrictionTensorData G ordinary)
  (K L : CochainComplex C ℤ)

private theorem tensorLocalizationConjugate_map
    [IsIso (Functor.LaxMonoidal.μ DerivedCategory.Q
      ((G.mapHomologicalComplex (.up ℤ)).obj K)
      ((G.mapHomologicalComplex (.up ℤ)).obj L))]
    (f : K ⟶ K) (g : L ⟶ L) :
    let i := tensorIso (G.mapDerivedCategoryFactors.app K)
        (G.mapDerivedCategoryFactors.app L) ≪≫
      asIso (Functor.LaxMonoidal.μ DerivedCategory.Q
        ((G.mapHomologicalComplex (.up ℤ)).obj K)
        ((G.mapHomologicalComplex (.up ℤ)).obj L))
    i.hom ≫ DerivedCategory.Q.map
        ((G.mapHomologicalComplex (.up ℤ)).map f ⊗ₘ
          (G.mapHomologicalComplex (.up ℤ)).map g) ≫ i.inv =
      G.mapDerivedCategory.map (DerivedCategory.Q.map f) ⊗ₘ
        G.mapDerivedCategory.map (DerivedCategory.Q.map g) := by
  let i := tensorIso (G.mapDerivedCategoryFactors.app K)
      (G.mapDerivedCategoryFactors.app L) ≪≫
    asIso (Functor.LaxMonoidal.μ DerivedCategory.Q
      ((G.mapHomologicalComplex (.up ℤ)).obj K)
      ((G.mapHomologicalComplex (.up ℤ)).obj L))
  change i.hom ≫ _ ≫ i.inv = _
  apply (cancel_mono i.hom).1
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  dsimp only [i, Iso.trans_hom, tensorIso_hom, Iso.app_hom, asIso_hom]
  simp only [Category.assoc]
  rw [← Functor.LaxMonoidal.μ_natural]
  rw [← Category.assoc, ← Category.assoc]
  congr 1
  simp only [tensorIso_hom, Iso.app_hom, tensorHom_comp_tensorHom]
  congr 1
  · exact (G.mapDerivedCategoryFactors.hom.naturality f).symm
  · exact (G.mapDerivedCategoryFactors.hom.naturality g).symm


end Localization


/-- The normalized balanced sheaf tensor and its diagonal section.
Source: finite-ring Kunneth proof, first paragraph, sheaf case.
(blueprint: lem-pur-native-diagonal-tensor-etale). -/
structure NativeDiagonalTensorEtaleData
    (F B : Type (u + 1)) [Field F] [Field B] [Algebra F B]
    (T : Scheme.{u}) (e : B ⊗[F] B)
    (t : RestrictionTensorData (Sheaf.restrictScalars T.smallEtaleTopology (algebraMap F B))
      (sheafComposeLaxMonoidal T.smallEtaleTopology
        (ModuleCat.restrictScalars (algebraMap F B))))
    (M N : DerivedCategoryModule B T) where
  action : (B ⊗[F] B) →+* End
    ((Sheaf.restrictScalars T.smallEtaleTopology (algebraMap F B)).mapDerivedCategory.obj M ⊗
      (Sheaf.restrictScalars T.smallEtaleTopology (algebraMap F B)).mapDerivedCategory.obj N)
  action_pure : ∀ a b : B, action (a ⊗ₜ[F] b) =
    (Sheaf.restrictScalars T.smallEtaleTopology (algebraMap F B)).mapDerivedCategory.map
        (a • 𝟙 M) ⊗ₘ
      (Sheaf.restrictScalars T.smallEtaleTopology (algebraMap F B)).mapDerivedCategory.map
        (b • 𝟙 N)
  inclusion :
    (Sheaf.restrictScalars T.smallEtaleTopology (algebraMap F B)).mapDerivedCategory.obj
      (M ⊗ N) ⟶
    (Sheaf.restrictScalars T.smallEtaleTopology (algebraMap F B)).mapDerivedCategory.obj M ⊗
      (Sheaf.restrictScalars T.smallEtaleTopology (algebraMap F B)).mapDerivedCategory.obj N
  split : inclusion ≫ t.map M N = 𝟙 _
  retract : t.map M N ≫ inclusion = action e

set_option maxHeartbeats 1000000 in
-- Kernel checking the representative transports unfolds large native derived sheaf instances.
/-- Finite separability splits the normalized native small-etale tensorator.
Source: the first paragraph of the finite-ring Kunneth proof.

Proof. On the underlying presheaf modules define the section of the balanced quotient by
the separability sum x tensor_B y mapping to sum a_i x tensor_F b_i y. The diagonal
annihilation relation proves balancing and multiplication(e)=1 proves the two retraction
identities. The maps commute with restriction and extend through sheafification by its
universal property. This also handles locally constant coefficient sections. Apply them
in every bidegree and take direct-sum totalizations. Every complex of sheaves over the
constant field is K-flat: upper truncations have flat terms and their filtered colimit is
the original complex. Restriction preserves these representatives. Descend the natural
maps through localization using the standard native derived tensor comparisons. The
chain_summand and normalization clauses of t force the descended quotient to be t.map.
The pure-action identity is the corresponding calculation on each tensor summand.
The construction works on the empty scheme and for arbitrary unbounded complexes.
(blueprint: lem-pur-native-diagonal-tensor-etale). -/
theorem nativeDiagonalTensorEtale
    (F B : Type (u + 1)) [Field F] [Field B] [Finite F] [Finite B] [Algebra F B]
    (T : Scheme.{u}) (e : B ⊗[F] B) (hμ : Algebra.TensorProduct.lmul' F e = 1)
    (hd : ∀ b : B, (b ⊗ₜ[F] (1 : B) - (1 : B) ⊗ₜ[F] b) * e = 0)
    (t : RestrictionTensorData (Sheaf.restrictScalars T.smallEtaleTopology (algebraMap F B))
      (sheafComposeLaxMonoidal T.smallEtaleTopology
        (ModuleCat.restrictScalars (algebraMap F B))))
    (M N : DerivedCategoryModule B T) :
    Nonempty (NativeDiagonalTensorEtaleData F B T e t M N) := by
  let G := Sheaf.restrictScalars T.smallEtaleTopology (algebraMap F B)
  let K := DerivedCategory.Q.objPreimage M
  let L := DerivedCategory.Q.objPreimage N
  let m : DerivedCategory.Q.obj K ≅ M := DerivedCategory.Q.objObjPreimageIso M
  let n : DerivedCategory.Q.obj L ≅ N := DerivedCategory.Q.objObjPreimageIso N
  obtain ⟨a, s, hs, hp, ha⟩ := nativeSheafChainRetraction F B T e hμ hd t K L
  have := tensorComparisonIsoOfAllFlat
    (fun X : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} B) ↦
      (flat_iff_forall_flat_sheafFiber_obj X).2
        (fun {_} {_} {_} _ ↦ (ModuleCat.flat_iff_flat _).2 inferInstance)) K L
  have := tensorComparisonIsoOfAllFlat
    (fun X : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} F) ↦
      (flat_iff_forall_flat_sheafFiber_obj X).2
        (fun {_} {_} {_} _ ↦ (ModuleCat.flat_iff_flat _).2 inferInstance))
    ((G.mapHomologicalComplex (.up ℤ)).obj K)
    ((G.mapHomologicalComplex (.up ℤ)).obj L)
  obtain ⟨ad, sd, hsd, hpd, had⟩ := diagonalTensorLocalization G inferInstance t K L
    a s e hs hp
  have hadp (b c : B) : ad (b ⊗ₜ[F] c) =
      G.mapDerivedCategory.map (b • 𝟙 (DerivedCategory.Q.obj K)) ⊗ₘ
        G.mapDerivedCategory.map (c • 𝟙 (DerivedCategory.Q.obj L)) := by
    rw [had, ha]
    have h := tensorLocalizationConjugate_map G K L (b • 𝟙 K) (c • 𝟙 L)
    have hK : DerivedCategory.Q.map (b • 𝟙 K) =
        b • 𝟙 (DerivedCategory.Q.obj K) := by rw [Functor.map_smul, CategoryTheory.Functor.map_id]
    have hL : DerivedCategory.Q.map (c • 𝟙 L) =
        c • 𝟙 (DerivedCategory.Q.obj L) := by rw [Functor.map_smul, CategoryTheory.Functor.map_id]
    rw [hK, hL] at h
    dsimp only [G] at h ⊢
    simpa only [Iso.trans_hom, Iso.trans_inv, tensorIso_hom, tensorIso_inv,
      Iso.app_hom, Iso.app_inv, asIso_hom, asIso_inv, Category.assoc] using h
  let i := tensorIso (G.mapDerivedCategory.mapIso m) (G.mapDerivedCategory.mapIso n)
  let j := G.mapDerivedCategory.mapIso (tensorIso m n)
  let af := i.conjRingEquiv.toRingHom.comp ad
  let sf := j.inv ≫ sd ≫ i.hom
  have ht : t.map M N = i.inv ≫ t.map (DerivedCategory.Q.obj K)
      (DerivedCategory.Q.obj L) ≫ j.hom := by
    apply (cancel_epi i.hom).1
    simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
    simpa only [i, j, tensorIso_hom, Functor.mapIso_hom, Category.assoc] using
      t.naturality m.hom n.hom
  refine ⟨{
    action := af
    action_pure := ?_
    inclusion := sf
    split := ?_
    retract := ?_ }⟩
  · intro b c
    change i.inv ≫ ad (b ⊗ₜ[F] c) ≫ i.hom = _
    rw [hadp]
    simp only [i, tensorIso_inv, tensorIso_hom, Functor.mapIso_inv,
      Functor.mapIso_hom, tensorHom_comp_tensorHom,
      ← G.mapDerivedCategory.map_comp]
    simp [Linear.smul_comp, Linear.comp_smul]
    rfl
  · rw [ht]
    simp only [sf, Category.assoc, Iso.hom_inv_id_assoc]
    rw [← Category.assoc sd, hsd, Category.id_comp, Iso.inv_hom_id]
  · rw [ht]
    simp only [sf, Category.assoc, Iso.hom_inv_id_assoc]
    rw [← Category.assoc (t.map (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj L)), hpd]
    rfl


#print axioms nativeDiagonalTensorEtale

end AlgebraicGeometry.Etale
