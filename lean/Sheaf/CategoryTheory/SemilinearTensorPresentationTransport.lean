/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q63
-/
module

public import Sheaf.CategoryTheory.SemilinearTensorPresentationData
import all Sheaf.CategoryTheory.GeometricModuleTransport
import all Sheaf.CategoryTheory.GeometricModuleConstruction
import all Sheaf.CategoryTheory.RingedToposKFlatPullback
import Sheaf.Paper.RingedTopoiInverseImageTensorComparison
import all Sheaf.Paper.RingedTopoiInverseImagePairing
import Sheaf.Paper.RingedTopoiInverseImageTensorPairingIsIso
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all Sheaf.CategoryTheory.TensorPushoutAction
import Mathlib.Algebra.Category.Ring.Constructions
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
import Mathlib.Algebra.Module.TransferInstance
import Mathlib.CategoryTheory.Sites.LeftExact
import Mathlib.Algebra.Category.Ring.FilteredColimits

/-! # Semilinear tensor transport through a ring presentation

Source: the integral-twist paragraph of
literature/blueprint/main-20261015/blueprint/sec-smooth-purity/sk-prop-an/
sk-prop-sfb-cartesian-coefficients-twists.proof.md; Stacks Tags 03CY, 03D1--03D3, 03EK, 03EL.
(blueprint: lem-pur-semilinear-tensor-presentation-transport)
-/

@[expose] public noncomputable section

universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped TensorProduct
namespace SheafOfModules.TensorPresentationTransport
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {C E : Type u} [Category.{u} C] [Category.{u} E]
  {J : GrothendieckTopology C} {K : GrothendieckTopology E}

open SheafOfModules.GeometricConstruction

private theorem algebraicLift
    (F : Sheaf J (Type u) ⥤ Sheaf K (Type u))
    (V : Sheaf K (Type u) ⥤ Sheaf J (Type u)) (adj : F ⊣ V)
    [PreservesFiniteLimits F]
    (R : Sheaf J CommRingCat.{u}) (S : Sheaf K CommRingCat.{u})
    (d : F.obj (ringSets R) ≅ ringSets S) (hd : IsRingTransport F R S d) :
    ∃ I : AlgebraicInverseImage F R S, I.ringUnderlying = d := by
  have ha := binary_of_graph F d.hom d.hom d.hom (radd R) (radd S)
    (fun U x y ↦ @Add.add (R.obj.obj U) inferInstance x y)
    (fun U x y ↦ @Add.add (S.obj.obj U) inferInstance x y)
    (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) hd.1
  have hm := binary_of_graph F d.hom d.hom d.hom (rmul R) (rmul S)
    (fun U x y ↦ @Mul.mul (R.obj.obj U) inferInstance x y)
    (fun U x y ↦ @Mul.mul (S.obj.obj U) inferInstance x y)
    (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) hd.2.1
  have ha' : F.map (radd R) = prodComparison F _ _ ≫
      prod.map d.hom d.hom ≫ radd S ≫ d.inv := by
    apply (cancel_mono d.hom).mp
    simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using ha
  have hm' : F.map (rmul R) = prodComparison F _ _ ≫
      prod.map d.hom d.hom ≫ rmul S ≫ d.inv := by
    apply (cancel_mono d.hom).mp
    simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using hm
  obtain ⟨I, P, eI, eP, hI, hP⟩ := geometric_module_construction J K F V adj
    R S S d.symm (radd R) (rmul R) (radd S) (rmul S)
      ⟨fun _ _ ↦ rfl, fun _ _ ↦ rfl, fun _ _ ↦ rfl, fun _ _ ↦ rfl, ha', hm'⟩ (𝟙 S)
  refine ⟨{ ringUnderlying := d
            ringAdd := hd.1
            ringMul := hd.2.1
            ringZero := hd.2.2.1
            ringOne := hd.2.2.2
            modules := I
            moduleUnderlying := eI
            moduleAdd := ?_
            moduleZero := ?_
            moduleSMul := ?_ }, rfl⟩
  · intro M T a b z hz
    obtain ⟨addM, muM, addI, muI, haM, hsM, haI, hsI, heaI, hesI⟩ := hI M
    exact graph_sections F (eI.app M) (eI.app M) (eI.app M) addM addI heaI
      (fun U x y ↦ @Add.add (M.val.obj U) inferInstance x y)
      (fun U x y ↦ @Add.add ((I.obj M).val.obj U) inferInstance x y)
      haM haI a b z hz
  · intro M T a ha U x
    obtain ⟨addM, muM, addI, muI, haM, hsM, haI, hsI, heaI, hesI⟩ := hI M
    have h := graph_sections F (eI.app M) (eI.app M) (eI.app M) addM addI heaI
      (fun U x y ↦ @Add.add (M.val.obj U) inferInstance x y)
      (fun U x y ↦ @Add.add ((I.obj M).val.obj U) inferInstance x y)
      haM haI a a a (by
        intro W t
        have hz : @Eq (M.val.obj W) (a.hom.app W t) 0 := ha W t
        exact hz.trans ((zero_add (0 : M.val.obj W)).symm.trans
          (congrArg₂ (fun x y : M.val.obj W ↦ x + y) hz.symm hz.symm))) U x
    exact add_eq_left.mp h.symm
  · intro M T a b z hz
    obtain ⟨addM, muM, addI, muI, haM, hsM, haI, hsI, heaI, hesI⟩ := hI M
    exact graph_sections F d.symm (eI.app M) (eI.app M) muM muI hesI
      (fun U x y ↦ @SMul.smul (R.obj.obj U) (M.val.obj U) inferInstance x y)
      (fun U x y ↦ @SMul.smul (S.obj.obj U) ((I.obj M).val.obj U)
        inferInstance x y) hsM hsI a b z hz

private theorem descend_binary
    (F : Sheaf J (Type u) ⥤ Sheaf K (Type u)) [PreservesFiniteLimits F]
    {X Y Z : Sheaf J (Type u)} {A B G A' B' G' : Sheaf K (Type u)}
    (eX : A ≅ F.obj X) (eY : B ≅ F.obj Y) (eZ : G ≅ F.obj Z)
    (a : X ⨯ Y ⟶ Z) (b : A ⨯ B ⟶ G) (c : A' ⨯ B' ⟶ G')
    (kX : F.obj X ⟶ A') (kY : F.obj Y ⟶ B') (kZ : F.obj Z ⟶ G')
    (h : F.map a ≫ eZ.inv =
      prodComparison F X Y ≫ prod.map eX.inv eY.inv ≫ b)
    (hk : F.map a ≫ kZ = prodComparison F X Y ≫ prod.map kX kY ≫ c) :
    b ≫ eZ.hom ≫ kZ = prod.map (eX.hom ≫ kX) (eY.hom ≫ kY) ≫ c := by
  apply (cancel_epi (prodComparison F X Y ≫ prod.map eX.inv eY.inv)).mp
  simp only [Category.assoc, prod.map_map_assoc, Iso.inv_hom_id_assoc]
  have hh := congrArg (fun q ↦ q ≫ eZ.hom ≫ kZ) h
  simp only [Category.assoc, Iso.inv_hom_id_assoc] at hh
  exact hh.symm.trans hk

private theorem linearIsoOfTransport
    (F : Sheaf J (Type u) ⥤ Sheaf K (Type u)) [PreservesFiniteLimits F]
    {R : Sheaf J CommRingCat.{u}} {S : Sheaf K CommRingCat.{u}}
    (I : AlgebraicInverseImage F R S)
    (M : SheafOfModules.{u} (RingedTensor.ringSheaf R))
    (N : SheafOfModules.{u} (RingedTensor.ringSheaf S))
    (s : F.obj (abSets (moduleAb M)) ≅ abSets (moduleAb N))
    (ha : IsAdditiveTransport F (moduleAb M) (moduleAb N) s)
    (hs : IsSemilinearTransport F R S (moduleAb M) (moduleAb N)
      (fun U ↦ inferInstanceAs (SMul (R.obj.obj U) (M.val.obj U)))
      (fun U ↦ inferInstanceAs (SMul (S.obj.obj U) (N.val.obj U))) I.ringUnderlying s) :
    ∃ e : I.modules.obj M ≅ N,
      (RingedTensor.underlying S).map e.hom = I.moduleUnderlying.hom.app M ≫ s.hom := by
  let α := I.moduleUnderlying.hom.app M ≫ s.hom
  let aM := fromProd _ _ ≫ addition R M
  let aI := fromProd _ _ ≫ addition S (I.modules.obj M)
  let aN := fromProd _ _ ≫ addition S N
  let mM := fromProd _ _ ≫ action R M
  let mI := fromProd _ _ ≫ action S (I.modules.obj M)
  let mN := fromProd _ _ ≫ action S N
  have hIA := binary_of_graph F _ _ _ aM aI
    (fun U x y ↦ @Add.add (M.val.obj U) inferInstance x y)
    (fun U x y ↦ @Add.add ((I.modules.obj M).val.obj U) inferInstance x y)
    (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (I.moduleAdd M)
  have hNA := binary_of_graph F _ _ _ aM aN
    (fun U x y ↦ @Add.add (M.val.obj U) inferInstance x y)
    (fun U x y ↦ @Add.add (N.val.obj U) inferInstance x y)
    (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) ha
  have hIS := binary_of_graph F _ _ _ mM mI
    (fun U x y ↦ @SMul.smul (R.obj.obj U) (M.val.obj U) inferInstance x y)
    (fun U x y ↦ @SMul.smul (S.obj.obj U) ((I.modules.obj M).val.obj U)
      inferInstance x y)
    (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (I.moduleSMul M)
  have hNS := binary_of_graph F _ _ _ mM mN
    (fun U x y ↦ @SMul.smul (R.obj.obj U) (M.val.obj U) inferInstance x y)
    (fun U x y ↦ @SMul.smul (S.obj.obj U) (N.val.obj U) inferInstance x y)
    (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) hs
  have hαA := descend_binary F (I.moduleUnderlying.app M) (I.moduleUnderlying.app M)
    (I.moduleUnderlying.app M) aM aI aN s.hom s.hom s.hom hIA hNA
  have hαS := descend_binary F I.ringUnderlying.symm (I.moduleUnderlying.app M)
    (I.moduleUnderlying.app M) mM mI mN I.ringUnderlying.hom s.hom s.hom hIS hNS
  simp only [Iso.symm_hom, Iso.inv_hom_id] at hαS
  have hadd := binary_hom_sections α α α aI aN
    (fun U x y ↦ @Add.add ((I.modules.obj M).val.obj U) inferInstance x y)
    (fun U x y ↦ @Add.add (N.val.obj U) inferInstance x y)
    (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) hαA
  have hsmul := binary_hom_sections (𝟙 (ringSets S)) α α mI mN
    (fun U x y ↦ @SMul.smul (S.obj.obj U) ((I.modules.obj M).val.obj U)
      inferInstance x y)
    (fun U x y ↦ @SMul.smul (S.obj.obj U) (N.val.obj U) inferInstance x y)
    (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) hαS
  let f : I.modules.obj M ⟶ N := linearLift α hadd hsmul
  have : IsIso ((RingedTensor.underlying S).map f) := by
    change IsIso (I.moduleUnderlying.hom.app M ≫ s.hom)
    infer_instance
  have : IsIso f := isIso_of_reflects_iso f (RingedTensor.underlying S)
  exact ⟨asIso f, rfl⟩

private theorem restrictedSemilinear
    (F : Sheaf J (Type u) ⥤ Sheaf K (Type u))
    {DY AY : Sheaf J CommRingCat.{u}} {DX AX : Sheaf K CommRingCat.{u}}
    {daY : DY ⟶ AY} {daX : DX ⟶ AX}
    (Y : Presentation daY) (X : Presentation daX) (t : Transport F Y X)
    (MY : SheafOfModules.{u} (RingedTensor.ringSheaf AY))
    (MX : SheafOfModules.{u} (RingedTensor.ringSheaf AX))
    (s : F.obj (abSets (moduleAb MY)) ≅ abSets (moduleAb MX))
    (hs : IsSemilinearTransport F AY AX (moduleAb MY) (moduleAb MX)
      (fun U ↦ inferInstanceAs (SMul (AY.obj.obj U) (MY.val.obj U)))
      (fun U ↦ inferInstanceAs (SMul (AX.obj.obj U) (MX.val.obj U))) t.a s) :
    IsSemilinearTransport F DY DX (moduleAb (restrictModule daY MY))
      (moduleAb (restrictModule daX MX))
      (fun U ↦ inferInstanceAs (SMul (DY.obj.obj U) ((restrictModule daY MY).val.obj U)))
      (fun U ↦ inferInstanceAs (SMul (DX.obj.obj U) ((restrictModule daX MX).val.obj U)))
      t.d s := by
  intro T a x z hz U w
  have h := hs T (a ≫ (sheafCompose J (CategoryTheory.forget CommRingCat)).map daY)
    x z hz U w
  rw [F.map_comp, Category.assoc, t.da_comm] at h
  exact h

private theorem coefficientSemilinear
    (F : Sheaf J (Type u) ⥤ Sheaf K (Type u))
    {DY AY : Sheaf J CommRingCat.{u}} {DX AX : Sheaf K CommRingCat.{u}}
    {daY : DY ⟶ AY} {daX : DX ⟶ AX}
    (Y : Presentation daY) (X : Presentation daX) (t : Transport F Y X) :
    IsSemilinearTransport F DY DX (moduleAb (coefficientModule Y.db))
      (moduleAb (coefficientModule X.db))
      (fun U ↦ inferInstanceAs (SMul (DY.obj.obj U) ((coefficientModule Y.db).val.obj U)))
      (fun U ↦ inferInstanceAs (SMul (DX.obj.obj U) ((coefficientModule X.db).val.obj U)))
      t.d t.b := by
  intro T a x z hz U w
  have h := t.hb.2.1 T
    (a ≫ (sheafCompose J (CategoryTheory.forget CommRingCat)).map Y.db) x z hz U w
  rw [F.map_comp, Category.assoc, t.db_comm] at h
  exact h

private theorem additive_comparison
    (F : Sheaf J (Type u) ⥤ Sheaf K (Type u))
    (V : Sheaf K (Type u) ⥤ Sheaf J (Type u)) (adj : F ⊣ V)
    [PreservesFiniteLimits F]
    {DY AY : Sheaf J CommRingCat.{u}} {DX AX : Sheaf K CommRingCat.{u}}
    {daY : DY ⟶ AY} {daX : DX ⟶ AX}
    (Y : Presentation daY) (X : Presentation daX) (t : Transport F Y X)
    (MY : SheafOfModules.{u} (RingedTensor.ringSheaf AY))
    (MX : SheafOfModules.{u} (RingedTensor.ringSheaf AX))
    (s : F.obj (abSets (moduleAb MY)) ≅ abSets (moduleAb MX))
    (hs : IsAdditiveTransport F (moduleAb MY) (moduleAb MX) s)
    (hsa : IsSemilinearTransport F AY AX (moduleAb MY) (moduleAb MX)
      (fun U ↦ inferInstanceAs (SMul (AY.obj.obj U) (MY.val.obj U)))
      (fun U ↦ inferInstanceAs (SMul (AX.obj.obj U) (MX.val.obj U))) t.a s) :
    ∃ r : F.obj (abSets (moduleAb (tensorModule Y MY))) ≅
        abSets (moduleAb (tensorModule X MX)),
      IsAdditiveTransport F (moduleAb (tensorModule Y MY))
        (moduleAb (tensorModule X MX)) r ∧
      ∀ (T : Sheaf J (Type u)) (x : T ⟶ abSets (moduleAb MY))
        (y : T ⟶ ringSets Y.B) (z : T ⟶ abSets (moduleAb (tensorModule Y MY))),
        (∀ U w, z.hom.app U w = pure Y MY U (x.hom.app U w) (y.hom.app U w)) →
        ∀ U w, (F.map z ≫ r.hom).hom.app U w =
          pure X MX U ((F.map x ≫ s.hom).hom.app U w)
            ((F.map y ≫ t.b.hom).hom.app U w) := by
  obtain ⟨I, hi⟩ := algebraicLift F V adj DY DX t.d t.hd
  have hsD := restrictedSemilinear F Y X t MY MX s hsa
  have hbD := coefficientSemilinear F Y X t
  rw [← hi] at hsD hbD
  obtain ⟨es, hes⟩ := linearIsoOfTransport F I (restrictModule daY MY)
    (restrictModule daX MX) s hs hsD
  obtain ⟨eb, heb⟩ := linearIsoOfTransport F I (coefficientModule Y.db)
    (coefficientModule X.db) t.b t.hb.1 hbD
  obtain ⟨σ, hσn, hσ⟩ := RingedTensor.exists_inverseImageTensorComparison DY DX F I V adj
  let := monoidalCategory DX
  let e := σ (restrictModule daY MY) (coefficientModule Y.db) ≪≫
    MonoidalCategory.tensorIso es eb
  let r := (I.moduleUnderlying.app (tensorModule Y MY)).symm ≪≫
    (RingedTensor.underlying DX).mapIso e
  have he (U : Eᵒᵖ) (m : (I.modules.obj (restrictModule daY MY)).val.obj U)
      (b : (I.modules.obj (coefficientModule Y.db)).val.obj U) :
      ((MonoidalCategory.tensorIso es eb).hom).val.app U (RingedTensor.pure DX _ _ U m b) =
        pure X MX U (es.hom.val.app U m) (eb.hom.val.app U b) :=
    RingedTensor.pure_map DX es.hom eb.hom U m b
  refine ⟨r, ?_, ?_⟩
  · intro T x y z hz U w
    have hh := I.moduleAdd (tensorModule Y MY) T x y z hz U w
    exact (congrArg (e.hom.val.app U) hh).trans ((e.hom.val.app U).hom.map_add _ _)
  · intro T x y z hz U w
    have hh := hσ (restrictModule daY MY) (coefficientModule Y.db) T x y z hz U w
    change (MonoidalCategory.tensorIso es eb).hom.val.app U
      ((σ _ _).hom.val.app U ((F.map z ≫
        I.moduleUnderlying.inv.app (tensorModule Y MY)).hom.app U w)) = _
    rw [hh, he]
    have hs' := congrArg (fun k ↦ k.hom.app U w)
      (congrArg (fun k ↦ F.map x ≫
        I.moduleUnderlying.inv.app (restrictModule daY MY) ≫ k) hes)
    have hb' := congrArg (fun k ↦ k.hom.app U w)
      (congrArg (fun k ↦ F.map y ≫
        I.moduleUnderlying.inv.app (coefficientModule Y.db) ≫ k) heb)
    simp only [Iso.inv_hom_id_app_assoc] at hs' hb'
    change es.hom.val.app U
      ((F.map x ≫ I.moduleUnderlying.inv.app (restrictModule daY MY)).hom.app U w) =
        (F.map x ≫ s.hom).hom.app U w at hs'
    change eb.hom.val.app U
      ((F.map y ≫ I.moduleUnderlying.inv.app (coefficientModule Y.db)).hom.app U w) =
        (F.map y ≫ t.b.hom).hom.app U w at hb'
    exact congrArg₂ (pure X MX U) hs' hb'

private def abLift {H G : Sheaf J AddCommGrpCat.{u}}
    (f : abSets H ⟶ abSets G)
    (hf : ∀ U (x y : H.obj.obj U), f.hom.app U (x + y) =
      @Add.add (G.obj.obj U) inferInstance (f.hom.app U x) (f.hom.app U y)) : H ⟶ G :=
  ⟨{ app := fun U ↦ AddCommGrpCat.ofHom
       { toFun := f.hom.app U
         map_add' := hf U
         map_zero' := by
           have h := hf U 0 0
           simp only [zero_add] at h
           exact add_eq_left.mp h.symm }
     naturality := by
       intro U V i
       ext x
       exact CategoryTheory.congr_fun (f.hom.naturality i) x }⟩

private theorem ab_pure_hom_ext
    (R : Sheaf J CommRingCat.{u})
    (M N : SheafOfModules.{u} (RingedTensor.ringSheaf R))
    {H : Sheaf J AddCommGrpCat.{u}}
    (f g : moduleAb ((monoidalCategory R).tensorObj M N) ⟶ H)
    (h : ∀ U m n, f.hom.app U (RingedTensor.pure R M N U m n) =
      g.hom.app U (RingedTensor.pure R M N U m n)) : f = g := by
  let e := (toSheaf (RingedTensor.ringSheaf R)).mapIso (tensorObjIsoSheafification M N)
  apply (cancel_epi e.inv).mp
  apply ((CategoryTheory.sheafificationAdjunction J AddCommGrpCat.{u}).homEquiv
    ((PresheafOfModules.toPresheaf _).obj (M.val ⊗ N.val)) H).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  ext U t
  change f.hom.app U ((tensorObjIsoSheafification M N).inv.val.app U
      (((PresheafOfModules.sheafificationAdjunction
        (𝟙 (RingedTensor.ringSheaf R).obj)).unit.app (M.val ⊗ N.val)).app U t)) =
    g.hom.app U ((tensorObjIsoSheafification M N).inv.val.app U
      (((PresheafOfModules.sheafificationAdjunction
        (𝟙 (RingedTensor.ringSheaf R).obj)).unit.app (M.val ⊗ N.val)).app U t))
  induction t using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul m n => exact h U m n
  | add t t' ht ht' => simp only [map_add, ht, ht']

private theorem additiveLiftOfTransport
    (F : Sheaf J (Type u) ⥤ Sheaf K (Type u)) [PreservesFiniteLimits F]
    {R : Sheaf J CommRingCat.{u}} {S : Sheaf K CommRingCat.{u}}
    (I : AlgebraicInverseImage F R S)
    (M : SheafOfModules.{u} (RingedTensor.ringSheaf R))
    (H : Sheaf K AddCommGrpCat.{u}) (f : F.obj (abSets (moduleAb M)) ⟶ abSets H)
    (ha : ∀ (T : Sheaf J (Type u)) (x y z : T ⟶ abSets (moduleAb M)),
      (∀ U w, @id (M.val.obj U) (z.hom.app U w) =
        @id (M.val.obj U) (x.hom.app U w) + @id (M.val.obj U) (y.hom.app U w)) →
      ∀ U w, (F.map z ≫ f).hom.app U w =
        @Add.add (H.obj.obj U) inferInstance ((F.map x ≫ f).hom.app U w)
          ((F.map y ≫ f).hom.app U w)) :
    ∃ g : moduleAb (I.modules.obj M) ⟶ H,
      (sheafCompose K (CategoryTheory.forget AddCommGrpCat)).map g =
        I.moduleUnderlying.hom.app M ≫ f := by
  let aM := fromProd _ _ ≫ addition R M
  let aI := fromProd _ _ ≫ addition S (I.modules.obj M)
  let aH : abSets H ⊗ abSets H ⟶ abSets H :=
    ⟨{ app := fun U ↦ TypeCat.ofHom (fun x ↦
         @Add.add (H.obj.obj U) inferInstance x.1 x.2)
       naturality := by intro U V i; ext x; exact ((H.obj.map i).hom.map_add _ _).symm }⟩
  let aH' := fromProd _ _ ≫ aH
  have hIA := binary_of_graph F _ _ _ aM aI
    (fun U x y ↦ @Add.add (M.val.obj U) inferInstance x y)
    (fun U x y ↦ @Add.add ((I.modules.obj M).val.obj U) inferInstance x y)
    (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (I.moduleAdd M)
  have hHA := binary_of_graph F f f f aM aH'
    (fun U x y ↦ @Add.add (M.val.obj U) inferInstance x y)
    (fun U x y ↦ @Add.add (H.obj.obj U) inferInstance x y)
    (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) ha
  have hh := descend_binary F (I.moduleUnderlying.app M) (I.moduleUnderlying.app M)
    (I.moduleUnderlying.app M) aM aI aH' f f f hIA hHA
  have hadd := binary_hom_sections _ _ _ aI aH'
    (fun U x y ↦ @Add.add ((I.modules.obj M).val.obj U) inferInstance x y)
    (fun U x y ↦ @Add.add (H.obj.obj U) inferInstance x y)
    (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) hh
  exact ⟨abLift (I.moduleUnderlying.hom.app M ≫ f) hadd, rfl⟩

private theorem image_tensor_hom_ext
    (F : Sheaf J (Type u) ⥤ Sheaf K (Type u))
    (V : Sheaf K (Type u) ⥤ Sheaf J (Type u)) (adj : F ⊣ V)
    [PreservesFiniteLimits F]
    {R : Sheaf J CommRingCat.{u}} {S : Sheaf K CommRingCat.{u}}
    (I : AlgebraicInverseImage F R S)
    (M N : SheafOfModules.{u} (RingedTensor.ringSheaf R))
    (H : Sheaf K AddCommGrpCat.{u})
    (f g : F.obj ((RingedTensor.underlying R).obj
      ((monoidalCategory R).tensorObj M N)) ⟶ abSets H)
    (hf : ∀ (T : Sheaf J (Type u)) (x y z : T ⟶
        (RingedTensor.underlying R).obj ((monoidalCategory R).tensorObj M N)),
      (∀ U w, @id (((monoidalCategory R).tensorObj M N).val.obj U) (z.hom.app U w) =
        @id (((monoidalCategory R).tensorObj M N).val.obj U) (x.hom.app U w) +
          @id (((monoidalCategory R).tensorObj M N).val.obj U) (y.hom.app U w)) →
      ∀ U w, (F.map z ≫ f).hom.app U w =
        @Add.add (H.obj.obj U) inferInstance ((F.map x ≫ f).hom.app U w)
          ((F.map y ≫ f).hom.app U w))
    (hg : ∀ (T : Sheaf J (Type u)) (x y z : T ⟶
        (RingedTensor.underlying R).obj ((monoidalCategory R).tensorObj M N)),
      (∀ U w, @id (((monoidalCategory R).tensorObj M N).val.obj U) (z.hom.app U w) =
        @id (((monoidalCategory R).tensorObj M N).val.obj U) (x.hom.app U w) +
          @id (((monoidalCategory R).tensorObj M N).val.obj U) (y.hom.app U w)) →
      ∀ U w, (F.map z ≫ g).hom.app U w =
        @Add.add (H.obj.obj U) inferInstance ((F.map x ≫ g).hom.app U w)
          ((F.map y ≫ g).hom.app U w))
    (h : F.map (RingedTensor.pureSheaf R M N) ≫ f =
      F.map (RingedTensor.pureSheaf R M N) ≫ g) : f = g := by
  let : F.Braided := Functor.Braided.ofChosenFiniteProducts F
  obtain ⟨f', hf'⟩ := additiveLiftOfTransport F I
    ((monoidalCategory R).tensorObj M N) H f hf
  obtain ⟨g', hg'⟩ := additiveLiftOfTransport F I
    ((monoidalCategory R).tensorObj M N) H g hg
  obtain ⟨b, hb, _⟩ := RingedTensor.exists_inverseImageTensorPairing R S F I M N
  have : IsIso b := RingedTensor.inverseImageTensorPairing_isIso R S F V adj I M N b hb
  have hp : RingedTensor.inverseImagePurePairing R S F I M N ≫
      (sheafCompose K (CategoryTheory.forget AddCommGrpCat)).map f' =
    RingedTensor.inverseImagePurePairing R S F I M N ≫
      (sheafCompose K (CategoryTheory.forget AddCommGrpCat)).map g' := by
    rw [hf', hg']
    dsimp only [RingedTensor.inverseImagePurePairing]
    simp only [Category.assoc, Iso.inv_hom_id_app_assoc]
    exact congrArg (fun k ↦
      ((I.moduleUnderlying.hom.app M) ⊗ₘ (I.moduleUnderlying.hom.app N)) ≫
        Functor.LaxMonoidal.μ F _ _ ≫ k) h
  have he : (toSheaf (RingedTensor.ringSheaf S)).map b ≫ f' =
      (toSheaf (RingedTensor.ringSheaf S)).map b ≫ g' := by
    apply ab_pure_hom_ext S (I.modules.obj M) (I.modules.obj N)
    intro U m n
    change f'.hom.app U (b.val.app U (RingedTensor.pure S _ _ U m n)) =
      g'.hom.app U (b.val.app U (RingedTensor.pure S _ _ U m n))
    rw [hb]
    exact congrArg (fun k ↦ k.hom.app U (m, n)) hp
  have he' := (cancel_epi ((toSheaf (RingedTensor.ringSheaf S)).map b)).mp he
  apply (cancel_epi (I.moduleUnderlying.hom.app ((monoidalCategory R).tensorObj M N))).mp
  rw [← hf', ← hg', he']

private theorem pairMate
    (F : Sheaf J (Type u) ⥤ Sheaf K (Type u))
    (V : Sheaf K (Type u) ⥤ Sheaf J (Type u)) (adj : F ⊣ V)
    {T : Sheaf J (Type u)} {A B : Sheaf K (Type u)}
    (a : F.obj T ⟶ A) (b : F.obj T ⟶ B) :
    let : PreservesLimitsOfSize.{u, u} V := adj.rightAdjoint_preservesLimits
    adj.homEquiv T (A ⨯ B) (prod.lift a b) =
      prod.lift (adj.homEquiv T A a) (adj.homEquiv T B b) ≫
        inv (prodComparison V A B) := by
  let : PreservesLimitsOfSize.{u, u} V := adj.rightAdjoint_preservesLimits
  apply (cancel_mono (prodComparison V A B)).mp
  apply prod.hom_ext
  · simp only [Category.assoc, IsIso.inv_hom_id_assoc, prod.lift_fst]
    rw [prodComparison_fst, ← adj.homEquiv_naturality_right]
    simp only [prod.lift_fst]
  · simp only [Category.assoc, IsIso.inv_hom_id_assoc, prod.lift_snd]
    rw [prodComparison_snd, ← adj.homEquiv_naturality_right]
    simp only [prod.lift_snd]

private theorem adjunct_formula_iff
    (F : Sheaf J (Type u) ⥤ Sheaf K (Type u))
    (V : Sheaf K (Type u) ⥤ Sheaf J (Type u)) (adj : F ⊣ V)
    {DY AY : Sheaf J CommRingCat.{u}} {DX AX : Sheaf K CommRingCat.{u}}
    {daY : DY ⟶ AY} {daX : DX ⟶ AX}
    (Y : Presentation daY) (X : Presentation daX)
    (MY : SheafOfModules.{u} (RingedTensor.ringSheaf AY))
    (MX : SheafOfModules.{u} (RingedTensor.ringSheaf AX))
    (s : F.obj (abSets (moduleAb MY)) ≅ abSets (moduleAb MX))
    (b : F.obj (ringSets Y.B) ≅ ringSets X.B)
    (r : F.obj (abSets (moduleAb (tensorModule Y MY))) ≅
      abSets (moduleAb (tensorModule X MX))) :
    HasAdjunctFormula F V adj Y X MY MX s b r ↔
      F.map (pairing Y MY) ≫ r.hom =
        prod.lift (F.map (CartesianMonoidalCategory.fst _ _) ≫ s.hom)
          (F.map (CartesianMonoidalCategory.snd _ _) ≫ b.hom) ≫
            (CartesianMonoidalCategory.lift prod.fst prod.snd ≫ pairing X MX) := by
  let : PreservesLimitsOfSize.{u, u} V := adj.rightAdjoint_preservesLimits
  change _ ↔ _
  rw [← (adj.homEquiv _ _).injective.eq_iff]
  rw [adj.homEquiv_naturality_left, adj.homEquiv_naturality_right, pairMate]
  simp only [adj.homEquiv_naturality_left]
  rfl

private theorem coefficient_maps
    {D A : Sheaf J CommRingCat.{u}} {da : D ⟶ A}
    {Y Y' : Presentation da} (q : CoefficientChange Y Y')
    (M : SheafOfModules.{u} (RingedTensor.ringSheaf A)) :
    ∃ j : moduleAb (tensorModule Y M) ⟶ moduleAb (tensorModule Y' M),
      IsTensorMap q M j := by
  let f : coefficientModule Y.db ⟶ coefficientModule Y'.db :=
    { val :=
        { app := fun U ↦ ModuleCat.ofHom
            (X := (coefficientModule Y.db).val.obj U)
            (Y := (coefficientModule Y'.db).val.obj U)
            { toFun := q.q.hom.app U
              map_add' := (q.q.hom.app U).hom.map_add
              map_smul' := by
                intro r b
                change Y.B.obj.obj U at b
                change q.q.hom.app U (Y.db.hom.app U r * b) =
                  Y'.db.hom.app U r * q.q.hom.app U b
                rw [map_mul]
                exact congrArg (fun z ↦ z * q.q.hom.app U b)
                  (congrArg (fun k ↦ k.hom.app U r) q.db_comm) }
          naturality := by
            intro U V i
            ext b
            exact ConcreteCategory.congr_hom (q.q.hom.naturality i) b } }
  let j := (toSheaf (RingedTensor.ringSheaf D)).map
    ((monoidalCategory D).tensorHom (𝟙 (restrictModule da M)) f)
  refine ⟨j, ?_⟩
  intro U m b
  change ((monoidalCategory D).tensorHom (𝟙 (restrictModule da M)) f).val.app U
    (RingedTensor.pure D _ _ U m b) = _
  exact RingedTensor.pure_map D (𝟙 (restrictModule da M)) f U m b

private theorem fromProd_lift
    {X Y T : Sheaf J (Type u)} (a : T ⟶ X) (b : T ⟶ Y) :
    prod.lift a b ≫ CartesianMonoidalCategory.lift prod.fst prod.snd =
      CartesianMonoidalCategory.lift a b := by
  apply CartesianMonoidalCategory.hom_ext <;>
    simp only [Category.assoc, CartesianMonoidalCategory.lift_fst,
      CartesianMonoidalCategory.lift_snd, prod.lift_fst, prod.lift_snd]

section Action
variable {D A : Sheaf J CommRingCat.{u}} {da : D ⟶ A}
  (P : Presentation da)

private abbrev rawRing := pushout P.db.hom da.hom
private abbrev rawB : P.B.obj ⟶ rawRing P := pushout.inl _ _
private abbrev rawA : A.obj ⟶ rawRing P := pushout.inr _ _
private abbrev rawToRing : rawRing P ⟶ P.R.obj :=
  pushout.desc P.iB.hom P.iA.hom (congrArg (fun k ↦ k.hom) P.pushout.w.symm)

private theorem rawToRing_local :
    Presheaf.IsLocallyInjective J (rawToRing P) ∧
      Presheaf.IsLocallySurjective J (rawToRing P) := by
  have : HasSheafify J CommRingCat.{u} := inferInstance
  let L := presheafToSheaf J CommRingCat.{u}
  let adj := CategoryTheory.sheafificationAdjunction J CommRingCat.{u}
  let ε (Q : Sheaf J CommRingCat.{u}) := asIso (adj.counit.app Q)
  have h := (IsPushout.of_hasPushout P.db.hom da.hom).map L
  have hR : IsPushout (L.map P.db.hom) (L.map da.hom)
      ((ε P.B).hom ≫ P.iB) ((ε A).hom ≫ P.iA) := by
    apply P.pushout.flip.of_iso' (ε D) (ε P.B) (ε A) (Iso.refl P.R)
    · exact (adj.counit.naturality P.db).symm
    · exact (adj.counit.naturality da).symm
    · simp
    · simp
  let e := h.isoIsPushout _ _ hR
  have he : e.hom = L.map (rawToRing P) ≫ (ε P.R).hom := by
    apply h.hom_ext
    · simp only [e, IsPushout.inl_isoIsPushout_hom]
      rw [← L.map_comp_assoc]
      simp only [rawToRing, pushout.inl_desc]
      exact (adj.counit.naturality P.iB).symm
    · simp only [e, IsPushout.inr_isoIsPushout_hom]
      rw [← L.map_comp_assoc]
      simp only [rawToRing, pushout.inr_desc]
      exact (adj.counit.naturality P.iA).symm
  have : IsIso (L.map (rawToRing P)) := by
    have he' : L.map (rawToRing P) = e.hom ≫ (ε P.R).inv := by
      rw [he, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    rw [he']
    infer_instance
  exact (J.W_iff_isLocallyBijective (rawToRing P)).mp ((J.W_iff _).mpr inferInstance)

private noncomputable def rawEquiv (U : Cᵒᵖ) :
    letI := (P.db.hom.app U).hom.toAlgebra
    letI := (da.hom.app U).hom.toAlgebra
    P.B.obj.obj U ⊗[D.obj.obj U] A.obj.obj U ≃+* (rawRing P).obj U := by
  letI := (P.db.hom.app U).hom.toAlgebra
  letI := (da.hom.app U).hom.toAlgebra
  let h := (IsPushout.of_hasPushout P.db.hom da.hom).app U
  exact ((CommRingCat.isPushout_tensorProduct (D.obj.obj U) (P.B.obj.obj U)
    (A.obj.obj U)).isoIsPushout _ _ h).commRingCatIsoToRingEquiv

private theorem rawEquiv_pure (U : Cᵒᵖ) (b : P.B.obj.obj U) (a : A.obj.obj U) :
    letI := (P.db.hom.app U).hom.toAlgebra
    letI := (da.hom.app U).hom.toAlgebra
    rawEquiv P U (b ⊗ₜ[D.obj.obj U] a) =
      (rawB P).app U b * (rawA P).app U a := by
  let := (P.db.hom.app U).hom.toAlgebra
  let := (da.hom.app U).hom.toAlgebra
  let h := (IsPushout.of_hasPushout P.db.hom da.hom).app U
  let e := (CommRingCat.isPushout_tensorProduct (D.obj.obj U) (P.B.obj.obj U)
    (A.obj.obj U)).isoIsPushout _ _ h
  have hl := congrArg (fun k ↦ k b)
    ((CommRingCat.isPushout_tensorProduct (D.obj.obj U) (P.B.obj.obj U)
      (A.obj.obj U)).inl_isoIsPushout_hom _ _ h)
  have hr := congrArg (fun k ↦ k a)
    ((CommRingCat.isPushout_tensorProduct (D.obj.obj U) (P.B.obj.obj U)
      (A.obj.obj U)).inr_isoIsPushout_hom _ _ h)
  change e.hom (b ⊗ₜ[D.obj.obj U] a) = _
  have ht : b ⊗ₜ[D.obj.obj U] a =
      (b ⊗ₜ[D.obj.obj U] (1 : A.obj.obj U)) *
        ((1 : P.B.obj.obj U) ⊗ₜ[D.obj.obj U] a) := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  rw [ht, map_mul]
  exact congrArg₂ (fun x y ↦ x * y) hl hr

private abbrev rawModule
    (M : SheafOfModules.{u} (RingedTensor.ringSheaf A)) :=
  (restrictModule da M).val ⊗ (coefficientModule P.db).val

@[instance_reducible]
private noncomputable def rawModuleAction
    (M : SheafOfModules.{u} (RingedTensor.ringSheaf A)) (U : Cᵒᵖ) :
    Module ((rawRing P).obj U) ((rawModule P M).obj U) := by
  letI := (P.db.hom.app U).hom.toAlgebra
  letI := (da.hom.app U).hom.toAlgebra
  letI := Module.compHom (M.val.obj U) (da.hom.app U).hom
  letI := CategoryTheory.tensorAction (V := M.val.obj U)
    (da.hom.app U).hom (P.db.hom.app U).hom
  letI := (TensorProduct.comm (D.obj.obj U) (M.val.obj U)
    (P.B.obj.obj U)).toAddEquiv.module (P.B.obj.obj U ⊗[D.obj.obj U] A.obj.obj U)
  change Module ((rawRing P).obj U)
    (TensorProduct (D.obj.obj U) (M.val.obj U) (P.B.obj.obj U))
  exact Module.compHom _ (rawEquiv P U).symm.toRingHom

private theorem rawModuleAction_pure
    (M : SheafOfModules.{u} (RingedTensor.ringSheaf A))
    (U : Cᵒᵖ) (b v : P.B.obj.obj U) (a : A.obj.obj U) (m : M.val.obj U) :
    letI := Module.compHom (M.val.obj U) (da.hom.app U).hom
    @SMul.smul _ _ (rawModuleAction P M U).toSMul
      ((rawB P).app U b * (rawA P).app U a)
      (TensorProduct.tmul (D.obj.obj U) m
        (show (coefficientModule P.db).val.obj U from v)) =
      TensorProduct.tmul (D.obj.obj U) (a • m)
        (show (coefficientModule P.db).val.obj U from b * v) := by
  let := (P.db.hom.app U).hom.toAlgebra
  let := (da.hom.app U).hom.toAlgebra
  let := Module.compHom (M.val.obj U) (da.hom.app U).hom
  let := CategoryTheory.tensorAction (V := M.val.obj U)
    (da.hom.app U).hom (P.db.hom.app U).hom
  rw [← rawEquiv_pure P U b a]
  change (TensorProduct.comm (D.obj.obj U) (M.val.obj U) (P.B.obj.obj U)).symm
    ((rawEquiv P U).symm (rawEquiv P U (b ⊗ₜ[D.obj.obj U] a)) •
      (v ⊗ₜ[D.obj.obj U] m)) = _
  rw [RingEquiv.symm_apply_apply, CategoryTheory.tensorAction_tmul]
  rfl

private theorem rawModuleAction_restrict
    (M : SheafOfModules.{u} (RingedTensor.ringSheaf A))
    {U V : Cᵒᵖ} (f : U ⟶ V) (z : (rawRing P).obj U) (n : (rawModule P M).obj U) :
    (rawModule P M).map f (@SMul.smul _ _ (rawModuleAction P M U).toSMul z n) =
      @SMul.smul _ _ (rawModuleAction P M V).toSMul
        ((rawRing P).map f z) ((rawModule P M).map f n) := by
  let (W : Cᵒᵖ) := (P.db.hom.app W).hom.toAlgebra
  let (W : Cᵒᵖ) := (da.hom.app W).hom.toAlgebra
  let (W : Cᵒᵖ) := Module.compHom (M.val.obj W) (da.hom.app W).hom
  let (W : Cᵒᵖ) := rawModuleAction P M W
  change (rawModule P M).map f (z • n) =
    (rawRing P).map f z • (show (rawModule P M).obj V from (rawModule P M).map f n)
  obtain ⟨z, rfl⟩ := (rawEquiv P U).surjective z
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero, zero_smul]
  | add z z' hz hz' => simp only [map_add, add_smul, hz, hz']
  | tmul b a =>
    rw [rawEquiv_pure, map_mul]
    have hb : (rawRing P).map f ((rawB P).app U b) =
        (rawB P).app V (P.B.obj.map f b) :=
      ConcreteCategory.congr_hom ((rawB P).naturality f).symm b
    have ha : (rawRing P).map f ((rawA P).app U a) =
        (rawA P).app V (A.obj.map f a) :=
      ConcreteCategory.congr_hom ((rawA P).naturality f).symm a
    rw [hb, ha]
    induction n using TensorProduct.induction_on with
    | zero => simp only [map_zero, smul_zero]
    | add n n' hn hn' => simp only [map_add, smul_add, hn, hn']
    | tmul m v =>
      change M.val.obj U at m
      change P.B.obj.obj U at v
      have hU := rawModuleAction_pure P M U b v a m
      have hV := rawModuleAction_pure P M V (P.B.obj.map f b)
        (P.B.obj.map f v) (A.obj.map f a) (M.val.map f m)
      dsimp only [sheafCompose] at hU hV
      refine (congrArg ((rawModule P M).map f) hU).trans ?_
      have hm := PresheafOfModules.Monoidal.tensorObj_map_tmul
        (M₁ := (restrictModule da M).val) (M₂ := (coefficientModule P.db).val) f
        (show (restrictModule da M).val.obj U from a • m)
        (show (coefficientModule P.db).val.obj U from b * v)
      refine hm.trans ?_
      have hn := PresheafOfModules.Monoidal.tensorObj_map_tmul
        (M₁ := (restrictModule da M).val) (M₂ := (coefficientModule P.db).val) f
        (show (restrictModule da M).val.obj U from m)
        (show (coefficientModule P.db).val.obj U from v)
      refine Eq.trans ?_ (hV.symm.trans (congrArg (fun y ↦
        @SMul.smul _ _ (rawModuleAction P M V).toSMul
          ((rawB P).app V (P.B.obj.map f b) *
            (rawA P).app V (A.obj.map f a)) y) hn).symm)
      change (show M.val.obj V from M.val.map f (a • m)) ⊗ₜ[D.obj.obj V]
        (show (coefficientModule P.db).val.obj V from P.B.obj.map f (b * v)) = _
      have hs : M.val.map f (a • m) =
          (A.obj.map f a) • (show M.val.obj V from M.val.map f m) :=
        M.val.map_smul f a m
      rw [hs, map_mul]


private theorem tensor_action
    (M : SheafOfModules.{u} (RingedTensor.ringSheaf A)) :
    ∃ h : ∀ U : Cᵒᵖ, Module (P.R.obj.obj U) ((tensorModule P M).val.obj U),
      IsTensorAction P M h := by
  let R₀ := (rawRing P) ⋙ forget₂ CommRingCat RingCat
  let α : R₀ ⟶ (RingedTensor.ringSheaf P.R).obj :=
    Functor.whiskerRight (rawToRing P) (forget₂ CommRingCat RingCat)
  have hα := rawToRing_local P
  have : Presheaf.IsLocallyInjective J (rawToRing P) := hα.1
  have : Presheaf.IsLocallySurjective J (rawToRing P) := hα.2
  have : Presheaf.IsLocallyInjective J α := by
    constructor
    intro U x y h
    exact Presheaf.equalizerSieve_mem J (rawToRing P) x y h
  have : Presheaf.IsLocallySurjective J α := by
    constructor
    intro U x
    exact Presheaf.imageSieve_mem J (rawToRing P) x
  let : ∀ U : Cᵒᵖ, Module (R₀.obj U) ((rawModule P M).presheaf.obj U) :=
    rawModuleAction P M
  let Q : PresheafOfModules.{u} R₀ := PresheafOfModules.ofPresheaf
    (rawModule P M).presheaf (fun {_ _} f z x ↦ rawModuleAction_restrict P M f z x)
  let H := moduleAb (tensorModule P M)
  let φ : Q.presheaf ⟶ H.obj := (PresheafOfModules.toPresheaf _).map
    (RingedTensor.pureMap D (restrictModule da M) (coefficientModule P.db))
  have : Presheaf.IsLocallyInjective J φ := by
    change Presheaf.IsLocallyInjective J (toSheafify J (rawModule P M).presheaf ≫
      ((toSheaf (RingedTensor.ringSheaf D)).map
        (tensorObjIsoSheafification (restrictModule da M) (coefficientModule P.db)).inv).hom)
    infer_instance
  have : Presheaf.IsLocallySurjective J φ := by
    change Presheaf.IsLocallySurjective J (toSheafify J (rawModule P M).presheaf ≫
      ((toSheaf (RingedTensor.ringSheaf D)).map
        (tensorObjIsoSheafification (restrictModule da M) (coefficientModule P.db)).inv).hom)
    infer_instance
  let h := PresheafOfModules.Sheafify.module (M₀ := Q) α φ
  refine ⟨h, ?_, ?_⟩
  · intro U V f z n
    exact PresheafOfModules.Sheafify.map_smul (M₀ := Q) α φ U f z n
  · intro U a v w m
    let z := (rawB P).app U v * (rawA P).app U a
    have hz : α.app U z = P.iA.hom.app U a * P.iB.hom.app U v := by
      change (rawToRing P).app U z = _
      dsimp only [z]
      rw [map_mul]
      have hb := congrArg (fun k ↦ k.app U v)
        (pushout.inl_desc P.iB.hom P.iA.hom
          (congrArg (fun k ↦ k.hom) P.pushout.w.symm))
      have ha := congrArg (fun k ↦ k.app U a)
        (pushout.inr_desc P.iB.hom P.iA.hom
          (congrArg (fun k ↦ k.hom) P.pushout.w.symm))
      change (rawToRing P).app U ((rawB P).app U v) = _ at hb
      change (rawToRing P).app U ((rawA P).app U a) = _ at ha
      rw [hb, ha, mul_comm]
    let := Module.compHom (M.val.obj U) (da.hom.app U).hom
    have ht := PresheafOfModules.Sheafify.map_smul_eq (M₀ := Q) α φ
      (α.app U z) (φ.app U (m ⊗ₜ[D.obj.obj U] w)) (𝟙 U) z (by simp)
      (m ⊗ₜ[D.obj.obj U] w) (by simp)
    rw [hz] at ht
    rw [H.obj.map_id] at ht
    exact ht.trans (congrArg (φ.app U) (rawModuleAction_pure P M U v w a m))

end Action


attribute [local irreducible] monoidalCategory

private theorem transport_action
    (F : Sheaf J (Type u) ⥤ Sheaf K (Type u))
    (V : Sheaf K (Type u) ⥤ Sheaf J (Type u)) (adj : F ⊣ V)
    [PreservesFiniteLimits F]
    {DY AY : Sheaf J CommRingCat.{u}} {DX AX : Sheaf K CommRingCat.{u}}
    {daY : DY ⟶ AY} {daX : DX ⟶ AX}
    (Y : Presentation daY) (X : Presentation daX) (t : Transport F Y X)
    (MY : SheafOfModules.{u} (RingedTensor.ringSheaf AY))
    (MX : SheafOfModules.{u} (RingedTensor.ringSheaf AX))
    (r : F.obj (abSets (moduleAb (tensorModule Y MY))) ≅
      abSets (moduleAb (tensorModule X MX)))
    (hr : IsAdditiveTransport F (moduleAb (tensorModule Y MY))
      (moduleAb (tensorModule X MX)) r)
    (hY : ∀ U : Cᵒᵖ, Module (Y.R.obj.obj U) ((tensorModule Y MY).val.obj U))
    (hres : ∀ {U V : Cᵒᵖ} (f : U ⟶ V) (z : Y.R.obj.obj U)
      (n : (tensorModule Y MY).val.obj U),
      (tensorModule Y MY).val.map f (@SMul.smul _ _ (hY U).toSMul z n) =
        @SMul.smul _ _ (hY V).toSMul (Y.R.obj.map f z)
          ((tensorModule Y MY).val.map f n)) :
    ∃ hX : ∀ U : Eᵒᵖ, Module (X.R.obj.obj U) ((tensorModule X MX).val.obj U),
      (∀ {U V : Eᵒᵖ} (f : U ⟶ V) (z : X.R.obj.obj U)
        (n : (tensorModule X MX).val.obj U),
        (tensorModule X MX).val.map f (@SMul.smul _ _ (hX U).toSMul z n) =
          @SMul.smul _ _ (hX V).toSMul (X.R.obj.map f z)
            ((tensorModule X MX).val.map f n)) ∧
      IsSemilinearTransport F Y.R X.R (moduleAb (tensorModule Y MY))
        (moduleAb (tensorModule X MX)) (fun U ↦ (hY U).toSMul)
        (fun U ↦ (hX U).toSMul) t.c r := by
  let (U : Cᵒᵖ) : Module ((RingedTensor.ringSheaf Y.R).obj.obj U)
      ((tensorModule Y MY).val.presheaf.obj U) := hY U
  let N : SheafOfModules.{u} (RingedTensor.ringSheaf Y.R) :=
    ⟨PresheafOfModules.ofPresheaf (tensorModule Y MY).val.presheaf
        (fun {_ _} f z n ↦ hres f z n),
      (tensorModule Y MY).isSheaf⟩
  obtain ⟨I, hi⟩ := algebraicLift F V adj Y.R X.R t.c t.hc
  obtain ⟨f, hf⟩ := additiveLiftOfTransport F I N
    (moduleAb (tensorModule X MX)) r.hom hr
  have : IsIso ((sheafCompose K (CategoryTheory.forget AddCommGrpCat)).map f) := by
    rw [hf]
    infer_instance
  have : IsIso f := isIso_of_reflects_iso f
    (sheafCompose K (CategoryTheory.forget AddCommGrpCat))
  let e (U : Eᵒᵖ) : (I.modules.obj N).val.obj U ≃+
      (tensorModule X MX).val.obj U := Iso.addCommGroupIsoToAddEquiv
    (((CategoryTheory.evaluation Eᵒᵖ AddCommGrpCat).obj U).mapIso (asIso f.hom))
  let hX (U : Eᵒᵖ) : Module (X.R.obj.obj U) ((tensorModule X MX).val.obj U) :=
    (e U).symm.module (X.R.obj.obj U)
  have he (U : Eᵒᵖ) (z : X.R.obj.obj U) (n : (I.modules.obj N).val.obj U) :
      f.hom.app U (z • n) = @SMul.smul _ _ (hX U).toSMul z (f.hom.app U n) := by
    change e U (z • n) = e U (z • (e U).symm (e U n))
    rw [AddEquiv.symm_apply_apply]
  refine ⟨hX, ?_, ?_⟩
  · intro U W g z n
    obtain ⟨m, rfl⟩ := (e U).surjective n
    change (tensorModule X MX).val.map g
        (@SMul.smul _ _ (hX U).toSMul z (f.hom.app U m)) =
      @SMul.smul _ _ (hX W).toSMul (X.R.obj.map g z)
        (show (tensorModule X MX).val.obj W from
          (tensorModule X MX).val.map g (f.hom.app U m))
    rw [← he]
    have hn := ConcreteCategory.congr_hom (f.hom.naturality g).symm m
    change (tensorModule X MX).val.map g (f.hom.app U (z • m)) = _
    have ht := ConcreteCategory.congr_hom (f.hom.naturality g).symm (z • m)
    change _ = f.hom.app W ((I.modules.obj N).val.map g (z • m)) at ht
    rw [(I.modules.obj N).val.map_smul] at ht
    exact ht.trans ((he W _ _).trans (congrArg
      (fun v ↦ @SMul.smul _ _ (hX W).toSMul (X.R.obj.map g z) v) hn.symm))
  · intro T a m n hn U w
    have ht := I.moduleSMul N T a m n hn U w
    have hc : (F.map a ≫ I.ringUnderlying.hom).hom.app U w =
        (F.map a ≫ t.c.hom).hom.app U w :=
      congrArg (fun e : F.obj (ringSets Y.R) ≅ ringSets X.R ↦
        (F.map a ≫ e.hom).hom.app U w) hi
    have hf' (k : T ⟶ abSets (moduleAb N)) :
        F.map k ≫ I.moduleUnderlying.inv.app N ≫
          (sheafCompose K (CategoryTheory.forget AddCommGrpCat)).map f = F.map k ≫ r.hom := by
      rw [hf]
      simp only [Iso.inv_hom_id_app_assoc]
    have hfn (k : T ⟶ abSets (moduleAb N)) :
        f.hom.app U ((F.map k ≫ I.moduleUnderlying.inv.app N).hom.app U w) =
          (F.map k ≫ r.hom).hom.app U w :=
      congrArg (fun q ↦ q.hom.app U w) (hf' k)
    exact (hfn n).symm.trans ((congrArg (f.hom.app U) ht).trans
      ((he U _ _).trans (congrArg₂
        (fun z v ↦ @SMul.smul _ _ (hX U).toSMul z v) hc (hfn m))))

private theorem normalized_additive_comparison
    (F : Sheaf J (Type u) ⥤ Sheaf K (Type u))
    (V : Sheaf K (Type u) ⥤ Sheaf J (Type u)) (adj : F ⊣ V)
    [PreservesFiniteLimits F]
    {DY AY : Sheaf J CommRingCat.{u}} {DX AX : Sheaf K CommRingCat.{u}}
    {daY : DY ⟶ AY} {daX : DX ⟶ AX}
    (Y : Presentation daY) (X : Presentation daX) (t : Transport F Y X)
    (MY : SheafOfModules.{u} (RingedTensor.ringSheaf AY))
    (MX : SheafOfModules.{u} (RingedTensor.ringSheaf AX))
    (s : F.obj (abSets (moduleAb MY)) ≅ abSets (moduleAb MX))
    (hs : IsAdditiveTransport F (moduleAb MY) (moduleAb MX) s)
    (hsa : IsSemilinearTransport F AY AX (moduleAb MY) (moduleAb MX)
      (fun U ↦ inferInstanceAs (SMul (AY.obj.obj U) (MY.val.obj U)))
      (fun U ↦ inferInstanceAs (SMul (AX.obj.obj U) (MX.val.obj U))) t.a s) :
    ∃ r : F.obj (abSets (moduleAb (tensorModule Y MY))) ≅
        abSets (moduleAb (tensorModule X MX)),
      IsAdditiveTransport F (moduleAb (tensorModule Y MY))
        (moduleAb (tensorModule X MX)) r ∧
      HasAdjunctFormula F V adj Y X MY MX s t.b r := by
  obtain ⟨r, hr, hp⟩ := additive_comparison F V adj Y X t MY MX s hs hsa
  refine ⟨r, hr, (adjunct_formula_iff F V adj Y X MY MX s t.b r).mpr ?_⟩
  rw [← Category.assoc, fromProd_lift]
  ext U w
  exact hp _ (CartesianMonoidalCategory.fst _ _) (CartesianMonoidalCategory.snd _ _)
    (pairing Y MY) (fun _ _ ↦ rfl) U w



private theorem pairing_graph
    (F : Sheaf J (Type u) ⥤ Sheaf K (Type u))
    (V : Sheaf K (Type u) ⥤ Sheaf J (Type u)) (adj : F ⊣ V)
    [PreservesFiniteLimits F]
    {DY AY : Sheaf J CommRingCat.{u}} {DX AX : Sheaf K CommRingCat.{u}}
    {daY : DY ⟶ AY} {daX : DX ⟶ AX}
    (Y : Presentation daY) (X : Presentation daX)
    (MY : SheafOfModules.{u} (RingedTensor.ringSheaf AY))
    (MX : SheafOfModules.{u} (RingedTensor.ringSheaf AX))
    (s : F.obj (abSets (moduleAb MY)) ≅ abSets (moduleAb MX))
    (b : F.obj (ringSets Y.B) ≅ ringSets X.B)
    (r : F.obj (abSets (moduleAb (tensorModule Y MY))) ≅
      abSets (moduleAb (tensorModule X MX)))
    (hp : HasAdjunctFormula F V adj Y X MY MX s b r)
    (T : Sheaf J (Type u)) (m : T ⟶ abSets (moduleAb MY)) (v : T ⟶ ringSets Y.B)
    (n : T ⟶ abSets (moduleAb (tensorModule Y MY)))
    (hn : ∀ U w, n.hom.app U w = pure Y MY U (m.hom.app U w) (v.hom.app U w)) :
    ∀ U w, (F.map n ≫ r.hom).hom.app U w =
      pure X MX U ((F.map m ≫ s.hom).hom.app U w)
        ((F.map v ≫ b.hom).hom.app U w) := by
  have hn' : n = CartesianMonoidalCategory.lift m v ≫ pairing Y MY := by
    ext U w
    exact hn U w
  have h := (adjunct_formula_iff F V adj Y X MY MX s b r).mp hp
  rw [← Category.assoc, fromProd_lift] at h
  have he : F.map n ≫ r.hom =
      CartesianMonoidalCategory.lift (F.map m ≫ s.hom) (F.map v ≫ b.hom) ≫
        pairing X MX := by
    rw [hn', F.map_comp, Category.assoc, h, ← Category.assoc]
    congr 1
    apply CartesianMonoidalCategory.hom_ext <;>
      simp only [Category.assoc, CartesianMonoidalCategory.lift_fst,
        CartesianMonoidalCategory.lift_snd, ← F.map_comp_assoc]
  intro U w
  exact congrArg (fun k ↦ k.hom.app U w) he

private theorem split_pair
    (F : Sheaf J (Type u) ⥤ Sheaf K (Type u)) [PreservesFiniteLimits F]
    (P Q : Sheaf J (Type u)) (U : Eᵒᵖ)
    (x : (F.obj P).obj.obj U) (y : (F.obj Q).obj.obj U) :
    ∃ w : (F.obj (P ⊗ Q)).obj.obj U,
      (F.map (CartesianMonoidalCategory.fst P Q)).hom.app U w = x ∧
      (F.map (CartesianMonoidalCategory.snd P Q)).hom.app U w = y := by
  let : F.Braided := Functor.Braided.ofChosenFiniteProducts F
  refine ⟨(Functor.LaxMonoidal.μ F P Q).hom.app U (x, y), ?_, ?_⟩
  · exact congrArg (fun k ↦ k.hom.app U (x, y)) (Functor.Monoidal.μ_fst F P Q)
  · exact congrArg (fun k ↦ k.hom.app U (x, y)) (Functor.Monoidal.μ_snd F P Q)

private theorem transported_action_pure
    (F : Sheaf J (Type u) ⥤ Sheaf K (Type u))
    (V : Sheaf K (Type u) ⥤ Sheaf J (Type u)) (adj : F ⊣ V)
    [PreservesFiniteLimits F]
    {DY AY : Sheaf J CommRingCat.{u}} {DX AX : Sheaf K CommRingCat.{u}}
    {daY : DY ⟶ AY} {daX : DX ⟶ AX}
    (Y : Presentation daY) (X : Presentation daX) (t : Transport F Y X)
    (MY : SheafOfModules.{u} (RingedTensor.ringSheaf AY))
    (MX : SheafOfModules.{u} (RingedTensor.ringSheaf AX))
    (s : F.obj (abSets (moduleAb MY)) ≅ abSets (moduleAb MX))
    (hsa : IsSemilinearTransport F AY AX (moduleAb MY) (moduleAb MX)
      (fun U ↦ inferInstanceAs (SMul (AY.obj.obj U) (MY.val.obj U)))
      (fun U ↦ inferInstanceAs (SMul (AX.obj.obj U) (MX.val.obj U))) t.a s)
    (r : F.obj (abSets (moduleAb (tensorModule Y MY))) ≅
      abSets (moduleAb (tensorModule X MX)))
    (hp : HasAdjunctFormula F V adj Y X MY MX s t.b r)
    (hY : ∀ U : Cᵒᵖ, Module (Y.R.obj.obj U) ((tensorModule Y MY).val.obj U))
    (hX : ∀ U : Eᵒᵖ, Module (X.R.obj.obj U) ((tensorModule X MX).val.obj U))
    (hYp : IsTensorAction Y MY hY)
    (hsm : IsSemilinearTransport F Y.R X.R (moduleAb (tensorModule Y MY))
      (moduleAb (tensorModule X MX)) (fun U ↦ (hY U).toSMul)
      (fun U ↦ (hX U).toSMul) t.c r) :
    ∀ (U : Eᵒᵖ) (x : AX.obj.obj U) (v w : X.B.obj.obj U) (m : MX.val.obj U),
      @SMul.smul _ _ (hX U).toSMul (X.iA.hom.app U x * X.iB.hom.app U v)
        (pure X MX U m w) = pure X MX U (x • m) (v * w) := by
  let A := ringSets AY
  let B := ringSets Y.B
  let M := abSets (moduleAb MY)
  let T := (A ⊗ B) ⊗ (M ⊗ B)
  let a : T ⟶ A := CartesianMonoidalCategory.fst _ _ ≫ CartesianMonoidalCategory.fst _ _
  let v₀ : T ⟶ B := CartesianMonoidalCategory.fst _ _ ≫ CartesianMonoidalCategory.snd _ _
  let m₀ : T ⟶ M := CartesianMonoidalCategory.snd _ _ ≫ CartesianMonoidalCategory.fst _ _
  let w₀ : T ⟶ B := CartesianMonoidalCategory.snd _ _ ≫ CartesianMonoidalCategory.snd _ _
  let av : T ⟶ ringSets Y.R := CartesianMonoidalCategory.lift
    (a ≫ (sheafCompose J (CategoryTheory.forget CommRingCat)).map Y.iA)
    (v₀ ≫ (sheafCompose J (CategoryTheory.forget CommRingCat)).map Y.iB) ≫ ringMul Y.R
  let n : T ⟶ abSets (moduleAb (tensorModule Y MY)) :=
    CartesianMonoidalCategory.lift m₀ w₀ ≫ pairing Y MY
  let am : T ⟶ M := CartesianMonoidalCategory.lift a m₀ ≫ action AY MY
  let vw : T ⟶ B := CartesianMonoidalCategory.lift v₀ w₀ ≫ ringMul Y.B
  let n' : T ⟶ abSets (moduleAb (tensorModule Y MY)) :=
    CartesianMonoidalCategory.lift am vw ≫ pairing Y MY
  intro U x v w m
  obtain ⟨av₁, ha, hv⟩ := split_pair F A B U (t.a.inv.hom.app U x) (t.b.inv.hom.app U v)
  obtain ⟨mw₁, hm, hw⟩ := split_pair F M B U (s.inv.hom.app U m) (t.b.inv.hom.app U w)
  obtain ⟨ξ, hav, hmw⟩ := split_pair F (A ⊗ B) (M ⊗ B) U av₁ mw₁
  have ea : (F.map a ≫ t.a.hom).hom.app U ξ = x := by
    dsimp only [a]
    rw [F.map_comp]
    change t.a.hom.hom.app U ((F.map (CartesianMonoidalCategory.fst A B)).hom.app U
      ((F.map (CartesianMonoidalCategory.fst (A ⊗ B) (M ⊗ B))).hom.app U ξ)) = x
    rw [hav, ha]
    exact congrArg (fun k ↦ k.hom.app U
      (show (ringSets AX).obj.obj U from x)) t.a.inv_hom_id
  have ev : (F.map v₀ ≫ t.b.hom).hom.app U ξ = v := by
    dsimp only [v₀]
    rw [F.map_comp]
    change t.b.hom.hom.app U ((F.map (CartesianMonoidalCategory.snd A B)).hom.app U
      ((F.map (CartesianMonoidalCategory.fst (A ⊗ B) (M ⊗ B))).hom.app U ξ)) = v
    rw [hav, hv]
    exact congrArg (fun k ↦ k.hom.app U
      (show (ringSets X.B).obj.obj U from v)) t.b.inv_hom_id
  have em : (F.map m₀ ≫ s.hom).hom.app U ξ = m := by
    dsimp only [m₀]
    rw [F.map_comp]
    change s.hom.hom.app U ((F.map (CartesianMonoidalCategory.fst M B)).hom.app U
      ((F.map (CartesianMonoidalCategory.snd (A ⊗ B) (M ⊗ B))).hom.app U ξ)) = m
    rw [hmw, hm]
    exact congrArg (fun k ↦ k.hom.app U
      (show (abSets (moduleAb MX)).obj.obj U from m)) s.inv_hom_id
  have ew : (F.map w₀ ≫ t.b.hom).hom.app U ξ = w := by
    dsimp only [w₀]
    rw [F.map_comp]
    change t.b.hom.hom.app U ((F.map (CartesianMonoidalCategory.snd M B)).hom.app U
      ((F.map (CartesianMonoidalCategory.snd (A ⊗ B) (M ⊗ B))).hom.app U ξ)) = w
    rw [hmw, hw]
    exact congrArg (fun k ↦ k.hom.app U
      (show (ringSets X.B).obj.obj U from w)) t.b.inv_hom_id
  have hn := pairing_graph F V adj Y X MY MX s t.b r hp T m₀ w₀ n
    (fun _ _ ↦ rfl) U ξ
  have hn' := pairing_graph F V adj Y X MY MX s t.b r hp T am vw n'
    (fun _ _ ↦ rfl) U ξ
  have ham := hsa T a m₀ am (fun _ _ ↦ rfl) U ξ
  have hvw := t.hb.2.1 T v₀ w₀ vw (fun _ _ ↦ rfl) U ξ
  have hav' := t.hc.2.1 T
    (a ≫ (sheafCompose J (CategoryTheory.forget CommRingCat)).map Y.iA)
    (v₀ ≫ (sheafCompose J (CategoryTheory.forget CommRingCat)).map Y.iB)
    av (fun _ _ ↦ rfl) U ξ
  have hai := congrArg (fun k ↦ k.hom.app U ξ)
    (congrArg (fun k ↦ F.map a ≫ k) t.iA_comm)
  have hbi := congrArg (fun k ↦ k.hom.app U ξ)
    (congrArg (fun k ↦ F.map v₀ ≫ k) t.iB_comm)
  simp only [← F.map_comp_assoc] at hai hbi
  have hai' : (F.map (a ≫
      (sheafCompose J (CategoryTheory.forget CommRingCat)).map Y.iA) ≫ t.c.hom).hom.app U ξ =
      X.iA.hom.app U x := hai.trans (congrArg (X.iA.hom.app U) ea)
  have hbi' : (F.map (v₀ ≫
      (sheafCompose J (CategoryTheory.forget CommRingCat)).map Y.iB) ≫ t.c.hom).hom.app U ξ =
      X.iB.hom.app U v := hbi.trans (congrArg (X.iB.hom.app U) ev)
  have ht := hsm T av n n' (fun W z ↦ (hYp.2 W
    (a.hom.app W z) (v₀.hom.app W z) (w₀.hom.app W z) (m₀.hom.app W z)).symm) U ξ
  rw [hn', hn, ham, hvw, hav', hai', hbi', ea, ev, em, ew] at ht
  exact ht.symm

private theorem transport_unique
    (F : Sheaf J (Type u) ⥤ Sheaf K (Type u))
    (V : Sheaf K (Type u) ⥤ Sheaf J (Type u)) (adj : F ⊣ V)
    [PreservesFiniteLimits F]
    {DY AY : Sheaf J CommRingCat.{u}} {DX AX : Sheaf K CommRingCat.{u}}
    {daY : DY ⟶ AY} {daX : DX ⟶ AX}
    (Y : Presentation daY) (X : Presentation daX) (t : Transport F Y X)
    (MY : SheafOfModules.{u} (RingedTensor.ringSheaf AY))
    (MX : SheafOfModules.{u} (RingedTensor.ringSheaf AX))
    (s : F.obj (abSets (moduleAb MY)) ≅ abSets (moduleAb MX))
    (r r' : F.obj (abSets (moduleAb (tensorModule Y MY))) ≅
      abSets (moduleAb (tensorModule X MX)))
    (hr : IsAdditiveTransport F (moduleAb (tensorModule Y MY))
      (moduleAb (tensorModule X MX)) r)
    (hr' : IsAdditiveTransport F (moduleAb (tensorModule Y MY))
      (moduleAb (tensorModule X MX)) r')
    (hp : HasAdjunctFormula F V adj Y X MY MX s t.b r)
    (hp' : HasAdjunctFormula F V adj Y X MY MX s t.b r') : r = r' := by
  obtain ⟨I, hi⟩ := algebraicLift F V adj DY DX t.d t.hd
  apply Iso.ext
  apply image_tensor_hom_ext F V adj I (restrictModule daY MY) (coefficientModule Y.db)
    (moduleAb (tensorModule X MX)) r.hom r'.hom hr hr'
  exact ((adjunct_formula_iff F V adj Y X MY MX s t.b r).mp hp).trans
    ((adjunct_formula_iff F V adj Y X MY MX s t.b r').mp hp').symm

private theorem tensor_map_pairing
    {D A : Sheaf J CommRingCat.{u}} {da : D ⟶ A}
    {Y Y' : Presentation da} (q : CoefficientChange Y Y')
    (M : SheafOfModules.{u} (RingedTensor.ringSheaf A))
    (j : moduleAb (tensorModule Y M) ⟶ moduleAb (tensorModule Y' M))
    (hj : IsTensorMap q M j) :
    pairing Y M ≫ (sheafCompose J (CategoryTheory.forget AddCommGrpCat)).map j =
      (𝟙 (abSets (moduleAb M)) ⊗ₘ
        (sheafCompose J (CategoryTheory.forget CommRingCat)).map q.q) ≫ pairing Y' M := by
  ext U x
  exact hj U x.1 x.2

private theorem transport_natural
    (F : Sheaf J (Type u) ⥤ Sheaf K (Type u))
    (V : Sheaf K (Type u) ⥤ Sheaf J (Type u)) (adj : F ⊣ V)
    [PreservesFiniteLimits F]
    {DY AY : Sheaf J CommRingCat.{u}} {DX AX : Sheaf K CommRingCat.{u}}
    {daY : DY ⟶ AY} {daX : DX ⟶ AX}
    (Y : Presentation daY) (X : Presentation daX) (t : Transport F Y X)
    (MY : SheafOfModules.{u} (RingedTensor.ringSheaf AY))
    (MX : SheafOfModules.{u} (RingedTensor.ringSheaf AX))
    (s : F.obj (abSets (moduleAb MY)) ≅ abSets (moduleAb MX))
    (r : F.obj (abSets (moduleAb (tensorModule Y MY))) ≅
      abSets (moduleAb (tensorModule X MX)))
    (hr : IsAdditiveTransport F (moduleAb (tensorModule Y MY))
      (moduleAb (tensorModule X MX)) r)
    (hp : HasAdjunctFormula F V adj Y X MY MX s t.b r)
    (Y' : Presentation daY) (X' : Presentation daX) (t' : Transport F Y' X')
    (qY : CoefficientChange Y Y') (qX : CoefficientChange X X')
    (hq : F.map ((sheafCompose J (CategoryTheory.forget CommRingCat)).map qY.q) ≫
      t'.b.hom = t.b.hom ≫ (sheafCompose K (CategoryTheory.forget CommRingCat)).map qX.q)
    (jY : moduleAb (tensorModule Y MY) ⟶ moduleAb (tensorModule Y' MY))
    (jX : moduleAb (tensorModule X MX) ⟶ moduleAb (tensorModule X' MX))
    (hjY : IsTensorMap qY MY jY) (hjX : IsTensorMap qX MX jX)
    (r' : F.obj (abSets (moduleAb (tensorModule Y' MY))) ≅
      abSets (moduleAb (tensorModule X' MX)))
    (hr' : IsAdditiveTransport F (moduleAb (tensorModule Y' MY))
      (moduleAb (tensorModule X' MX)) r')
    (hp' : HasAdjunctFormula F V adj Y' X' MY MX s t'.b r') :
    F.map ((sheafCompose J (CategoryTheory.forget AddCommGrpCat)).map jY) ≫ r'.hom =
      r.hom ≫ (sheafCompose K (CategoryTheory.forget AddCommGrpCat)).map jX := by
  obtain ⟨I, hi⟩ := algebraicLift F V adj DY DX t.d t.hd
  apply image_tensor_hom_ext F V adj I (restrictModule daY MY) (coefficientModule Y.db)
    (moduleAb (tensorModule X' MX))
  · intro T x y z hz U w
    change T ⟶ abSets (moduleAb (tensorModule Y MY)) at x y z
    change ∀ U w, @id ((tensorModule Y MY).val.obj U) (z.hom.app U w) =
      @Add.add ((tensorModule Y MY).val.obj U) inferInstance
        (x.hom.app U w) (y.hom.app U w) at hz
    have he : ∀ U w,
        @id ((tensorModule Y' MY).val.obj U)
          (((z ≫ (sheafCompose J (CategoryTheory.forget AddCommGrpCat)).map jY)).hom.app U w) =
        @Add.add ((tensorModule Y' MY).val.obj U) inferInstance
          (((x ≫ (sheafCompose J (CategoryTheory.forget AddCommGrpCat)).map jY)).hom.app U w)
          (((y ≫ (sheafCompose J (CategoryTheory.forget AddCommGrpCat)).map jY)).hom.app U w) := by
      intro U w
      change jY.hom.app U (z.hom.app U w) =
        jY.hom.app U (x.hom.app U w) + jY.hom.app U (y.hom.app U w)
      exact (congrArg (jY.hom.app U) (hz U w)).trans
        ((jY.hom.app U).hom.map_add _ _)
    have h := hr' T (x ≫ (sheafCompose J (CategoryTheory.forget AddCommGrpCat)).map jY)
      (y ≫ (sheafCompose J (CategoryTheory.forget AddCommGrpCat)).map jY)
      (z ≫ (sheafCompose J (CategoryTheory.forget AddCommGrpCat)).map jY)
      he U w
    simp only [Functor.map_comp, Category.assoc, id_eq] at h
    change (F.map z ≫ F.map
      ((sheafCompose J (CategoryTheory.forget AddCommGrpCat)).map jY) ≫ r'.hom).hom.app U w =
      @Add.add ((tensorModule X' MX).val.obj U) inferInstance
        ((F.map x ≫ F.map
          ((sheafCompose J (CategoryTheory.forget AddCommGrpCat)).map jY) ≫ r'.hom).hom.app U w)
        ((F.map y ≫ F.map
          ((sheafCompose J (CategoryTheory.forget AddCommGrpCat)).map jY) ≫ r'.hom).hom.app U w)
    exact h
  · intro T x y z hz U w
    have h := hr T x y z hz U w
    exact (congrArg (jX.hom.app U) h).trans ((jX.hom.app U).hom.map_add _ _)
  · change F.map (pairing Y MY) ≫ _ = F.map (pairing Y MY) ≫ _
    have hp0 := (adjunct_formula_iff F V adj Y X MY MX s t.b r).mp hp
    have hp1 := (adjunct_formula_iff F V adj Y' X' MY MX s t'.b r').mp hp'
    rw [← Category.assoc, fromProd_lift] at hp0 hp1
    have hl : F.map (𝟙 (abSets (moduleAb MY)) ⊗ₘ
          (sheafCompose J (CategoryTheory.forget CommRingCat)).map qY.q) ≫
        CartesianMonoidalCategory.lift
          (F.map (CartesianMonoidalCategory.fst _ _) ≫ s.hom)
          (F.map (CartesianMonoidalCategory.snd _ _) ≫ t'.b.hom) =
        CartesianMonoidalCategory.lift
          (F.map (CartesianMonoidalCategory.fst _ _) ≫ s.hom)
          (F.map (CartesianMonoidalCategory.snd _ _) ≫ t.b.hom) ≫
        (𝟙 (abSets (moduleAb MX)) ⊗ₘ
          (sheafCompose K (CategoryTheory.forget CommRingCat)).map qX.q) := by
      apply CartesianMonoidalCategory.hom_ext <;>
        simp only [Category.assoc, CartesianMonoidalCategory.lift_fst,
          CartesianMonoidalCategory.lift_snd,
          CartesianMonoidalCategory.lift_snd_assoc,
          CartesianMonoidalCategory.tensorHom_fst,
          CartesianMonoidalCategory.tensorHom_snd, Category.comp_id,
          ← F.map_comp_assoc]
      rw [F.map_comp, Category.assoc, hq]
    calc
      _ = F.map (𝟙 _ ⊗ₘ
          (sheafCompose J (CategoryTheory.forget CommRingCat)).map qY.q) ≫
          F.map (pairing Y' MY) ≫ r'.hom := by
        rw [← F.map_comp_assoc, ← F.map_comp_assoc, tensor_map_pairing qY MY jY hjY]
      _ = _ := by
        rw [hp1, ← Category.assoc, hl]
        rw [Category.assoc, ← tensor_map_pairing qX MX jX hjX,
          ← Category.assoc, ← hp0]
        simp only [Category.assoc]

/-- Semilinear transport of the sheafified tensor, with its actual adjunct and scalars.

Source: integral-twist paragraph of sk-prop-sfb-cartesian-coefficients-twists.proof.md;
Stacks, Modules on Sites, Tags 03CY, 03D1--03D3, 03EK and 03EL.
(blueprint: lem-pur-semilinear-tensor-presentation-transport)

Proof:
1. Use lem-weil-pbc-geometric-module-transport with identity structural map to construct
   the algebraic inverse image over F(DY), with its transported operations and actual
   underlying adjunction. The normalized tensor comparison of
   lem-weil-pbc-algebraic-inverse-image-tensor-comparison identifies the pure pairing
   as a morphism on the full product sheaf, using that product as the test sheaf.
2. Sectionwise, A tensor_D B acts on M tensor_D B by
   (x tensor v)(m tensor w) = xm tensor vw. Additivity and balancing follow from the
   tensor relations; associativity and the unit follow on pure tensors. Restrictions
   preserve the action. The module sheafification interface
   lem-pc-sites-module-sheafification-interface extends it uniquely to the sheafified
   tensor ring and module. The pushout presentation identifies that ring with R,
   producing hY and hX. It does not assert a sectionwise pushout.
3. Semilinearity of s over a restricts to d-semilinearity by da_comm, and b is
   d-semilinear by db_comm. The pairing s(u) tensor b(v) is balanced over F(DY).
   lem-pc-sites-sheaf-tensor-bilinear-universal gives its map U. The pairing using
   s inverse and b inverse is its inverse, by the same universal property.
   Compose U with the normalized inverse-image tensor comparison to obtain r.
4. Unit naturality of the actual adjunction identifies the adjunct of r on the pure
   pairing with V of the target pairing applied to the actual adjuncts of s and b.
   The inverse product comparison for V is exactly the one in HasAdjunctFormula.
5. Two additive maps with that adjunct formula agree on every presheaf pure tensor,
   then on finite sums, and hence on the abelian sheafification. Injectivity of the
   adjunction hom equivalence proves uniqueness among all additive isomorphisms.
6. Applying F to the four-variable action formula and using the normalized pairing
   comparison shows that its inverse intertwines the tensor-ring actions. Identify
   maps after sheafification by the factorization clause of
   lem-pc-sites-module-sheafification-interface, not by assuming global pure generation.
7. The map U is semilinear for a tensor b by its pure-input formula; extend that
   equality through module sheafification by the same factorization clause. The
   compatibility with both presentation inclusions, iA_comm and iB_comm, is the
   stated c F(beta) equation and gives c-semilinearity of r on all local sections.
8. Sheafify 1 tensor q to obtain the additive coefficient maps jY and jX, with the
   displayed pure formulas. Naturality of the inverse-image tensor comparison and
   b' F(qY) = qX b identify the two composites on pure pairs. Their tensor universal
   property and sheafification give the naturality equation. The i-compatibility
   equations identify their scalar structures. No points or freeness are used.
-/
theorem exists_unique_semilinear_tensor_transport
    {C E : Type u} [Category.{u} C] [Category.{u} E]
    {J : GrothendieckTopology C} {K : GrothendieckTopology E}
    (F : Sheaf J (Type u) ⥤ Sheaf K (Type u))
    (V : Sheaf K (Type u) ⥤ Sheaf J (Type u)) (adj : F ⊣ V)
    [PreservesFiniteLimits F]
    {DY AY : Sheaf J CommRingCat.{u}} {DX AX : Sheaf K CommRingCat.{u}}
    {daY : DY ⟶ AY} {daX : DX ⟶ AX}
    (Y : Presentation daY) (X : Presentation daX) (t : Transport F Y X)
    (MY : SheafOfModules.{u} (RingedTensor.ringSheaf AY))
    (MX : SheafOfModules.{u} (RingedTensor.ringSheaf AX))
    (s : F.obj (abSets (moduleAb MY)) ≅ abSets (moduleAb MX))
    (hs : IsAdditiveTransport F (moduleAb MY) (moduleAb MX) s)
    (hsa : IsSemilinearTransport F AY AX (moduleAb MY) (moduleAb MX)
      (fun U ↦ inferInstanceAs (SMul (AY.obj.obj U) (MY.val.obj U)))
      (fun U ↦ inferInstanceAs (SMul (AX.obj.obj U) (MX.val.obj U))) t.a s) :
    ∃ (hY : ∀ U : Cᵒᵖ, Module (Y.R.obj.obj U) ((tensorModule Y MY).val.obj U))
      (hX : ∀ U : Eᵒᵖ, Module (X.R.obj.obj U) ((tensorModule X MX).val.obj U)),
      IsTensorAction Y MY hY ∧ IsTensorAction X MX hX ∧
      ∃ r : F.obj (abSets (moduleAb (tensorModule Y MY))) ≅
          abSets (moduleAb (tensorModule X MX)),
        IsAdditiveTransport F (moduleAb (tensorModule Y MY))
          (moduleAb (tensorModule X MX)) r ∧
        HasAdjunctFormula F V adj Y X MY MX s t.b r ∧
        (∀ r₀ : F.obj (abSets (moduleAb (tensorModule Y MY))) ≅
            abSets (moduleAb (tensorModule X MX)),
          IsAdditiveTransport F (moduleAb (tensorModule Y MY))
            (moduleAb (tensorModule X MX)) r₀ →
          HasAdjunctFormula F V adj Y X MY MX s t.b r₀ → r₀ = r) ∧
        IsSemilinearTransport F Y.R X.R (moduleAb (tensorModule Y MY))
          (moduleAb (tensorModule X MX)) (fun U ↦ (hY U).toSMul)
          (fun U ↦ (hX U).toSMul) t.c r ∧
        ∀ (Y' : Presentation daY) (X' : Presentation daX) (t' : Transport F Y' X')
          (qY : CoefficientChange Y Y') (qX : CoefficientChange X X'),
          t'.d = t.d → t'.a = t.a →
          F.map ((sheafCompose J (CategoryTheory.forget CommRingCat)).map qY.q) ≫
            t'.b.hom = t.b.hom ≫
              (sheafCompose K (CategoryTheory.forget CommRingCat)).map qX.q →
          F.map ((sheafCompose J (CategoryTheory.forget CommRingCat)).map qY.i) ≫
            t'.c.hom = t.c.hom ≫
              (sheafCompose K (CategoryTheory.forget CommRingCat)).map qX.i →
          ∃ (jY : moduleAb (tensorModule Y MY) ⟶ moduleAb (tensorModule Y' MY))
            (jX : moduleAb (tensorModule X MX) ⟶ moduleAb (tensorModule X' MX)),
            IsTensorMap qY MY jY ∧ IsTensorMap qX MX jX ∧
            ∀ r' : F.obj (abSets (moduleAb (tensorModule Y' MY))) ≅
                abSets (moduleAb (tensorModule X' MX)),
              IsAdditiveTransport F (moduleAb (tensorModule Y' MY))
                (moduleAb (tensorModule X' MX)) r' →
              HasAdjunctFormula F V adj Y' X' MY MX s t'.b r' →
              F.map ((sheafCompose J (CategoryTheory.forget AddCommGrpCat)).map jY) ≫
                r'.hom = r.hom ≫
                  (sheafCompose K (CategoryTheory.forget AddCommGrpCat)).map jX := by
  -- The normalized additive comparison transports the source scalar action to the target.
  obtain ⟨hY, hYp⟩ := tensor_action Y MY
  obtain ⟨r, hr, hp⟩ := normalized_additive_comparison F V adj Y X t MY MX s hs hsa
  obtain ⟨hX, hres, hsm⟩ := transport_action F V adj Y X t MY MX r hr hY hYp.1
  refine ⟨hY, hX, hYp, ⟨hres, ?_⟩, r, hr, hp, ?_, hsm, ?_⟩
  · exact transported_action_pure F V adj Y X t MY MX s hsa r hp hY hX hYp hsm
  · intro r₀ hr₀ hp₀
    exact transport_unique F V adj Y X t MY MX s r₀ r hr₀ hr hp₀ hp
  · intro Y' X' t' qY qX _ _ hq _
    obtain ⟨jY, hjY⟩ := coefficient_maps qY MY
    obtain ⟨jX, hjX⟩ := coefficient_maps qX MX
    refine ⟨jY, jX, hjY, hjX, ?_⟩
    intro r' hr' hp'
    exact transport_natural F V adj Y X t MY MX s r hr hp
      Y' X' t' qY qX hq jY jX hjY hjX r' hr' hp'

end SheafOfModules.TensorPresentationTransport
