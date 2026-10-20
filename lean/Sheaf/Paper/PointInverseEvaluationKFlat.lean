/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P2, SHEAF group M4
-/
module

public import WeilConjectures.Topology.RingedSpaceModuleCohomology
public import Sheaf.Algebra.Homology.KFlat
public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategory
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric
public import Mathlib.Algebra.Category.ModuleCat.Colimits
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
import WeilConjectures.Mathlib.Algebra.Homology.Bifunctor
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
import Mathlib.Algebra.Category.Grp.Zero

/-! # K-flat complexes under inverse evaluation on a point

Source: Stacks Project, Tags 0B6A, 06YN and 06YC.
-/

@[expose] public section

universe u
set_option autoImplicit false
set_option synthInstance.maxSize 2048
open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.RingedSpace

local instance pointKFlatCommRing (Y : RingedSpace.{u}) :
    CommRing ((moduleRings Y).obj.obj (op ⊤)) :=
  inferInstanceAs (CommRing (Y.presheaf.obj (op ⊤)))

noncomputable local instance pointKFlatColimits
    (Y : RingedSpace.{u}) :
    HasColimitsOfSize.{0, 0} (ModuleCat.{u} ((moduleRings Y).obj.obj (op ⊤))) :=
  hasColimitsOfSizeShrink.{0, 0, u} _

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
open TopologicalSpace MonoidalCategory in
private theorem top_le_of_mem (Y : RingedSpace.{u}) [Unique Y]
    (U : Opens Y) (h : (default : Y) ∈ U) : ⊤ ≤ U := by
  intro x _
  simpa only [Subsingleton.elim x default] using h

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
open TopologicalSpace MonoidalCategory in
private theorem point_presheaf_isSheaf (Y : RingedSpace.{u}) [Unique Y]
    (P : PresheafOfModules.{u} (moduleRings Y).obj)
    [Subsingleton (P.obj (op ⊥))] :
    Presheaf.IsSheaf (Opens.grothendieckTopology Y) P.presheaf := by
  classical
  apply (TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing _).mpr
  intro ι U sf hsf
  let T := P.presheaf ⋙ forget AddCommGrpCat
  by_cases h : ∃ i, (default : Y) ∈ U i
  · obtain ⟨i, hi⟩ := h
    have htop := top_le_of_mem Y (U i) hi
    let inc : iSup U ⟶ U i := homOfLE (le_top.trans htop)
    let s := T.map inc.op (sf i)
    have hs : ∀ j, T.map (Opens.leSupr U j).op s = sf j := by
      intro j
      let lift : U j ⟶ U i ⊓ U j := homOfLE (le_inf (le_top.trans htop) le_rfl)
      have hcompat := congrArg (fun z ↦ T.map lift.op z) (hsf i j)
      change T.map lift.op (T.map (Opens.infLELeft _ _).op (sf i)) =
        T.map lift.op (T.map (Opens.infLERight _ _).op (sf j)) at hcompat
      simp only [← Functor.map_comp_apply, ← op_comp] at hcompat
      have hid : lift ≫ Opens.infLERight _ _ = 𝟙 (U j) := Subsingleton.elim _ _
      rw [hid, op_id, T.map_id] at hcompat
      change T.map (Opens.leSupr U j).op (T.map inc.op (sf i)) = sf j
      rw [← Functor.map_comp_apply, ← op_comp]
      have hm : Opens.leSupr U j ≫ inc = lift ≫ Opens.infLELeft _ _ :=
        Subsingleton.elim _ _
      rw [hm]
      exact hcompat
    refine ⟨s, hs, ?_⟩
    intro t ht
    have hid : inc ≫ Opens.leSupr U i = 𝟙 (iSup U) := Subsingleton.elim _ _
    have hti := congrArg (fun z ↦ T.map inc.op z) (ht i)
    change T.map inc.op (T.map (Opens.leSupr U i).op t) = s at hti
    rw [← Functor.map_comp_apply, ← op_comp, hid, op_id, T.map_id] at hti
    exact hti
  · have hbot : ∀ i, U i = ⊥ := by
      intro i
      apply le_antisymm _ bot_le
      intro x hx
      exact (h ⟨i, by simpa only [Subsingleton.elim x default] using hx⟩).elim
    have hunion : iSup U = ⊥ := by simp [hbot]
    have : Subsingleton (ToType (P.presheaf.obj (op (iSup U)))) := by
      change Subsingleton (P.obj (op (iSup U)))
      rw [hunion]
      infer_instance
    refine ⟨0, ?_, fun t _ ↦ Subsingleton.elim _ _⟩
    intro i
    have : Subsingleton (ToType (P.presheaf.obj (op (U i)))) := by
      change Subsingleton (P.obj (op (U i)))
      rw [hbot i]
      infer_instance
    exact Subsingleton.elim _ _

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
open TopologicalSpace MonoidalCategory in
private theorem point_tensor_isSheaf (Y : RingedSpace.{u}) [Unique Y]
    (M N : SheafOfModules.{u} (moduleRings Y)) :
    Presheaf.IsSheaf (Opens.grothendieckTopology Y) (M.val ⊗ N.val).presheaf := by
  have : Subsingleton (M.val.obj (op ⊥)) := by
    let F : Y.carrier.Sheaf AddCommGrpCat := ⟨M.val.presheaf, M.isSheaf⟩
    exact AddCommGrpCat.subsingleton_of_isZero F.isTerminalOfEmpty.isZero
  have : Subsingleton ((M.val ⊗ N.val).obj (op ⊥)) := by
    change Subsingleton (TensorProduct _ (M.val.obj (op ⊥)) (N.val.obj (op ⊥)))
    infer_instance
  exact point_presheaf_isSheaf Y (M.val ⊗ N.val)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
open TopologicalSpace MonoidalCategory in
private noncomputable def point_sectionTensor (Y : RingedSpace.{u})
    (M N : SheafOfModules.{u} (moduleRings Y)) :
    M.val ⊗ N.val ⟶
      (letI := SheafOfModules.monoidalCategory Y.sheaf; M ⊗ N).val := by
  let := SheafOfModules.monoidalCategory Y.sheaf
  exact (PresheafOfModules.sheafificationAdjunction (𝟙 (moduleRings Y).obj)).unit.app
    (M.val ⊗ N.val) ≫ (SheafOfModules.tensorObjIsoSheafification (R := Y.sheaf) M N).inv.val

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
open TopologicalSpace MonoidalCategory in
private theorem point_sectionTensor_isIso (Y : RingedSpace.{u}) [Unique Y]
    (M N : SheafOfModules.{u} (moduleRings Y)) :
    IsIso (point_sectionTensor Y M N) := by
  let := SheafOfModules.monoidalCategory Y.sheaf
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 (moduleRings Y).obj)
  have : IsIso (adj.unit.app (M.val ⊗ N.val)) :=
    adj.isIso_unit_app_of_iso
      (X := ⟨M.val ⊗ N.val, point_tensor_isSheaf Y M N⟩) (Iso.refl _)
  have : IsIso (SheafOfModules.tensorObjIsoSheafification (R := Y.sheaf) M N).inv.val :=
    inferInstanceAs (IsIso ((SheafOfModules.forget (moduleRings Y)).map
      (SheafOfModules.tensorObjIsoSheafification (R := Y.sheaf) M N).inv))
  change IsIso (adj.unit.app (M.val ⊗ N.val) ≫
    (SheafOfModules.tensorObjIsoSheafification (R := Y.sheaf) M N).inv.val)
  infer_instance

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
open TopologicalSpace MonoidalCategory in
private theorem point_sectionTensor_natural (Y : RingedSpace.{u})
    {M M' N N' : SheafOfModules.{u} (moduleRings Y)} (f : M ⟶ M') (g : N ⟶ N') :
    letI := SheafOfModules.monoidalCategory Y.sheaf
    (f.val ⊗ₘ g.val) ≫ point_sectionTensor Y M' N' =
      point_sectionTensor Y M N ≫ (f ⊗ₘ g).val := by
  let := SheafOfModules.monoidalCategory Y.sheaf
  let S := PresheafOfModules.sheafification (𝟙 (moduleRings Y).obj)
  have h : (f ⊗ₘ g) ≫
      (SheafOfModules.tensorObjIsoSheafification (R := Y.sheaf) M' N').hom =
      (SheafOfModules.tensorObjIsoSheafification (R := Y.sheaf) M N).hom ≫
        S.map (f.val ⊗ₘ g.val) := by
    rw [tensorHom_def, Category.assoc,
      SheafOfModules.whiskerLeft_tensorObjIsoSheafification_hom
        (R := Y.sheaf) M' g,
      ← Category.assoc, SheafOfModules.whiskerRight_tensorObjIsoSheafification_hom
        (R := Y.sheaf) f N,
      Category.assoc, ← Functor.map_comp, ← tensorHom_def]
  have hi : (SheafOfModules.tensorObjIsoSheafification (R := Y.sheaf) M N).inv ≫
      (f ⊗ₘ g) = S.map (f.val ⊗ₘ g.val) ≫
        (SheafOfModules.tensorObjIsoSheafification (R := Y.sheaf) M' N').inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, ← h]
    simp
  unfold point_sectionTensor
  have hu := (PresheafOfModules.sheafificationAdjunction
    (𝟙 (moduleRings Y).obj)).unit.naturality (f.val ⊗ₘ g.val)
  dsimp at hu
  rw [← Category.assoc, hu, Category.assoc]
  have hiv := congrArg SheafOfModules.Hom.val hi.symm
  exact congrArg (fun z ↦ (PresheafOfModules.sheafificationAdjunction
    (𝟙 (moduleRings Y).obj)).unit.app (M.val ⊗ N.val) ≫ z) hiv

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
open TopologicalSpace MonoidalCategory in
private noncomputable def point_tensorIso (Y : RingedSpace.{u}) [Unique Y]
    (M N : SheafOfModules.{u} (moduleRings Y)) :
    letI := SheafOfModules.monoidalCategory Y.sheaf
    (globalSectionsFunctor Y).obj M ⊗ (globalSectionsFunctor Y).obj N ≅
      (globalSectionsFunctor Y).obj (M ⊗ N) := by
  let := SheafOfModules.monoidalCategory Y.sheaf
  have := point_sectionTensor_isIso Y M N
  exact (PresheafOfModules.evaluation (moduleRings Y).obj (op ⊤)).mapIso
    (asIso (point_sectionTensor Y M N))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
open TopologicalSpace MonoidalCategory in
private theorem point_tensorIso_natural (Y : RingedSpace.{u}) [Unique Y]
    {M M' N N' : SheafOfModules.{u} (moduleRings Y)} (f : M ⟶ M') (g : N ⟶ N') :
    letI := SheafOfModules.monoidalCategory Y.sheaf
    ((globalSectionsFunctor Y).map f ⊗ₘ (globalSectionsFunctor Y).map g) ≫
      (point_tensorIso Y M' N').hom =
      (point_tensorIso Y M N).hom ≫ (globalSectionsFunctor Y).map (f ⊗ₘ g) := by
  let := SheafOfModules.monoidalCategory Y.sheaf
  exact congrArg (fun z ↦ z.app (op ⊤)) (point_sectionTensor_natural Y f g)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
open TopologicalSpace MonoidalCategory in
private noncomputable def point_tensorNatIso (Y : RingedSpace.{u}) [Unique Y] :
    letI := SheafOfModules.monoidalCategory Y.sheaf
    (((Functor.whiskeringLeft₂ _).obj (globalSectionsFunctor Y)).obj
      (globalSectionsFunctor Y)).obj (curriedTensor _) ≅
      (Functor.postcompose₂.obj (globalSectionsFunctor Y)).obj (curriedTensor _) := by
  let := SheafOfModules.monoidalCategory Y.sheaf
  refine NatIso.ofComponents (fun M ↦ NatIso.ofComponents (fun N ↦ point_tensorIso Y M N)
    (fun {N N'} g ↦ ?_)) (fun {M M'} f ↦ ?_)
  · change ((globalSectionsFunctor Y).obj M ◁ (globalSectionsFunctor Y).map g) ≫ _ =
      _ ≫ (globalSectionsFunctor Y).map (M ◁ g)
    have h := point_tensorIso_natural Y (𝟙 M) g
    rw [(globalSectionsFunctor Y).map_id M, id_tensorHom, id_tensorHom] at h
    exact h
  · apply NatTrans.ext
    funext N
    change ((globalSectionsFunctor Y).map f ▷ (globalSectionsFunctor Y).obj N) ≫ _ =
      _ ≫ (globalSectionsFunctor Y).map (f ▷ N)
    have h := point_tensorIso_natural Y f (𝟙 N)
    rw [(globalSectionsFunctor Y).map_id N, tensorHom_id, tensorHom_id] at h
    exact h

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
open TopologicalSpace MonoidalCategory in
/-- Evaluation on a point commutes with unbounded total tensor products.
Source: Stacks Project, Tags 009A, 006U and 06YC.

Proof: on a singleton every open is empty or the whole space. The empty-cover
sheaf condition forces empty sections to vanish. The sectionwise tensor of two
module sheaves therefore satisfies the sheaf condition: a cover of the whole
space contains the whole space, and its matching families are determined by that
component; the empty-open value remains zero. The sheafification counit thus
identifies evaluation of the sheaf tensor with the tensor of evaluations,
naturally in both modules. Transport along he gives the same comparison for
e.functor. As an equivalence e.functor preserves coproducts. Apply its tensor
comparison on each summand F.X p tensor G.X q in degree n=p+q of the total complex.
Naturality intertwines both differentials, and additivity preserves the sign
(-1)^p in the second differential. The resulting degreewise isomorphisms and
their inverses are cochain maps, giving the claimed isomorphism. This includes
zero rings, zero complexes and arbitrary unbounded complexes. -/
private theorem pointEvaluation_totalTensorIso
    (Y : RingedSpace.{u}) [Unique Y]
    (e : SheafOfModules.{u} (moduleRings Y) ≌
      ModuleCat.{u} ((moduleRings Y).obj.obj (op ⊤)))
    (he : Nonempty (e.functor ≅ globalSectionsFunctor Y))
    [e.functor.Additive]
    (F G : CochainComplex (SheafOfModules.{u} (moduleRings Y)) ℤ) :
    letI := SheafOfModules.monoidalCategory Y.sheaf
    Nonempty (((e.functor.mapHomologicalComplex (.up ℤ)).obj
      (CochainComplex.mapBifunctor F G (MonoidalCategory.curriedTensor _))) ≅
      CochainComplex.mapBifunctor
        ((e.functor.mapHomologicalComplex (.up ℤ)).obj F)
        ((e.functor.mapHomologicalComplex (.up ℤ)).obj G)
        (MonoidalCategory.curriedTensor _)) := by
  obtain ⟨he⟩ := he
  have : (globalSectionsFunctor Y).IsEquivalence := Functor.isEquivalence_of_iso he
  let := SheafOfModules.monoidalCategory Y.sheaf
  let H := NatIso.mapHomologicalComplex he (.up ℤ)
  let comparison := asIso (HomologicalComplex.mapBifunctorComparison
    (point_tensorNatIso Y).inv (.up ℤ) F G)
  exact ⟨H.app (CochainComplex.mapBifunctor F G (curriedTensor _)) ≪≫
    comparison ≪≫ ((H.app F).symm ⊗ᵢ (H.app G).symm)⟩

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
open TopologicalSpace MonoidalCategory in
private theorem acyclic_map_iff
    {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
    (e : C ≌ D) [e.functor.Additive] (F : CochainComplex C ℤ) :
    ((e.functor.mapHomologicalComplex (.up ℤ)).obj F).Acyclic ↔ F.Acyclic := by
  apply forall_congr'
  intro i
  exact (F.sc i).exact_map_iff_of_faithful e.functor

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Inverse evaluation on a one-point ringed space takes ordinary module K-flat
complexes to K-flat sheaf complexes.
Source: Stacks Project, Section 20.44, Tag 0B6A (the one-point identification),
Definition 06YN and Lemma 06YC.
(blueprint: lem-sc-point-inverse-evaluation-kflat)

Proof: every open of the point is either empty or the whole space. The empty-open
section module of a sheaf is zero. Consequently evaluation of the sheaf tensor at
the whole space is the ordinary tensor product of its section modules: sheafifying
the sectionwise tensor does not alter the whole-space sections, since every cover
of the whole point contains the whole point. This identification is natural in
both modules. Evaluation is an exact equivalence and preserves coproducts, so
termwise evaluation identifies the total sheaf tensor with the total module tensor
and preserves and reflects acyclicity. The given natural isomorphism identifies
e.functor with evaluation. For an acyclic sheaf complex F, its evaluated complex
is acyclic. The counit of e identifies evaluation of e.inverse(K) with K. Ordinary
K-flatness of K therefore makes the evaluated tensor F tensor e.inverse(K)
acyclic, and reflection of acyclicity proves the claim. The equivalence between
preservation of quasi-isomorphisms and acyclic tensors follows from mapping cones
(or HomotopyCategory.kFlat_iff_preserves_acyclic). This argument includes the zero
ring, the zero complex and all unbounded complexes. -/
theorem pointInverseEvaluation_isKFlat
    (Y : RingedSpace.{u}) [Unique Y]
    (e : SheafOfModules.{u} (moduleRings Y) ≌
      ModuleCat.{u} ((moduleRings Y).obj.obj (op ⊤)))
    (he : Nonempty (e.functor ≅ globalSectionsFunctor Y))
    [e.inverse.Additive]
    (K : CochainComplex (ModuleCat.{u} ((moduleRings Y).obj.obj (op ⊤))) ℤ)
    (hK : (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat K) :
    CochainComplex.IsAcyclicTensorKFlat (R := Y.sheaf)
      ((e.inverse.mapHomologicalComplex (.up ℤ)).obj K) := by
  obtain ⟨he⟩ := he
  have : e.functor.Additive := Functor.additive_of_iso he.symm
  let := SheafOfModules.monoidalCategory Y.sheaf
  intro F hF
  let E := e.functor.mapHomologicalComplex (.up ℤ)
  have hEF : (E.obj F).Acyclic := (acyclic_map_iff e F).2 hF
  have ht := (HomotopyCategory.kFlat_iff_preserves_acyclic _).1
    ((HomotopyCategory.kFlat_quotient_obj_iff K).2 hK)
    ((HomotopyCategory.quotient _ _).obj (E.obj F))
    ((HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic _).2 hEF)
  have hTensor : (CochainComplex.mapBifunctor (E.obj F) K
      (MonoidalCategory.curriedTensor _)).Acyclic :=
    (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic _).1 ht.2
  obtain ⟨comparison⟩ := pointEvaluation_totalTensorIso Y e ⟨he⟩ F
    ((e.inverse.mapHomologicalComplex (.up ℤ)).obj K)
  let counit := (e.mapHomologicalComplex (.up ℤ)).counitIso.app K
  let tensorCounit := ((MonoidalCategory.curriedTensor _).map₂CochainComplex.obj
    (E.obj F)).mapIso counit
  apply (acyclic_map_iff e _).1
  intro i
  exact (hTensor i).of_iso (comparison ≪≫ tensorCounit).symm

end AlgebraicGeometry.RingedSpace
