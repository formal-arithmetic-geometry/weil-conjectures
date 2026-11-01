/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.LocallyClosedCoefficientImmersion.LocallyClosedModuleExtensionModel
import Mathlib.CategoryTheory.EssentialImage
import all WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsSupplement
import all WeilConjectures.AlgebraicGeometry.ProEtale.Closed.ProEtaleClosedEssentialImage
import WeilConjectures.AlgebraicGeometry.ProEtaleModuleInverseImageComparison
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleIdentifiedOpenClosed
import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleAbelianClosedCounit
import WeilConjectures.Mathlib.AlgebraicGeometry.Cover.QuasiCompact
import WeilConjectures.Mathlib.CategoryTheory.Sites.Pullback
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.BaseChange
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.FullyFaithful
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.ClosedImmersion

/-!
# Objectwise normalized composition for the fixed locally closed model

Source: Stacks Project, Tags 09AH and 02V0.
(blueprint: lem-sfb-locally-closed-module-extension-binary).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry.Scheme

private theorem normalized_of_essImage
    {C D : Type*} [Category C] [Category D] (H : C ⥤ D) (L : D ⥤ C)
    (r : H ⋙ L ≅ 𝟭 C) {A : D} {M : C} (t : L.obj A ≅ M)
    (h : H.essImage A) :
    ∃ e : A ≅ H.obj M, LocallyClosedObjectNormalization H L r t.hom e := by
  obtain ⟨N, ⟨e⟩⟩ := h
  let g : N ≅ M := (r.app N).symm ≪≫ L.mapIso e ≪≫ t
  refine ⟨e.symm ≪≫ H.mapIso g, ?_⟩
  change L.map (e.inv ≫ H.map g.hom) ≫ r.hom.app M = t.hom
  rw [L.map_comp, Category.assoc]
  have hn : L.map (H.map g.hom) ≫ r.hom.app M = r.hom.app N ≫ g.hom :=
    r.hom.naturality g.hom
  rw [hn]
  simp [g]

private theorem zero_of_forget {C D : Type*} [Category C] [Category D]
    [HasZeroMorphisms C] [HasZeroMorphisms D] (F : C ⥤ D)
    [F.Faithful] [F.PreservesZeroMorphisms] (M : C) (h : IsZero (F.obj M)) :
    IsZero M := by
  apply (IsZero.iff_id_eq_zero _).2
  apply F.map_injective
  rw [F.map_id, F.map_zero]
  exact h.eq_of_src _ _

private theorem pull_zero_iff {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (S : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (c : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R ≅ S)
    (M : proEtaleRingModules Y R) :
    IsZero ((proEtaleRingModulePullback f R S c).obj M) ↔
      IsZero ((proEtaleSheafInverseImage f AddCommGrpCat.{u + 1}).obj
        ((SheafOfModules.toSheaf _).obj M)) := by
  rw [pullback_isZero_iff_inverseImage]
  obtain ⟨e⟩ := (proEtale_moduleInverseImage_comparison f R).1
  constructor
  · intro h
    exact ((SheafOfModules.toSheaf _).map_isZero h).of_iso (e.app M).symm
  · intro h
    apply zero_of_forget (SheafOfModules.toSheaf _) _
    exact h.of_iso (e.app M)

private theorem open_image_support {S X : LocallyClosedCoefficients.{u}}
    (v : LocallyClosedCoefficientImmersion S X) (hv : IsOpenImmersion v.hom)
    {Z : Scheme.{u}} (i : Z ⟶ X.scheme) [IsClosedImmersion i]
    (h : Set.range v.hom = (Set.range i)ᶜ)
    (Ri : Sheaf (ProEt.topology Z) CommRingCat.{u + 1})
    (ci : (proEtaleSheafInverseImage i CommRingCat.{u + 1}).obj X.ring ≅ Ri) :
    (∀ N, IsZero ((proEtaleRingModulePullback i X.ring Ri ci).obj
      ((LocallyClosedCoefficientImmersion.modelOpenExtension v hv).obj N))) ∧
    ∀ M, IsZero ((proEtaleRingModulePullback i X.ring Ri ci).obj M) →
      IsIso ((LocallyClosedCoefficientImmersion.modelOpenAdjunction v hv).counit.app M) := by
  let := hv
  let : IsNoetherian X.scheme := ⟨⟩
  let : NoetherianSpace S.scheme := v.hom.isOpenEmbedding.isInducing.noetherianSpace
  let U := ProEt.mk v.hom
  have : IsOpenImmersion U.hom := hv
  have : QuasiCompact U.hom := inferInstanceAs (QuasiCompact v.hom)
  obtain ⟨_, _, _, F, _, _, _, adj, _, hz, hc⟩ :=
    proEtaleIdentifiedOpenClosed i U h X.ring Ri S.ring ci v.coefficient
  let a := LocallyClosedCoefficientImmersion.modelOpenAdjunction v hv
  let e := a.leftAdjointUniq adj
  refine ⟨fun N ↦ (hz N).of_iso
    ((proEtaleRingModulePullback i X.ring Ri ci).mapIso (e.app N)), ?_⟩
  intro M hm
  have := hc M hm
  have he : e.hom.app (v.pull.obj M) ≫ adj.counit.app M = a.counit.app M :=
    a.leftAdjointUniq_hom_app_counit adj M
  rw [← he]
  infer_instance

private noncomputable def pull_carrier_iso {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (S : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (c : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R ≅ S)
    (M : proEtaleRingModules Y R) :
    (SheafOfModules.toSheaf _).obj ((proEtaleRingModulePullback f R S c).obj M) ≅
      (AlgebraicGeometry.ProEtale.upperStar AddCommGrpCat.{u + 1} f).obj
        ((SheafOfModules.toSheaf _).obj M) := by
  let e := proEtaleScalarEquivalence X ((sheafCompose (ProEt.topology X)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).mapIso c)
  let b : proEtaleModuleInverseImage f R ⋙ e.inverse ⊣
      proEtaleRingModuleDirectImage f R S c :=
    ((proEtaleModuleInverseImageAdjunction f R).comp e.symm.toAdjunction).ofNatIsoRight
      (coefficientDirectImageIso f R S c)
  let t := (proEtaleRingModuleAdjunction f R S c).leftAdjointUniq b
  let d : (SheafOfModules.toSheaf _).obj
      (e.inverse.obj ((proEtaleModuleInverseImage f R).obj M)) ≅
        (SheafOfModules.toSheaf _).obj ((proEtaleModuleInverseImage f R).obj M) :=
    Iso.refl _
  exact (SheafOfModules.toSheaf _).mapIso (t.app M) ≪≫ d ≪≫
    (Classical.choice (proEtale_moduleInverseImage_comparison f R).1).app M

private noncomputable def push_carrier_iso {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (S : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (c : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R ≅ S)
    (M : proEtaleRingModules X S) :
    (SheafOfModules.toSheaf _).obj ((proEtaleRingModuleDirectImage f R S c).obj M) ≅
      (AlgebraicGeometry.ProEtale.lowerStar AddCommGrpCat.{u + 1} f).obj
        ((SheafOfModules.toSheaf _).obj M) :=
  Iso.refl _

open AlgebraicGeometry.ProEtale

private theorem ab_open_disjoint {U X Y : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] (f : Y ⟶ X)
    (h : Disjoint (Set.range f) (Set.range j))
    (N : Sheaf (ProEt.topology U) AddCommGrpCat.{u + 1}) :
    IsZero ((upperStar AddCommGrpCat.{u + 1} f).obj
      ((openImmersionLowerShriek AddCommGrpCat.{u + 1} j).obj N)) := by
  apply IsInitial.isZero
  refine IsInitial.ofUnique (h := fun H ↦ ?_)
  have hz := isZero_upperStar_lowerStar_of_disjoint AddCommGrpCat.{u + 1} f j h H
  let : Unique (N ⟶ (upperStar AddCommGrpCat.{u + 1} j).obj
      ((lowerStar AddCommGrpCat.{u + 1} f).obj H)) :=
    ⟨⟨0⟩, fun g ↦ hz.eq_of_tgt g 0⟩
  exact Equiv.unique
    (((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).homEquiv _ H).trans
      ((openImmersionLowerShriekUpperStarAdjunction AddCommGrpCat.{u + 1} j).homEquiv N _))

private theorem ab_open_counit_iso {X Z U : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
    (h : Set.range j = (Set.range i)ᶜ)
    (F : Sheaf (ProEt.topology X) AddCommGrpCat.{u + 1})
    (hz : IsZero ((upperStar AddCommGrpCat.{u + 1} i).obj F)) :
    IsIso ((openImmersionLowerShriekUpperStarAdjunction AddCommGrpCat.{u + 1} j).counit.app F) := by
  let a := openImmersionLowerShriekUpperStarAdjunction AddCommGrpCat.{u + 1} j
  have : IsIso a.unit := a.unit_isIso_of_L_fully_faithful
  have hj : IsIso ((upperStar AddCommGrpCat.{u + 1} j).map (a.counit.app F)) := by
    have ht := a.right_triangle_components (Y := F)
    rw [← IsIso.inv_eq_of_hom_inv_id ht]
    infer_instance
  have hi : IsIso ((upperStar AddCommGrpCat.{u + 1} i).map (a.counit.app F)) := by
    have hs := ab_open_disjoint (N := (upperStar AddCommGrpCat.{u + 1} j).obj F)
      j i (by rw [h]; exact disjoint_compl_right)
    exact isIso_of_source_target_iso_zero _ hs.isoZero hz.isoZero
  exact abDetectIso i j h (a.counit.app F)

private def AbSupported {X : Scheme.{u}}
    (F : Sheaf (ProEt.topology X) AddCommGrpCat.{u + 1}) (s : Set X) : Prop :=
  ∀ {Y : Scheme.{u}} [IsNoetherian Y] (f : Y ⟶ X), Disjoint (Set.range f) s →
    IsZero ((upperStar AddCommGrpCat.{u + 1} f).obj F)

private theorem ab_supported_open {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] (N : Sheaf (ProEt.topology U) AddCommGrpCat.{u + 1})
    (s : Set U) (hs : AbSupported N s) :
    AbSupported ((openImmersionLowerShriek AddCommGrpCat.{u + 1} j).obj N) (j '' s) := by
  intro Y _ f hd
  let p : pullback j f ⟶ U := pullback.fst j f
  let q : pullback j f ⟶ Y := pullback.snd j f
  let : IsLocallyNoetherian (pullback j f) := isLocallyNoetherian_of_isOpenImmersion q
  let : NoetherianSpace (pullback (C := Scheme) j f) := q.isOpenEmbedding.isInducing.noetherianSpace
  let : IsNoetherian (pullback j f) := ⟨⟩
  have hp : Disjoint (Set.range p) s := by
    apply Set.disjoint_left.mpr
    rintro x ⟨z, rfl⟩ hx
    apply Set.disjoint_left.mp hd (show j (p z) ∈ Set.range f from ?_) ⟨p z, hx, rfl⟩
    refine ⟨q z, ?_⟩
    exact (congrArg (fun k : pullback j f ⟶ X ↦ k z) (pullback.condition (f := j) (g := f))).symm
  have hz := hs p hp
  have : (openImmersionLowerShriek AddCommGrpCat.{u + 1} q).IsLeftAdjoint :=
    (openImmersionLowerShriekUpperStarAdjunction AddCommGrpCat.{u + 1} q).isLeftAdjoint
  exact ((openImmersionLowerShriek AddCommGrpCat.{u + 1} q).map_isZero hz).of_iso
    ((openImmersionLowerShriekBaseChangeIso AddCommGrpCat.{u + 1}
      (IsPullback.of_hasPullback j f)).app N).symm

private theorem ab_closed_disjoint {S X Y : Scheme.{u}} (c : S ⟶ X)
    [IsClosedImmersion c] (f : Y ⟶ X)
    (h : Disjoint (Set.range f) (Set.range c))
    (N : Sheaf (ProEt.topology S) AddCommGrpCat.{u + 1}) :
    IsZero ((upperStar AddCommGrpCat.{u + 1} f).obj
      ((lowerStar AddCommGrpCat.{u + 1} c).obj N)) := by
  let V : X.Opens :=
    ⟨(Set.range c)ᶜ, c.isClosedEmbedding.isClosed_range.isOpen_compl⟩
  have hf : Set.range f ⊆ Set.range V.ι := by
    rw [V.range_ι]
    exact Set.disjoint_left.mp h
  let l := IsOpenImmersion.lift V.ι f hf
  have hz := isZero_upperStar_lowerStar_of_disjoint AddCommGrpCat.{u + 1} c V.ι
    (by rw [V.range_ι]; exact disjoint_compl_right) N
  have hz' := ((upperStar AddCommGrpCat.{u + 1} l).map_isZero hz).of_iso
    ((upperStarComp AddCommGrpCat.{u + 1} l V.ι).app _)
  simpa only [l, IsOpenImmersion.lift_fac] using hz'

private theorem ab_supported_closed {S X : Scheme.{u}} [IsNoetherian X]
    (c : S ⟶ X) [IsClosedImmersion c]
    (N : Sheaf (ProEt.topology S) AddCommGrpCat.{u + 1}) (s : Set S)
    (hs : AbSupported N s) :
    AbSupported ((lowerStar AddCommGrpCat.{u + 1} c).obj N) (c '' s) := by
  intro Y _ f hd
  let p : pullback c f ⟶ S := pullback.fst c f
  let q : pullback c f ⟶ Y := pullback.snd c f
  let : IsLocallyNoetherian (pullback c f) := LocallyOfFiniteType.isLocallyNoetherian q
  let : CompactSpace (pullback (C := Scheme) c f) := QuasiCompact.compactSpace_of_compactSpace q
  let : IsNoetherian (pullback c f) := ⟨⟩
  let V : Y.Opens :=
    ⟨(Set.range q)ᶜ, q.isClosedEmbedding.isClosed_range.isOpen_compl⟩
  let : NoetherianSpace V.toScheme := V.ι.isOpenEmbedding.isInducing.noetherianSpace
  let G := (upperStar AddCommGrpCat.{u + 1} f).obj
    ((lowerStar AddCommGrpCat.{u + 1} c).obj N)
  apply abJointZero q V.ι V.range_ι G
  · have hp : Disjoint (Set.range p) s := by
      apply Set.disjoint_left.mpr
      rintro x ⟨z, rfl⟩ hx
      apply Set.disjoint_left.mp hd (show c (p z) ∈ Set.range f from ?_) ⟨p z, hx, rfl⟩
      refine ⟨q z, ?_⟩
      exact (congrArg (fun k : pullback c f ⟶ X ↦ k z)
        (pullback.condition (f := c) (g := f))).symm
    let e : (upperStar AddCommGrpCat.{u + 1} q).obj G ≅
        (upperStar AddCommGrpCat.{u + 1} p).obj N :=
      ((upperStarComp AddCommGrpCat.{u + 1} q f).app _).symm ≪≫
      (eqToIso (congrArg (fun g : pullback c f ⟶ X ↦
        (upperStar AddCommGrpCat.{u + 1} g).obj
          ((lowerStar AddCommGrpCat.{u + 1} c).obj N))
        (pullback.condition (f := c) (g := f)).symm)) ≪≫
      ((upperStarComp AddCommGrpCat.{u + 1} p c).app _) ≪≫
      (upperStar AddCommGrpCat.{u + 1} p).mapIso
        (asIso ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} c).counit.app N))
    exact (hs p hp).of_iso e
  · have hv : Disjoint (Set.range (V.ι ≫ f)) (Set.range c) := by
      apply Set.disjoint_left.mpr
      rintro x ⟨z, rfl⟩ hx
      have hq : V.ι z ∈ Set.range q := by
        dsimp [q]
        rw [Scheme.Pullback.range_snd]
        exact hx
      have hz : V.ι z ∉ Set.range q := by
        have hz : V.ι z ∈ Set.range V.ι := ⟨z, rfl⟩
        rw [V.range_ι] at hz
        exact hz
      exact hz hq
    exact (ab_closed_disjoint c (V.ι ≫ f) hv N).of_iso
      ((upperStarComp AddCommGrpCat.{u + 1} V.ι f).app _).symm

private theorem ab_supported_iso {X : Scheme.{u}}
    {F G : Sheaf (ProEt.topology X) AddCommGrpCat.{u + 1}}
    (e : F ≅ G) (s : Set X) (h : AbSupported G s) : AbSupported F s := by
  intro Y _ f hd
  exact (h f hd).of_iso ((upperStar AddCommGrpCat.{u + 1} f).mapIso e)

private theorem ab_supported_univ {X : Scheme.{u}}
    (F : Sheaf (ProEt.topology X) AddCommGrpCat.{u + 1}) : AbSupported F Set.univ := by
  intro Y _ f hd
  let : IsEmpty Y := ⟨fun y ↦ Set.disjoint_left.mp hd ⟨y, rfl⟩ (Set.mem_univ _)⟩
  apply Sheaf.isZero_of_isZero_obj
  rintro ⟨V⟩
  let : IsEmpty V.left := ⟨fun y ↦ isEmptyElim (show Y from V.hom.base y)⟩
  exact (isZero_zero AddCommGrpCat.{u + 1}).of_iso
    ((ProEt.isTerminalSectionsOfIsEmpty _ V).uniqueUpToIso HasZeroObject.zeroIsTerminal)

private def open_carrier_iso {S X : LocallyClosedCoefficients.{u}}
    (v : LocallyClosedCoefficientImmersion S X) (hv : IsOpenImmersion v.hom)
    (N : proEtaleRingModules S.scheme S.ring) :
    (SheafOfModules.toSheaf _).obj
        ((LocallyClosedCoefficientImmersion.modelOpenExtension v hv).obj N) ≅
      (openImmersionLowerShriek AddCommGrpCat.{u + 1} v.hom).obj
        ((SheafOfModules.toSheaf _).obj N) := by
  let := hv
  let : IsNoetherian X.scheme := ⟨⟩
  let : NoetherianSpace S.scheme := v.hom.isOpenEmbedding.isInducing.noetherianSpace
  let Z : Closeds X.scheme :=
    ⟨(Set.range v.hom)ᶜ, v.hom.isOpenEmbedding.isOpen_range.isClosed_compl⟩
  let I := IdealSheafData.vanishingIdeal Z
  have hZ : Set.range v.hom = (Set.range I.subschemeι)ᶜ := by
    rw [I.range_subschemeι, IdealSheafData.coe_support_vanishingIdeal]
    exact (compl_compl (Set.range v.hom)).symm
  let Ri := (proEtaleSheafInverseImage I.subschemeι CommRingCat.{u + 1}).obj X.ring
  let O := LocallyClosedCoefficientImmersion.modelOpenExtension v hv
  let F := (SheafOfModules.toSheaf _).obj (O.obj N)
  have hz : IsZero ((upperStar AddCommGrpCat.{u + 1} I.subschemeι).obj F) :=
    (pull_zero_iff _ _ _ _ _).1 ((open_image_support v hv I.subschemeι hZ
      Ri (Iso.refl _)).1 N)
  have : IsIso ((openImmersionLowerShriekUpperStarAdjunction
      AddCommGrpCat.{u + 1} v.hom).counit.app F) :=
    ab_open_counit_iso I.subschemeι v.hom hZ F hz
  let e : (upperStar AddCommGrpCat.{u + 1} v.hom).obj F ≅
      (SheafOfModules.toSheaf _).obj N :=
    (pull_carrier_iso v.hom X.ring S.ring v.coefficient (O.obj N)).symm ≪≫
      ((SheafOfModules.toSheaf _).mapIso
        ((asIso (LocallyClosedCoefficientImmersion.modelOpenAdjunction v hv).unit).app N)).symm
  exact (asIso ((openImmersionLowerShriekUpperStarAdjunction
    AddCommGrpCat.{u + 1} v.hom).counit.app F)).symm ≪≫
      (openImmersionLowerShriek AddCommGrpCat.{u + 1} v.hom).mapIso e

private theorem model_supported {S X : LocallyClosedCoefficients.{u}}
    (a : LocallyClosedCoefficientImmersion S X)
    (N : proEtaleRingModules S.scheme S.ring) (s : Set S.scheme)
    (hs : AbSupported ((SheafOfModules.toSheaf _).obj N) s) :
    AbSupported ((SheafOfModules.toSheaf _).obj (a.modelExtension.obj N)) (a.hom '' s) := by
  let : IsNoetherian X.scheme := ⟨⟩
  let c := a.extensionFactorization.closed
  let v := a.extensionFactorization.openMap
  let : IsNoetherian a.extensionFactorization.middle.scheme := ⟨⟩
  have h : AbSupported
      ((lowerStar AddCommGrpCat.{u + 1} c.hom).obj ((SheafOfModules.toSheaf _).obj N))
      (c.hom '' s) := ab_supported_closed (S := S.scheme)
    (X := a.extensionFactorization.middle.scheme) c.hom
    ((SheafOfModules.toSheaf _).obj N) s hs
  have h' : AbSupported ((SheafOfModules.toSheaf _).obj (c.push.obj N))
      (c.hom '' s) := ab_supported_iso (push_carrier_iso c.hom _ _ c.coefficient N) _ h
  have h'' : AbSupported
      ((openImmersionLowerShriek AddCommGrpCat.{u + 1} v.hom).obj
        ((SheafOfModules.toSheaf _).obj (c.push.obj N))) (v.hom '' (c.hom '' s)) :=
    ab_supported_open v.hom _ (c.hom '' s) h'
  have h''' : AbSupported ((SheafOfModules.toSheaf _).obj
      ((LocallyClosedCoefficientImmersion.modelOpenExtension v
        a.extensionFactorization.isOpen).obj (c.push.obj N))) (v.hom '' (c.hom '' s)) :=
    ab_supported_iso (open_carrier_iso v a.extensionFactorization.isOpen
    (c.push.obj N)) _ h''
  have hc : c.hom ≫ v.hom = a.hom :=
    congrArg LocallyClosedCoefficientImmersion.hom a.extensionFactorization.composite
  have heq : a.hom '' s = v.hom '' (c.hom '' s) := by
    rw [← Set.image_comp]
    exact (congrArg (fun f : S.scheme ⟶ X.scheme ↦ f '' s) hc).symm
  rw [a.modelExtension_eq]
  rw [heq]
  exact @h'''

private theorem model_mem_essImage {S X : LocallyClosedCoefficients.{u}}
    (a : LocallyClosedCoefficientImmersion S X) (A : proEtaleRingModules X.scheme X.ring)
    (hA : AbSupported ((SheafOfModules.toSheaf _).obj A) (Set.range a.hom)) :
    a.modelExtension.essImage A := by
  let : IsNoetherian X.scheme := ⟨⟩
  let c := a.extensionFactorization.closed
  let v := a.extensionFactorization.openMap
  let O := LocallyClosedCoefficientImmersion.modelOpenExtension v a.extensionFactorization.isOpen
  let N := v.pull.obj A
  let : IsNoetherian a.extensionFactorization.middle.scheme := ⟨⟩
  have hc : c.hom ≫ v.hom = a.hom :=
    congrArg LocallyClosedCoefficientImmersion.hom a.extensionFactorization.composite
  let Z : Closeds X.scheme :=
    ⟨(Set.range v.hom)ᶜ, v.hom.isOpenEmbedding.isOpen_range.isClosed_compl⟩
  let I := IdealSheafData.vanishingIdeal Z
  have hZ : Set.range v.hom = (Set.range I.subschemeι)ᶜ := by
    rw [I.range_subschemeι, IdealSheafData.coe_support_vanishingIdeal]
    exact (compl_compl (Set.range v.hom)).symm
  let : IsLocallyNoetherian I.subscheme := LocallyOfFiniteType.isLocallyNoetherian I.subschemeι
  let : CompactSpace I.subscheme :=
    QuasiCompact.compactSpace_of_compactSpace I.subschemeι
  let : IsNoetherian I.subscheme := ⟨⟩
  have hi : Disjoint (Set.range I.subschemeι) (Set.range a.hom) := by
    rw [← hc]
    apply Set.disjoint_left.mpr
    rintro x hx ⟨z, rfl⟩
    have hx' : v.hom (c.hom z) ∈ (Set.range v.hom)ᶜ := by
      rw [hZ, compl_compl]
      exact hx
    exact hx' ⟨c.hom z, rfl⟩
  have hz : IsZero ((proEtaleRingModulePullback I.subschemeι X.ring
      ((proEtaleSheafInverseImage I.subschemeι CommRingCat.{u + 1}).obj X.ring)
      (Iso.refl _)).obj A) := (pull_zero_iff _ _ _ _ _).2 (hA I.subschemeι hi)
  have ho : IsIso ((LocallyClosedCoefficientImmersion.modelOpenAdjunction
      v a.extensionFactorization.isOpen).counit.app A) :=
    (open_image_support v a.extensionFactorization.isOpen I.subschemeι hZ _ (Iso.refl _)).2 A hz
  let W : a.extensionFactorization.middle.scheme.Opens :=
    ⟨(Set.range c.hom)ᶜ, c.hom.isClosedEmbedding.isClosed_range.isOpen_compl⟩
  let : NoetherianSpace W.toScheme := W.ι.isOpenEmbedding.isInducing.noetherianSpace
  let : IsNoetherian W.toScheme := ⟨⟩
  have hw : Disjoint (Set.range (W.ι ≫ v.hom)) (Set.range a.hom) := by
    rw [← hc]
    apply Set.disjoint_left.mpr
    rintro x ⟨z, rfl⟩ ⟨t, ht⟩
    have ht' : c.hom t = W.ι z := v.hom.isOpenEmbedding.injective ht
    have hz' : W.ι z ∈ (Set.range c.hom)ᶜ := by
      have hz : W.ι z ∈ Set.range W.ι := ⟨z, rfl⟩
      rw [W.range_ι] at hz
      exact hz
    exact hz' ⟨t, ht'⟩
  have hn : IsZero ((proEtaleRingModulePullback W.ι
      a.extensionFactorization.middle.ring
      ((proEtaleSheafInverseImage W.ι CommRingCat.{u + 1}).obj
        a.extensionFactorization.middle.ring) (Iso.refl _)).obj N) := by
    apply (pull_zero_iff _ _ _ _ _).2
    have h := hA (W.ι ≫ v.hom) hw
    exact h.of_iso
      ((upperStar AddCommGrpCat.{u + 1} W.ι).mapIso
        (pull_carrier_iso v.hom _ _ v.coefficient A) ≪≫
        ((upperStarComp AddCommGrpCat.{u + 1} W.ι v.hom).app _).symm)
  obtain ⟨Q, ⟨e⟩⟩ :=
    (proEtaleRingModule_closed_essImage_iff_and_unit_isIso c.hom W.ι W.range_ι
      a.extensionFactorization.middle.ring S.ring _ c.coefficient (Iso.refl _) N).1.2 hn
  rw [a.modelExtension_eq]
  exact ⟨Q, ⟨O.mapIso e ≪≫ asIso ((LocallyClosedCoefficientImmersion.modelOpenAdjunction
    v a.extensionFactorization.isOpen).counit.app A)⟩⟩

/-- Two fixed extensions have a normalized comparison on each input module.
This assertion has no naturality, identity comparisons, or associativity conclusions.

Source: Stacks Project, Tags 09AH and 02V0; Steps 3--8 of
lem-sfb-locally-closed-module-extension-coherence.
(blueprint: lem-sfb-locally-closed-module-extension-binary).

Proof: write a = v c and b = w d using their chosen factorizations. Lift the open w
in the closed subscheme c to an ambient open h; its intersection with c is a closed
e with c w = h e. The localization sequence and the two complementary vanishing
restrictions identify c_* w_! M with h_! e_* M. The actual identified-coefficient
supported-reconstruction theorem constructs the isomorphism and proves its restriction
equation using the open unit and closed counit. The open-restriction-counit theorem
matches that equation with the restriction of c_* w_!. Compose the pure open factors
by uniqueness of left adjoints with their specified units. Compose the pure closed
factors by fibre-product pasting of direct images; its conjugate inverse-image map is
the specified pullComp. The resulting functor is the closed-then-open extension for
(v h)(e d). Intersect its ambient open with the one chosen for ab and shrink both as
in the boundary comparison. Each map preserves restriction, so their composite has
the displayed normalization. For uniqueness, conjugate the source by one such
isomorphism. Full faithfulness of the model for ab, together with modelRestriction,
makes its pullback injective on morphisms between its image objects. The displayed
equation fixes the pullback, hence the hom and the entire isomorphism. These arguments
apply to zero modules and empty or identity factors without change. -/
theorem locallyClosedModel_binary_exists {S X T : LocallyClosedCoefficients.{u}}
    (a : LocallyClosedCoefficientImmersion S X) (b : LocallyClosedCoefficientImmersion T S)
    (M : proEtaleRingModules T.scheme T.ring) :
    ∃ e : a.modelExtension.obj (b.modelExtension.obj M) ≅ (a.comp b).modelExtension.obj M,
      LocallyClosedObjectNormalization (a.comp b).modelExtension (a.comp b).pull
        (a.comp b).modelRestriction
        (LocallyClosedCompositeRestrictionMap a.modelExtension b.modelExtension a.pull b.pull
          (a.comp b).pull a.modelRestriction b.modelRestriction (a.pullComp b) M) e := by
  let t := (a.pullComp b).app (a.modelExtension.obj (b.modelExtension.obj M)) ≪≫
    b.pull.mapIso (a.modelRestriction.app (b.modelExtension.obj M)) ≪≫
      b.modelRestriction.app M
  let : IsNoetherian X.scheme := ⟨⟩
  apply normalized_of_essImage (a.comp b).modelExtension (a.comp b).pull
    (a.comp b).modelRestriction t
  apply model_mem_essImage
  have h : AbSupported ((SheafOfModules.toSheaf _).obj (b.modelExtension.obj M))
      (b.hom '' Set.univ) := model_supported (S := T) (X := S) b M Set.univ
    (ab_supported_univ (X := T.scheme) ((SheafOfModules.toSheaf _).obj M))
  have h' : AbSupported
      ((SheafOfModules.toSheaf _).obj (a.modelExtension.obj (b.modelExtension.obj M)))
      (a.hom '' (b.hom '' Set.univ)) :=
    model_supported (S := S) (X := X) a (b.modelExtension.obj M) (b.hom '' Set.univ) h
  have heq : Set.range (a.comp b).hom = a.hom '' (b.hom '' Set.univ) := by
    rw [Set.image_univ, ← Set.range_comp]
    rfl
  rw [heq]
  exact @h'

/-- A family of normalized natural binary comparisons for the fixed model.
It is a parameter of the formal unit/associativity assertion, not an existence claim.
Source: Stacks, Tag 02V0
(blueprint: lem-sfb-locally-closed-module-extension-binary). -/
structure LocallyClosedModelComposition where
  gamma : ∀ {S X T : LocallyClosedCoefficients.{u}}
    (a : LocallyClosedCoefficientImmersion S X) (b : LocallyClosedCoefficientImmersion T S),
    b.modelExtension ⋙ a.modelExtension ≅ (a.comp b).modelExtension
  normalized : ∀ {S X T : LocallyClosedCoefficients.{u}}
    (a : LocallyClosedCoefficientImmersion S X) (b : LocallyClosedCoefficientImmersion T S),
    LocallyClosedBinaryNormalization a.modelExtension b.modelExtension a.pull b.pull
      (a.comp b).pull (a.comp b).modelExtension a.modelRestriction b.modelRestriction
      (a.comp b).modelRestriction (a.pullComp b) (gamma a b)

end AlgebraicGeometry.Scheme
