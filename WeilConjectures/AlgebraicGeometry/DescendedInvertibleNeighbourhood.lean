/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Fiber
public import WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
import WeilConjectures.AlgebraicGeometry.Modules.LocallyFreeAffine
import Mathlib.AlgebraicGeometry.Properties

/-! # Local triviality of a descended invertible module

Source: Stacks Project, Tag 0BF2, proof paragraph beginning with shrinking the base;
Tag 0BF0, field rank calculation.
-/

@[expose] public section
set_option autoImplicit false
universe v
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

private noncomputable def tensorIsoPullback {A B : Scheme.{v}} (g : A ⟶ B) :
    Modules.tensorPullback g ≅ Modules.pullback g :=
  (Modules.nonempty_tensorPullbackAdjunction g).some.leftAdjointUniq
    (Modules.pullbackPushforwardAdjunction g)

private theorem nonempty_of_unit_iso {A B : Scheme.{v}} [Nonempty B] (g : A ⟶ B)
    (h : IsIso ((Classical.choose (Modules.exists_tensorPullbackAdjunction g)).unit.app
      (SheafOfModules.unit B.ringCatSheaf))) : Nonempty A := by
  classical
  by_contra hn
  have : IsEmpty A := not_nonempty_iff.mp hn
  let adj := Classical.choose (Modules.exists_tensorPullbackAdjunction g)
  have : IsIso (adj.unit.app (SheafOfModules.unit B.ringCatSheaf)) := h
  have hz := Modules.isZero_of_isEmpty
    ((Modules.tensorPullback g).obj (SheafOfModules.unit B.ringCatSheaf))
  have hpush := (Modules.pushforward g).map_isZero hz
  exact Modules.not_isZero_unit B
    (hpush.of_iso (asIso (adj.unit.app (SheafOfModules.unit B.ringCatSheaf))))

private theorem exists_local_unit_of_invertible_pullback
    {A B : Scheme.{v}} (p : A ⟶ B) (N : B.Modules) [N.IsFiniteLocallyFree]
    [((Modules.pullback p).obj N).IsInvertible] (y : A) :
    ∃ V : B.Opens, p y ∈ V ∧
      Nonempty ((Modules.pullback V.ι).obj N ≅ SheafOfModules.unit _) := by
  classical
  obtain ⟨V, I, hI, hyV, ⟨eover⟩⟩ := Modules.exists_mem_over_iso_free N (p y)
  let eV : (Modules.pullback V.ι).obj N ≅ SheafOfModules.free I :=
    ((Modules.restrictFunctorIsoPullback V.ι).app N).symm ≪≫
      Modules.overIsoFreeEquiv N V I eover
  let D := p ⁻¹ᵁ V
  let d := p ∣_ V
  let P := (Modules.pullback D.ι).obj ((Modules.pullback p).obj N)
  have : P.IsInvertible := inferInstance
  let ef : P ≅ SheafOfModules.free I :=
    (Modules.pullbackComp D.ι p).app N ≪≫
      (Modules.pullbackCongr (morphismRestrict_ι p V).symm).app N ≪≫
      ((Modules.pullbackComp d V.ι).symm).app N ≪≫
      (Modules.pullback d).mapIso eV ≪≫ Modules.pullbackFreeIso d I
  obtain ⟨H, hyH, ⟨eu⟩⟩ := Modules.IsInvertible.exists_isoUnit (M := P) ⟨y, hyV⟩
  have : Nonempty H := ⟨⟨⟨y, hyV⟩, hyH⟩⟩
  let F := (Modules.pullback H.ι).obj P
  let efH : F ≅ SheafOfModules.free I :=
    (Modules.pullback H.ι).mapIso ef ≪≫ Modules.pullbackFreeIso H.ι I
  have hcard : Fintype.card I = 1 := by
    let R := Γ(H.toScheme, ⊤)
    have : Nonempty (⊤ : H.toScheme.Opens) := ⟨⟨⟨⟨y, hyV⟩, hyH⟩, trivial⟩⟩
    have : Nontrivial R := Scheme.component_nontrivial H.toScheme ⊤
    have hi : Module.finrank R Γ(F, ⊤) = Fintype.card I := by
      rw [(Modules.appLinearEquivOfIso efH ⊤).finrank_eq,
        (Modules.freeSectionsEquiv I).finrank_eq]
      exact Module.finrank_fintype_fun_eq_card R
    have h₁ : Module.finrank R Γ(F, ⊤) = 1 := by
      rw [(Modules.appLinearEquivOfIso eu ⊤).finrank_eq]
      exact Module.finrank_self R
    exact hi.symm.trans h₁
  obtain ⟨i, hi⟩ := Fintype.card_eq_one_iff.mp hcard
  let : Unique I := ⟨⟨i⟩, hi⟩
  exact ⟨V, hyV, ⟨eV ≪≫ coproductUniqueIso
    (fun _ : I ↦ SheafOfModules.unit V.toScheme.ringCatSheaf)⟩⟩

/-- Descent to a vector bundle gives a rank-one trivialization near a base point.
Source: Stacks Project, Tags 0BF2 and 0BF0, rank-one descent and local trivialization. -/
theorem exists_descendedInvertible_neighbourhood
    {X S : Scheme.{v}} (f : X ⟶ S)
    (hO : ∀ {T : Scheme.{v}} (g : T ⟶ S),
      IsIso ((Classical.choose
        (Modules.exists_tensorPullbackAdjunction (pullback.snd f g))).unit.app
          (SheafOfModules.unit T.ringCatSheaf)))
    (M : X.Modules) [M.IsInvertible]
    (W : Scheme.{v}) (k : W ⟶ S) (w : W)
    (hM : ∃ (N : W.Modules) (_ : N.IsFiniteLocallyFree),
      Nonempty ((Modules.tensorPullback (pullback.fst f k)).obj M ≅
        (Modules.tensorPullback (pullback.snd f k)).obj N)) :
    ∃ V : W.Opens, w ∈ V ∧ ∀ U : W.Opens, U ≤ V →
      Nonempty ((Modules.tensorPullback (pullback.fst f (U.ι ≫ k))).obj M ≅
        SheafOfModules.unit (pullback f (U.ι ≫ k)).ringCatSheaf) := by
  classical
  obtain ⟨N, hN, ⟨e⟩⟩ := hM
  let Z := pullback f k
  let a : Z ⟶ X := pullback.fst f k
  let b : Z ⟶ W := pullback.snd f k
  let eu : (Modules.pullback a).obj M ≅ (Modules.pullback b).obj N :=
    ((tensorIsoPullback a).app M).symm ≪≫ e ≪≫ (tensorIsoPullback b).app N
  have : ((Modules.pullback b).obj N).IsInvertible := Modules.IsInvertible.of_iso eu
  let r := W.fromSpecResidueField w
  let Y := pullback f (r ≫ k)
  have : Nonempty (Spec (W.residueField w)) := ⟨IsLocalRing.closedPoint _⟩
  have hY : Nonempty Y := nonempty_of_unit_iso (pullback.snd f (r ≫ k)) (hO (r ≫ k))
  let y : Y := Classical.choice hY
  let q : Y ⟶ Z := pullback.lift (pullback.fst f (r ≫ k))
    (pullback.snd f (r ≫ k) ≫ r) (by rw [Category.assoc]; exact pullback.condition)
  have hqw : b (q y) = w := by
    have hq : q ≫ b = pullback.snd f (r ≫ k) ≫ r := pullback.lift_snd _ _ _
    have he := congrArg (fun t : Y ⟶ W ↦ t y) hq
    simpa [Hom.comp_apply, r] using he
  obtain ⟨V, hwV, ⟨eV⟩⟩ := exists_local_unit_of_invertible_pullback b N (q y)
  refine ⟨V, by simpa [hqw] using hwV, ?_⟩
  intro U hUV
  let j := W.homOfLE hUV
  let eU : (Modules.pullback U.ι).obj N ≅ SheafOfModules.unit _ :=
    (Modules.pullbackCongr (W.homOfLE_ι hUV).symm).app N ≪≫
      ((Modules.pullbackComp j V.ι).symm).app N ≪≫
      (Modules.pullback j).mapIso eV ≪≫ Modules.pullbackObjUnitIso j
  let ZU := pullback f (U.ι ≫ k)
  let aU : ZU ⟶ X := pullback.fst f (U.ι ≫ k)
  let bU : ZU ⟶ U.toScheme := pullback.snd f (U.ι ≫ k)
  let t : ZU ⟶ Z := pullback.lift aU (bU ≫ U.ι)
    (by rw [Category.assoc]; exact pullback.condition)
  have hta : t ≫ a = aU := pullback.lift_fst _ _ _
  have htb : t ≫ b = bU ≫ U.ι := pullback.lift_snd _ _ _
  exact ⟨(tensorIsoPullback aU).app M ≪≫
    (Modules.pullbackCongr hta.symm).app M ≪≫
    ((Modules.pullbackComp t a).symm).app M ≪≫
    (Modules.pullback t).mapIso eu ≪≫
    (Modules.pullbackComp t b).app N ≪≫
    (Modules.pullbackCongr htb).app N ≪≫
    ((Modules.pullbackComp bU U.ι).symm).app N ≪≫
    (Modules.pullback bU).mapIso eU ≪≫ Modules.pullbackObjUnitIso bU⟩

end AlgebraicGeometry.Scheme
