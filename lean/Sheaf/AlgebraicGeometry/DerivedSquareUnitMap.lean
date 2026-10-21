/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G1
-/
module

public import Sheaf.AlgebraicGeometry.DerivedPullbackTopCohomology
public import WeilConjectures.AlgebraicGeometry.PinnedDerivedAdjunctionShifts
public import WeilConjectures.AlgebraicGeometry.Picard.CanonicalSingleDirectImageComparison
import Sheaf.AlgebraicGeometry.Picard.CanonicalSingleAdjunctionTranspose

/-! # The ordinary unit representative of a derived square

Source: Stacks Project, Cohomology, Tags 01FB and 08HY.
(blueprint: lem-weil-pbc-derived-square-unit-map).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
universe u w v
open CategoryTheory CategoryTheory.Limits
noncomputable section

private theorem square_transpose
    {A B C D : Type*} [Category.{v} A] [Category.{v} B] [Category.{v} C] [Category.{v} D]
    {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : A ⥤ C} {R₂ : C ⥤ A}
    {L₃ : B ⥤ D} {R₃ : D ⥤ B} {L₄ : C ⥤ D} {R₄ : D ⥤ C}
    (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂) (a₃ : L₃ ⊣ R₃) (a₄ : L₄ ⊣ R₄)
    (s : L₂ ⋙ L₄ ≅ L₁ ⋙ L₃) (M : B) (N : D) (c : L₃.obj M ⟶ N) :
    a₂.homEquiv _ _ (a₄.homEquiv _ _
      (s.hom.app (R₁.obj M) ≫ L₃.map (a₁.counit.app M) ≫ c)) =
    R₁.map (a₃.homEquiv _ _ c) ≫
      (conjugateIsoEquiv (a₁.comp a₃) (a₂.comp a₄) s).hom.app N := by
  suffices (a₂.comp a₄).homEquiv _ _
      (s.hom.app (R₁.obj M) ≫ L₃.map (a₁.counit.app M) ≫ c) =
        R₁.map (a₃.homEquiv _ _ c) ≫
          (conjugateIsoEquiv (a₁.comp a₃) (a₂.comp a₄) s).hom.app N by
    have hh : (a₂.comp a₄).homEquiv (R₁.obj M) N
        (s.hom.app (R₁.obj M) ≫ L₃.map (a₁.counit.app M) ≫ c) =
        a₂.homEquiv _ _ (a₄.homEquiv _ _
          (s.hom.app (R₁.obj M) ≫ L₃.map (a₁.counit.app M) ≫ c)) := by
      rw [Adjunction.comp_homEquiv]
      rfl
    exact hh.symm.trans this
  apply ((a₂.comp a₄).homEquiv _ _).symm.injective
  rw [Equiv.symm_apply_apply, Adjunction.homEquiv_symm_apply]
  change s.hom.app (R₁.obj M) ≫ L₃.map (a₁.counit.app M) ≫ c =
    (L₂ ⋙ L₄).map (R₁.map (a₃.homEquiv _ _ c) ≫
      (conjugateEquiv (a₁.comp a₃) (a₂.comp a₄) s.hom).app N) ≫
        (a₂.comp a₄).counit.app N
  rw [Functor.map_comp, Category.assoc,
    conjugateEquiv_counit (a₁.comp a₃) (a₂.comp a₄) s.hom]
  have hn := congrArg (fun b ↦ b ≫ (a₁.comp a₃).counit.app N)
    (s.hom.naturality (R₁.map (a₃.homEquiv _ _ c)))
  simp only [Category.assoc] at hn
  simp only [Functor.comp_obj] at *
  rw [hn]
  simp only [Functor.comp_map, Adjunction.comp_counit_app]
  rw [← L₃.map_comp_assoc, a₁.counit_naturality]
  rw [L₃.map_comp, Category.assoc]
  have hc : L₃.map ((a₃.homEquiv M N) c) ≫ a₃.counit.app N = c :=
    (a₃.homEquiv M N).symm_apply_apply c
  rw [hc]

namespace AlgebraicGeometry
attribute [local irreducible] Scheme.Modules.tensorPullback Adjunction.leftAdjointUniq
  Functor.rightDerivedFunctor pinnedModulePullbackComparisonAt

variable [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]

/-- The right-adjoint mate of the pinned pullback square, with its scalar normalization.
Source: Stacks Project, Tag 08HY
(blueprint: lem-weil-pbc-derived-square-unit-map). -/
def derivedSquareRightComparison {X S Z T : Scheme.{u}}
    (f : X ⟶ S) (k : Z ⟶ T) (g : T ⟶ S) (v : Z ⟶ X) (h : v ≫ f = k ≫ g) :
    schemeDerivedDirectImage v ⋙ schemeDerivedDirectImage f ≅
      schemeDerivedDirectImage k ⋙ schemeDerivedDirectImage g :=
  letI : ∀ {Y Y' : Scheme.{u}} (a : Y ⟶ Y'),
      (Scheme.Modules.tensorPullback a).Additive :=
    fun a ↦ Scheme.Modules.canonicalTensorPullbackAdditive.{u, w} a
  conjugateIsoEquiv ((pinnedDerivedAdjunction f).comp (pinnedDerivedAdjunction v))
    ((pinnedDerivedAdjunction g).comp (pinnedDerivedAdjunction k))
    (pinnedPullbackComposition k g ≪≫
      eqToIso (congrArg (fun a ↦ derivedPullback a) h.symm) ≪≫
        (pinnedPullbackComposition v f).symm)

/-- Apply Rf to the ordinary coefficient map in degree zero and its direct-image unit,
then use the right-adjoint comparison of the square. This construction makes sense for
an arbitrary h-map and an arbitrary commutative square.
Source: Stacks Project, Tags 01FB and 08HY
(blueprint: lem-weil-pbc-derived-square-unit-map). -/
def derivedSquareUnitMap {X S Z T : Scheme.{u}}
    (f : X ⟶ S) (k : Z ⟶ T) (g : T ⟶ S) (v : Z ⟶ X) (h : v ≫ f = k ≫ g)
    (F : X.Modules) (G : Z.Modules) (φ : F ⟶ (Scheme.Modules.pushforward v).obj G) :
    (schemeDerivedDirectImage f).obj ((DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj F) ⟶
    (schemeDerivedDirectImage g).obj ((schemeDerivedDirectImage k).obj
      ((DerivedCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) 0).obj G)) :=
  (schemeDerivedDirectImage f).map
      ((DerivedCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).map φ ≫
          Scheme.Modules.canonicalSingleDirectImageMap v G) ≫
    (derivedSquareRightComparison f k g v h).hom.app
      ((DerivedCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) 0).obj G)

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
-- Avoid unfolding the unique-adjoint comparison during elaboration.
private theorem tensor_single_transpose {X Y : Scheme.{u}} (v : X ⟶ Y) (F : Y.Modules) :
    (@pinnedDerivedAdjunction.{u, w} _
      (fun {_ _} a ↦ Scheme.Modules.canonicalTensorPullbackAdditive.{u, w} a)
      _ _ v).homEquiv _ _ (pinnedModulePullbackComparisonAt v 0 F) =
      (DerivedCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).map
          ((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction v)).unit.app F) ≫
        Scheme.Modules.canonicalSingleDirectImageMap v
          ((Scheme.Modules.tensorPullback v).obj F) := by
  dsimp only [Scheme.Modules, Scheme.ringCatSheaf] at *
  let adj := Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction v)
  let adj' := Scheme.Modules.pullbackPushforwardAdjunction v
  let t := adj.leftAdjointUniq adj'
  have h := Scheme.Modules.canonicalSingleAdjunctionTranspose v F
    ((Scheme.Modules.tensorPullback v).obj F) (t.inv.app F)
  have ht : adj'.homEquiv _ _ (t.inv.app F) = adj.unit.app F := by
    change adj'.homEquiv _ _ ((adj.leftAdjointUniq adj').inv.app F) = _
    rw [Adjunction.leftAdjointUniq_inv_app]
    exact Adjunction.homEquiv_leftAdjointUniq_hom_app adj' adj F
  let S := DerivedCategory.singleFunctor
    (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0
  have hf : Scheme.Modules.canonicalSinglePullbackMap v F =
      pinnedModulePullbackComparisonAt v 0 F ≫ S.map (t.hom.app F) := by
    unfold Scheme.Modules.canonicalSinglePullbackMap pinnedModulePullbackComparisonAt
      derivedSingleComparisonOfCounit
    dsimp only [pinnedPullbackCounit, S, t, adj, adj',
      Scheme.Modules, Scheme.ringCatSheaf]
    exact (Category.assoc _ _ _).symm
  have hc : Scheme.Modules.canonicalSinglePullbackMap v F ≫ S.map (t.inv.app F) =
      pinnedModulePullbackComparisonAt v 0 F := by
    rw [hf]
    apply Eq.trans (Category.assoc _ _ _)
    apply Eq.trans (congrArg (fun z ↦ pinnedModulePullbackComparisonAt v 0 F ≫ z)
        ((S.map_comp _ _).symm.trans
          ((congrArg S.map (t.hom_inv_id_app F)).trans (S.map_id _))))
    exact Category.comp_id _
  have h₁ := congrArg (fun z ↦
    (@pinnedDerivedAdjunction.{u, w} _
      (fun {_ _} a ↦ Scheme.Modules.canonicalTensorPullbackAdditive.{u, w} a)
      _ _ v).homEquiv _ _ z) hc
  have h₂ := congrArg (fun z ↦
    (DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).map z ≫
        Scheme.Modules.canonicalSingleDirectImageMap v
          ((Scheme.Modules.tensorPullback v).obj F)) ht
  exact h₁.symm.trans (h.trans h₂)

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- Transposing module base change gives Rf of the ordinary tensor-unit h-map,
followed by the right-adjoint comparison of the square. There is no cohomological bound.
Source: Stacks Project, Cohomology, Remark 08HY and Remark 01FB
(blueprint: lem-weil-pbc-derived-square-unit-map).

Proof: conjugate the pinned pullback square under the two composite adjunctions.
Naturality of the counit gives the double-transpose formula `square_transpose`.
The specified single-module comparison transposes to the single ordinary tensor unit
followed by the direct-image unit, by the single-module transpose theorem. Substitute
this formula and use naturality in the target to move the coefficient comparison
through the first transpose. This argument does not invert the coefficient comparison
or the base-change map. -/
theorem derivedModuleBaseChange_transpose {X S Z T : Scheme.{u}}
    (f : X ⟶ S) (k : Z ⟶ T) (g : T ⟶ S) (v : Z ⟶ X) (h : v ≫ f = k ≫ g)
    (F : X.Modules) :
    (@pinnedDerivedAdjunction.{u, w} _
      (fun {_ _} a ↦ Scheme.Modules.canonicalTensorPullbackAdditive.{u, w} a)
      _ _ g).homEquiv _ _
      (schemeDerivedBaseChangeMap f k g v h
          ((DerivedCategory.singleFunctor
            (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj F) ≫
        (schemeDerivedDirectImage k).map (pinnedModulePullbackComparisonAt v 0 F)) =
      derivedSquareUnitMap f k g v h F ((Scheme.Modules.tensorPullback v).obj F)
        ((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction v)).unit.app F) := by
  dsimp only [Scheme.Modules, Scheme.ringCatSheaf] at *
  let : ∀ {Y Y' : Scheme.{u}} (a : Y ⟶ Y'),
      (Scheme.Modules.tensorPullback a).Additive :=
    fun a ↦ Scheme.Modules.canonicalTensorPullbackAdditive.{u, w} a
  let s := pinnedPullbackComposition k g ≪≫
    eqToIso (congrArg (fun a ↦ derivedPullback a) h.symm) ≪≫
      (pinnedPullbackComposition v f).symm
  have hs := square_transpose (pinnedDerivedAdjunction f) (pinnedDerivedAdjunction g)
    (pinnedDerivedAdjunction v) (pinnedDerivedAdjunction k) s
    ((DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj F)
    ((DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) 0).obj
        ((Scheme.Modules.tensorPullback v).obj F)) (pinnedModulePullbackComparisonAt v 0 F)
  have hbc : schemeDerivedBaseChangeMap f k g v h
      ((DerivedCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj F) =
      (pinnedDerivedAdjunction k).homEquiv _ _
        (s.hom.app _ ≫ (derivedPullback v).map
          ((pinnedDerivedAdjunction f).counit.app _)) := by
    simp only [schemeDerivedBaseChangeMap, s, pinnedDerivedAdjunction,
      pinnedPullbackCounit, pinnedPullbackComposition, Iso.trans_hom, Iso.symm_hom,
      NatTrans.comp_app, eqToIso.hom, eqToHom_app, Category.assoc, Functor.id_obj]
  rw [hbc, ← (pinnedDerivedAdjunction k).homEquiv_naturality_right]
  rw [Category.assoc]
  exact hs.trans (congrArg (fun z ↦ (schemeDerivedDirectImage f).map z ≫
    (derivedSquareRightComparison f k g v h).hom.app _) (tensor_single_transpose v F))

end AlgebraicGeometry
