/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.GeneratingPullbackChartCore
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.Algebra.Homology.DerivedInternalHom
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed
public import Mathlib.Algebra.Homology.Monoidal
public import WeilConjectures.Algebra.Homology.HomComplex
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.Algebra.Homology.HomComplexUnitEvaluationIsIso
public import WeilConjectures.Algebra.Homology.HomComplexUnitEvaluationComm
public import WeilConjectures.Algebra.Homology.HomComplexComponents
public import WeilConjectures.Algebra.Homology.HomComplexUnitEvaluationNaturality
public import WeilConjectures.ProEtaleCoefficients.RingedStrictTowerHomotopyLimit
public import WeilConjectures.CategoryTheory.Ringed.RingedInternalHomExactRestrictionSupplement
public import Mathlib.Algebra.Homology.Double
public import Mathlib.CategoryTheory.Endomorphism
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.Algebra.Homology.Functor

/-! Transport of a finite ideal-generating list through core chart data.

Source: Stacks Project, sites-modules.tex, Tags 03D7, 04IE and 04J4;
algebraization.tex, Tag 0A0G.
(blueprint: lem-weil-pbc-generating-pullback-chart-generators).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory

private theorem sections_over_ext
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u}} (M : SheafOfModules.{u} R) (U : C)
    {s t : (M.over U).sections}
    (h : s.val (op (Over.mk (𝟙 U))) = t.val (op (Over.mk (𝟙 U)))) : s = t := by
  apply Subtype.ext
  funext V
  have hs := s.property (Over.homMk V.unop.hom :
    V.unop ⟶ Over.mk (𝟙 U)).op
  have ht := t.property (Over.homMk V.unop.hom :
    V.unop ⟶ Over.mk (𝟙 U)).op
  exact hs.symm.trans ((congrArg _ h).trans ht)

private theorem scalar_eq_of_value
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (O : Sheaf J CommRingCat.{u}) (U : C)
    (a : End (SheafOfModules.unit
      ((sheafCompose (J.over U) (forget₂ CommRingCat RingCat)).obj (O.over U))))
    (b : O.obj.obj (op U))
    (h : a.val.app (op (Over.mk (𝟙 U))) (1 : O.obj.obj (op U)) = b) :
    a = ringedKoszulScalar (O.over U) (ringedSliceSection O U b) := by
  apply (SheafOfModules.unitHomEquiv _).injective
  simp only [ringedKoszulScalar, Equiv.apply_symm_apply]
  apply sections_over_ext (SheafOfModules.unit
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)) U
  change a.val.app (op (Over.mk (𝟙 U))) (1 : O.obj.obj (op U)) =
    O.obj.map (𝟙 U).op b
  simpa using h

private theorem mapped_generator
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {R : Sheaf J RingCat.{u}} {S : Sheaf K RingCat.{u}}
    (F : SheafOfModules.{u} R ⥤ SheafOfModules.{u} S)
    [PreservesColimitsOfSize.{u, u} F]
    (η : SheafOfModules.unit S ≅ F.obj (SheafOfModules.unit R))
    (M : SheafOfModules.{u} R) (σ : M.GeneratingSections) (i : σ.I) :
    (σ.map F η).s i = (F.obj M).unitHomEquiv
      (η.hom ≫ F.map (M.unitHomEquiv.symm (σ.s i))) := by
  apply (SheafOfModules.unitHomEquiv _).symm.injective
  rw [Equiv.symm_apply_apply]
  change (SheafOfModules.unitHomEquiv _).symm
    (SheafOfModules.freeHomEquiv _ _ i) = _
  rw [SheafOfModules.unitHomEquiv_symm_freeHomEquiv_apply]
  dsimp only [SheafOfModules.GeneratingSections.mapFreeHom]
  rw [← Category.assoc, SheafOfModules.ιFree_mapFreeIso_hom, Category.assoc,
    ← Functor.map_comp, ← SheafOfModules.unitHomEquiv_symm_freeHomEquiv_apply]
  congr 2
  exact congrArg M.unitHomEquiv.symm
    (congrFun (M.freeHomEquiv.apply_symm_apply σ.s) i)

set_option maxHeartbeats 2000000 in
-- Evaluating the transported generators unfolds nested slice-module functors.
/-- Generator transport through an epic map compatible with ideal inclusions.
Source: Stacks Project, sites-modules.tex, Tags 03D7 and 04IE.
(blueprint: lem-weil-pbc-generating-pullback-chart-generators).

Proof: map the given generating sections through F, which preserves coproducts
and epis as a left adjoint, using its rank-one comparison. Push them through q.
Evaluate their images in the ring at the terminal slice object to define c.
A rank-one endomorphism on the slice is determined by its value on one there.
The square for q identifies the image of each generator with the transported
source scalar, proving the scalar equations as well as the generating property.
The argument applies without alteration to the empty generating family. -/
theorem exists_generating_pullback_chart_generators
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (RY : Sheaf J CommRingCat.{u}) (RX : Sheaf K CommRingCat.{u})
    (G : ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj RY) ⥤
      ringedSiteModules.{u} ((sheafCompose K (forget₂ CommRingCat RingCat)).obj RX))
    (u : G.obj (SheafOfModules.unit
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj RY)) ≅
      SheafOfModules.unit ((sheafCompose K (forget₂ CommRingCat RingCat)).obj RX))
    (core : PullbackCechChartCore RY RX G u)
    (IY : ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj RY))
    (ιY : IY ⟶ SheafOfModules.unit
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj RY))
    (IX : ringedSiteModules.{u}
      ((sheafCompose K (forget₂ CommRingCat RingCat)).obj RX))
    (ιX : IX ⟶ SheafOfModules.unit
      ((sheafCompose K (forget₂ CommRingCat RingCat)).obj RX))
    (q : core.F.obj (IY.over core.V) ⟶ IX.over core.U) [Epi q]
    (hq : q ≫ ιX.over core.U = core.F.map (ιY.over core.V) ≫ core.ringIso.hom)
    (hb : IsRingedIdealGeneratingList RY IY ιY core.V core.r core.b) :
    ∃ c : Fin core.r → RX.obj.obj (op core.U),
      IsRingedIdealGeneratingList RX IX ιX core.U core.r c ∧
      ∀ i : Fin core.r,
        core.F.map (ringedKoszulScalar (RY.over core.V)
          (ringedSliceSection RY core.V (core.b i))) ≫ core.ringIso.hom =
          core.ringIso.hom ≫ ringedKoszulScalar (RX.over core.U)
            (ringedSliceSection RX core.U (c i)) := by
  classical
  let F := core.F
  let : PreservesColimitsOfSize.{u, u} F := core.adjunction.leftAdjoint_preservesColimits
  obtain ⟨σ, e, he⟩ := hb
  let τ := (σ.map F core.ringIso.symm).ofEpi q
  let c (i : Fin core.r) : RX.obj.obj (op core.U) :=
    (SheafOfModules.sectionsMap (ιX.over core.U) (τ.s (e.symm i))).val
      (op (Over.mk (𝟙 core.U)))
  refine ⟨c, ⟨τ, e, ?_⟩, ?_⟩
  · intro i
    dsimp only [c]
    exact congrArg (fun j : σ.I ↦
      (SheafOfModules.sectionsMap (ιX.over core.U) (τ.s j)).val
        (op (Over.mk (𝟙 core.U)))) (e.symm_apply_apply i).symm
  · intro i
    let a := (IY.over core.V).unitHomEquiv.symm (σ.s (e.symm i))
    have ha : a ≫ ιY.over core.V = ringedKoszulScalar (RY.over core.V)
        (ringedSliceSection RY core.V (core.b i)) := by
      apply scalar_eq_of_value RY core.V
      change (SheafOfModules.sectionsMap (ιY.over core.V)
        ((IY.over core.V).unitHomEquiv a)).val _ = _
      rw [Equiv.apply_symm_apply]
      simpa using he (e.symm i)
    have hc : core.ringIso.inv ≫ F.map a ≫ q ≫ ιX.over core.U =
        ringedKoszulScalar (RX.over core.U) (ringedSliceSection RX core.U (c i)) := by
      apply scalar_eq_of_value RX core.U
      change (core.ringIso.inv ≫ F.map a ≫ q ≫ ιX.over core.U).val.app
          (op (Over.mk (𝟙 core.U))) (1 : RX.obj.obj (op core.U)) =
        ιX.val.app (op core.U) (q.val.app (op (Over.mk (𝟙 core.U)))
          (((σ.map F core.ringIso.symm).s (e.symm i)).val
            (op (Over.mk (𝟙 core.U)))))
      erw [mapped_generator]
      rfl
    calc
      F.map (ringedKoszulScalar (RY.over core.V)
          (ringedSliceSection RY core.V (core.b i))) ≫ core.ringIso.hom =
          F.map a ≫ q ≫ ιX.over core.U := by
            rw [← ha, Functor.map_comp, Category.assoc, ← hq]
      _ = core.ringIso.hom ≫ ringedKoszulScalar (RX.over core.U)
          (ringedSliceSection RX core.U (c i)) := by
            rw [← hc]
            simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]

end CategoryTheory
