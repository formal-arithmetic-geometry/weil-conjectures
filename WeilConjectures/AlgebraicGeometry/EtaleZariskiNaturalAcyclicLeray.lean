/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.AlgebraicGeometry.Sites.AffineEtale
public import WeilConjectures.Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.CategoryTheory.Sites.CohomologyRightDerivedSections
import WeilConjectures.AlgebraicGeometry.EtaleCohomologyNaturalDerivedEvaluation
import WeilConjectures.AlgebraicGeometry.EtaleZariskiDerivedSectionsAcyclicLeray

/-! # Natural acyclic Leray with two Ext models

Source: Stacks Project, Tags 03DW, 03P2 and 0733.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

set_option autoImplicit false

set_option linter.unusedVariables false in
/-- Natural mixed-universe Leray comparison on the subcategory of acyclic abelian
sheaves. No quasi-coherent module or tensor-sections construction is assumed
(Stacks, Tags 0733, 072Z, 0730 and 06XP). -/
theorem etaleZariskiNaturalAcyclicLeray
    (X : Scheme.{u}) (i : X.Opens ⥤ X.Etale)
    [i.IsContinuous (Opens.grothendieckTopology X.carrier) X.smallEtaleTopology]
    [(i.sheafPushforwardContinuous AddCommGrpCat.{u}
      (Opens.grothendieckTopology X.carrier) X.smallEtaleTopology).Additive]
    [PreservesFiniteLimits i] (hterminal : IsTerminal (i.obj ⊤))
    [HasExt.{u} (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})] :
    let T := i.sheafPushforwardContinuous AddCommGrpCat.{u}
      (Opens.grothendieckTopology X.carrier) X.smallEtaleTopology
    ∃ b : ∀ (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
        (hF : ∀ n : ℕ, IsZero ((T.rightDerived (n + 1)).obj F)) (n : ℕ),
        Sheaf.H' (T.obj F) (n + 1) (⊤ : X.Opens) ≃+
          @Sheaf.H _ _ X.smallEtaleTopology F inferInstance (HasExt.standard _) (n + 1),
      ∀ (F G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
        (hF : ∀ n : ℕ, IsZero ((T.rightDerived (n + 1)).obj F))
        (hG : ∀ n : ℕ, IsZero ((T.rightDerived (n + 1)).obj G))
        (φ : F ⟶ G) (n : ℕ) (x : Sheaf.H' (T.obj F) (n + 1) (⊤ : X.Opens)),
        b G hG n (((Sheaf.cohomologyPresheafFunctor
          (Opens.grothendieckTopology X.carrier) (n + 1)).map (T.map φ)).app (op ⊤) x) =
          @Sheaf.H.map _ _ X.smallEtaleTopology inferInstance (HasExt.standard _)
            _ _ φ (n + 1) (b F hF n x) := by
  classical
  dsimp
  let T := i.sheafPushforwardContinuous AddCommGrpCat.{u}
    (Opens.grothendieckTopology X.carrier) X.smallEtaleTopology
  let Z := sheafToPresheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u} ⋙
    (CategoryTheory.evaluation X.Opensᵒᵖ AddCommGrpCat.{u}).obj (op ⊤)
  obtain ⟨c, hc⟩ := etaleZariskiDerivedSectionsAcyclicLeray X i
  obtain ⟨e, he⟩ := etaleCohomologyNaturalDerivedEvaluation X (i.obj ⊤) hterminal
  let z (n : ℕ) := Classical.choice (
    Sheaf.nonempty_cohomologyPresheafFunctor_eval_iso_rightDerived
      (Opens.grothendieckTopology X.carrier) (⊤ : X.Opens) (n + 1))
  let a (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (n : ℕ) :=
    ((z n).app (T.obj F)).addCommGroupIsoToAddEquiv
  refine ⟨(fun F hF n => (a F n).trans ((c F hF n).trans (e F n).symm)), ?_⟩
  intro F G hF hG φ n x
  apply (e G n).injective
  simp only [AddEquiv.trans_apply, AddEquiv.apply_symm_apply]
  rw [he]
  have hz : a G n (((Sheaf.cohomologyPresheafFunctor
      (Opens.grothendieckTopology X.carrier) (n + 1)).map (T.map φ)).app (op ⊤) x) =
      (Z.rightDerived (n + 1)).map (T.map φ) (a F n x) := by
    exact ConcreteCategory.congr_hom ((z n).hom.naturality (T.map φ)) x
  simp only [AddEquiv.apply_symm_apply]
  exact (congrArg (c G hG n) hz).trans (hc F G hF hG φ n (a F n x))

end AlgebraicGeometry.Scheme.Modules
