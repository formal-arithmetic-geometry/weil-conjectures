/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PerfectHomContinuityOn
public import Mathlib.Algebra.Category.Grp.Preadditive
public import Mathlib.Algebra.Homology.ExactSequence

import WeilConjectures.AlgebraicGeometry.PerfectHomStageColimit
import WeilConjectures.AlgebraicGeometry.PerfectHomMayerVietorisLocalRows
import Mathlib.CategoryTheory.ConcreteCategory.EpiMono

/-! # The five-term comparison diagram for perfect Hom continuity

## References

* Stacks Project, Tags 09RE and 08BW.
-/

@[expose] public section

universe u w
open CategoryTheory CategoryTheory.Limits TopologicalSpace
namespace AlgebraicGeometry

/-- The exact comparison diagram for perfect Hom continuity, without asserting invertibility
of its middle map. The four adjacent comparisons are invertible by open-local continuity
(Stacks, Tags 09RE and 08BW). -/
theorem perfect_hom_mayerVietoris_comparison
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (R : I ⥤ CommRingCat.{u}) (c : Cocone R)
    (i : I) (X : Scheme.{u}) (s₀ : X ⟶ Spec (R.obj i))
    [LocallyOfFinitePresentation s₀] [QuasiCompact s₀] [QuasiSeparated s₀]
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    (U V : X.Opens) (hU : IsCompact (U : Set X)) (hV : IsAffineOpen V)
    (hcontU : PerfectHomContinuityOn R c i X s₀ U)
    (hcontV : PerfectHomContinuityOn R c i X s₀ V)
    (hcontUV : PerfectHomContinuityOn R c i X s₀ (U ⊓ V))
    (Y : Scheme.{u}) (t : Y ⟶ X) [IsOpenImmersion t]
    (ht : t.opensRange = U ⊔ V)
    (s : Y ⟶ Spec (R.obj i)) (hs : s = t ≫ s₀)
    [LocallyOfFinitePresentation s] [QuasiCompact s] [QuasiSeparated s]
    [∀ W : Y.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings Y.toRingedSpace).over W))]
    (P Q : schemeDerivedCategory Y) (hP : Y.IsPerfect P) (hQ : Y.IsPerfect Q) :
    ∃ (H : Set.Ici i ⥤ Type (max u w)) (d : Cocone H),
      Nonempty (IsColimit d) ∧
      ∃ (ident : ∀ j : Set.Ici i, H.obj j ≃
          ((derivedPullback (pullback.fst s (Spec.map (R.map (homOfLE j.property))))).obj P ⟶
           (derivedPullback (pullback.fst s (Spec.map (R.map (homOfLE j.property))))).obj Q)),
        (∀ (j k : Set.Ici i) (hjk : j ≤ k) (f : H.obj j),
          ident k (H.map (homOfLE hjk) f) =
            perfectStageMap R s j.property hjk (ident j f)) ∧
        ∃ (A B : ComposableArrows AddCommGrpCat.{max u w} 4) (φ : A ⟶ B)
          (a : d.pt ≃ A.obj' 2)
          (b : B.obj' 2 ≃
            ((derivedPullback (pullback.fst s (Spec.map (c.ι.app i)))).obj P ⟶
             (derivedPullback (pullback.fst s (Spec.map (c.ι.app i)))).obj Q)),
          A.Exact ∧ B.Exact ∧
          IsIso (ComposableArrows.app' φ 0) ∧ IsIso (ComposableArrows.app' φ 1) ∧
          IsIso (ComposableArrows.app' φ 3) ∧ IsIso (ComposableArrows.app' φ 4) ∧
          ∀ (j : Set.Ici i) (f : H.obj j),
            b ((ComposableArrows.app' φ 2) (a (d.ι.app j f))) =
              perfectLimitMap R c s j.property (ident j f) := by
  obtain ⟨H, d, ⟨hd⟩, ident, htransition⟩ := perfect_hom_stage_colimit R i Y s P Q
  obtain ⟨A, B, φ, a, b, hA, hB, h0, h1, h3, h4, hpin⟩ :=
    perfect_hom_mayerVietoris_local_rows R c i X s₀ U V hU hV
      Y t ht s hs P Q hP hQ H d hd ident htransition
  have hbij {α β : Type (max u w)} {m : α → β}
      (hm : PerfectHomLocalMap R c i X s₀ U V m) : Function.Bijective m :=
    PerfectHomLocalMap.bijective R c i X s₀ U V hm hcontU hcontV hcontUV
  refine ⟨H, d, ⟨hd⟩, ident, htransition, A, B, φ, a, b, hA, hB, ?_, ?_, ?_, ?_, hpin⟩
  · exact (ConcreteCategory.isIso_iff_bijective _).2 (hbij h0)
  · exact (ConcreteCategory.isIso_iff_bijective _).2 (hbij h1)
  · exact (ConcreteCategory.isIso_iff_bijective _).2 (hbij h3)
  · exact (ConcreteCategory.isIso_iff_bijective _).2 (hbij h4)

end AlgebraicGeometry
