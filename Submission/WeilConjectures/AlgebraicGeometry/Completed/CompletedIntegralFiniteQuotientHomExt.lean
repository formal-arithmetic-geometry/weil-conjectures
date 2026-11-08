/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Submission.WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
public import Submission.WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientGerm
import Submission.WeilConjectures.AlgebraicGeometry.Completed.CompletedIntegralProjectionDivisibility

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-! # Uniqueness of normalized maps from completed coefficients to a finite quotient

Source: the finite-quotient uniqueness argument in the coefficient-tower comparison,
blueprint main-20261015, sk-def-sp-coefficient-towers.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe t u w v
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale
open WeilConjectures

private theorem constRing_surj {C : Type w} [Category.{v} C]
    (J : GrothendieckTopology C) [HasSheafify J CommRingCat.{u}]
    [HasSheafify J (Type u)] [J.PreservesSheafification (forget CommRingCat.{u})]
    [J.HasSheafCompose (forget CommRingCat.{u})]
    {A B : CommRingCat.{u}} (f : A ⟶ B) (hf : Function.Surjective f)
    (U : Cᵒᵖ) :
    Function.Surjective (((constantSheaf J CommRingCat.{u}).map f).hom.app U) := by
  classical
  let e := constantCommuteCompose J (forget CommRingCat.{u})
  let s' := (constantSheaf J (Type u)).map (TypeCat.ofHom (Function.surjInv hf))
  have hs : s' ≫ (constantSheaf J (Type u)).map ((forget _).map f) = 𝟙 _ := by
    rw [← Functor.map_comp]
    trans (constantSheaf J (Type u)).map (𝟙 ((forget CommRingCat.{u}).obj B))
    · congr 1
      ext x
      exact Function.surjInv_eq hf x
    exact (constantSheaf J (Type u)).map_id _
  let r := e.hom.app B ≫ s' ≫ e.inv.app A
  have hr : r ≫ (sheafCompose J (forget CommRingCat.{u})).map
      ((constantSheaf J CommRingCat.{u}).map f) = 𝟙 _ := by
    dsimp only [r]
    rw [Category.assoc, Category.assoc]
    change e.hom.app B ≫ s' ≫ e.inv.app A ≫
      (constantSheaf J CommRingCat.{u} ⋙ sheafCompose J (forget CommRingCat.{u})).map f = _
    rw [← e.inv.naturality f]
    change e.hom.app B ≫ s' ≫
      (constantSheaf J (Type u)).map ((forget _).map f) ≫ e.inv.app B = _
    rw [← Category.assoc s', hs, Category.id_comp, e.hom_inv_id_app B]
  intro x
  refine ⟨r.hom.app U x, ?_⟩
  exact congrArg (fun h ↦ h.hom.app U x) hr

private theorem constantQuotient_surjective (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (T : AlgebraicGeometry.Scheme.{t})
    (n : ℕ) (U : T.ProEtᵒᵖ) :
    Function.Surjective
      ((WeilConjectures.integralConstantQuotientOfUniverses l E T n).hom.app U) := by
  have : LocallySmall.{max u (t + 1)} T.ProEt := locallySmall_max.{max u (t + 1), t, t + 1}
  have : HasColimitsOfSize.{t + 1, t + 1} CommRingCat.{max u (t + 1)} :=
    hasColimitsOfSizeShrink.{t + 1, t + 1, max u (t + 1), max u (t + 1)} _
  have : PreservesFilteredColimitsOfSize.{t + 1, t + 1} (forget CommRingCat.{max u (t + 1)}) :=
    preservesFilteredColimitsOfSize_shrink.{t + 1, max u (t + 1), t + 1, max u (t + 1)} _
  have : (AlgebraicGeometry.Scheme.ProEt.topology T).PreservesSheafification
      (forget CommRingCat.{max u (t + 1)}) :=
    GrothendieckTopology.instPreservesSheafification _ _
  apply constRing_surj.{max u (t + 1), t + 1, t}
  intro b
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective b.down
  refine ⟨ULift.up a, ?_⟩
  apply ULift.ext
  exact ha

end AlgebraicGeometry.ProEtale
