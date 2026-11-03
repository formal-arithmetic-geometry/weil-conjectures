/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.FrobeniusCoefficientTwists.FrobeniusCoefficientTwistsCanonical
import all WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficientTwistsSupplement
import WeilConjectures.AlgebraicGeometry.Pur.PurTwistIntegralLocalModels
import WeilConjectures.SixFunctors.Supporting.FirstRootLinePullback
import WeilConjectures.SmoothPurity.Integral.IntegralRootPowerGenerators

/-! # Extensionality on positive root generators

Source: coefficient-twist conventions, first-line inverse image and scalar extension.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

section PositiveRootLineConstruction

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local irreducible] proEtaleRingModulePullback proEtaleRingModuleAdjunction
  completedIntegralCoefficientSheafUnrestricted
attribute [local implicit_reducible] PurCompactSupport.completed
  completedIntegralCommRingSheafUnrestricted

end PositiveRootLineConstruction

end WeilConjectures

namespace WeilConjectures

/-- A narrow cover interface for the first root line, avoiding the unrelated derived
clauses in the full local-freeness theorem. -/
private theorem sfIntegralRootLine_cover
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (S : Scheme.{u})
    [∀ x : S, Invertible (l : S.residueField x)] :
    ∃ (I : Type (u + 1)) (V : I → S.ProEt),
      (ProEt.topology S).CoversTop V ∧
      ∀ i, Nonempty ((purTwistIntegralModule S l E).over (V i) ≅
        SheafOfModules.unit ((completedIntegralCoefficientSheafUnrestricted l E S).over
          (V i))) := by
  have hz := (pur_twist_sheaf_locally_free.{u, u} S l E).2.1.2.1
  obtain ⟨I, V, v, hc, hv⟩ := (purTwistIntegralLocalModels S l E hz).1
  exact ⟨I, V, AlgebraicGeometry.ProEtale.commonCover_coversTop S V v hc, hv⟩

/-- Construct every positive comparison from the normalized first line. The signed
comparison gives all powers; its zero and positive equations prove the generator
formula by two-step induction. Source: coefficient-twist conventions and the
Powers and duals paragraph of the cartesian-coefficients proof.
(blueprint: def-sf-orientation-integral-line-comparisons). -/
private theorem sfIntegralPositiveRootLineMaps_exists
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] {X Y : Scheme.{u}} (g : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)] :
    ∃ tau : ∀ d : ℕ,
      (FrobeniusCoefficientTwists.modulePull l E g).obj
        (FrobeniusCoefficientTwists.positiveLine l E Y d) ≅
          FrobeniusCoefficientTwists.positiveLine l E X d,
      ∀ (d : ℕ) (V : Y.ProEt)
        (a : (completedIntegralCoefficientSheafUnrestricted l E Y).obj.obj
          (Opposite.op V)) (x : Fin d → (purTwistZlOne Y l).obj.obj (Opposite.op V)),
        (tau d).hom.val.app (Opposite.op ((proEtaleBaseChange g).obj V))
          (FrobeniusCoefficientTwists.moduleSection l E g
            (FrobeniusCoefficientTwists.positiveLine l E Y d) V
            (FrobeniusCoefficientTwists.generator l E Y (Opposite.op V) a d x)) =
        FrobeniusCoefficientTwists.generator l E X
          (Opposite.op ((proEtaleBaseChange g).obj V))
          ((sfCompletedCoefficientMap l E g).hom.app (Opposite.op V) a) d
          (fun i ↦ FrobeniusCoefficientTwists.rootSection l g V (x i)) := by
  obtain ⟨t, ht⟩ := sfFirstRootLinePullback_exists l E g
  obtain ⟨β, hβ⟩ := AlgebraicGeometry.ProEtale.signedComparison_exists g
    ((PurCompactSupport.completed l E).ring Y)
    ((PurCompactSupport.completed l E).ring X)
    ((PurCompactSupport.completed l E).pull g)
    (purTwistIntegralModule Y l E) (purTwistIntegralModule X l E) t
    (sfIntegralRootLine_cover l E Y) (sfIntegralRootLine_cover l E X)
  have hcoeff (V : Y.ProEt)
      (a : (completedIntegralCoefficientSheafUnrestricted l E Y).obj.obj
        (Opposite.op V)) :
      (proEtaleRingDirectImageMap g
        ((PurCompactSupport.completed l E).ring Y)
        ((PurCompactSupport.completed l E).ring X)
        ((PurCompactSupport.completed l E).pull g)).hom.app (Opposite.op V) a =
          (sfCompletedCoefficientMap l E g).hom.app (Opposite.op V) a := by
    exact congrArg (fun k ↦ k.hom.app (Opposite.op V) a)
      (((proEtaleSheafAdjunction g CommRingCat.{u + 1}).homEquiv _ _).apply_symm_apply
        (sfCompletedCoefficientMap l E g))
  let τ : ∀ d : ℕ,
      (FrobeniusCoefficientTwists.modulePull l E g).obj
        (FrobeniusCoefficientTwists.positiveLine l E Y d) ≅
          FrobeniusCoefficientTwists.positiveLine l E X d := fun d ↦ β.signed (d : ℤ)
  have hτ : ∀ (d : ℕ) (V : Y.ProEt)
      (a : (completedIntegralCoefficientSheafUnrestricted l E Y).obj.obj
        (Opposite.op V)) (x : Fin d → (purTwistZlOne Y l).obj.obj (Opposite.op V)),
      (τ d).hom.val.app (Opposite.op ((proEtaleBaseChange g).obj V))
        (FrobeniusCoefficientTwists.moduleSection l E g
          (FrobeniusCoefficientTwists.positiveLine l E Y d) V
          (FrobeniusCoefficientTwists.generator l E Y (Opposite.op V) a d x)) =
      FrobeniusCoefficientTwists.generator l E X
        (Opposite.op ((proEtaleBaseChange g).obj V))
        ((sfCompletedCoefficientMap l E g).hom.app (Opposite.op V) a) d
        (fun i ↦ FrobeniusCoefficientTwists.rootSection l g V (x i)) := by
    intro d
    induction d using Nat.twoStepInduction with
    | zero =>
      intro V a x
      exact (β.zero V a).trans (hcoeff V a)
    | one =>
      intro V a x
      change (β.signed 1).hom.val.app _ _ = _
      rw [hβ]
      exact ht V a x
    | more n _ ih =>
      intro V a x
      have hlast := ht V 1 (fun _ ↦ x (Fin.last (n + 1)))
      have hy := @one_smul
        ((completedIntegralCoefficientSheafUnrestricted l E Y).obj.obj (Opposite.op V))
        ((purTwistIntegralOne Y l E).val.obj (Opposite.op V)) _
        (purTwistIntegralAction Y l E (Opposite.op V)).toMulAction
        (purTwistIntegralTensor Y l E (Opposite.op V) 1 (x (Fin.last (n + 1))))
      have hx := @one_smul
        ((completedIntegralCoefficientSheafUnrestricted l E X).obj.obj
          (Opposite.op ((proEtaleBaseChange g).obj V)))
        ((purTwistIntegralOne X l E).val.obj
          (Opposite.op ((proEtaleBaseChange g).obj V))) _
        (purTwistIntegralAction X l E
          (Opposite.op ((proEtaleBaseChange g).obj V))).toMulAction
        (purTwistIntegralTensor X l E (Opposite.op ((proEtaleBaseChange g).obj V)) 1
          (FrobeniusCoefficientTwists.rootSection l g V (x (Fin.last (n + 1)))))
      simp only [FrobeniusCoefficientTwists.generator] at hlast
      have hc1 : (sfCompletedCoefficientMap l E g).hom.app (Opposite.op V) 1 = 1 :=
        ((sfCompletedCoefficientMap l E g).hom.app (Opposite.op V)).hom.map_one
      have hx' := congrArg
        (fun b ↦ @SMul.smul _ _
          (purTwistIntegralAction X l E
            (Opposite.op ((proEtaleBaseChange g).obj V))).toSMul b
          (purTwistIntegralTensor X l E (Opposite.op ((proEtaleBaseChange g).obj V)) 1
            (FrobeniusCoefficientTwists.rootSection l g V (x (Fin.last (n + 1)))))) hc1
      have hlast' := (congrArg
        (fun z ↦ t.hom.val.app (Opposite.op ((proEtaleBaseChange g).obj V))
          (FrobeniusCoefficientTwists.moduleSection l E g
            (purTwistIntegralModule Y l E) V z)) hy).symm.trans (hlast.trans (hx'.trans hx))
      have hb := congrArg
        (fun k : (FrobeniusCoefficientTwists.modulePull l E g).obj
            (purTwistIntegralModule Y l E) ⟶ purTwistIntegralModule X l E ↦
          k.val.app (Opposite.op ((proEtaleBaseChange g).obj V))
            (FrobeniusCoefficientTwists.moduleSection l E g
              (purTwistIntegralModule Y l E) V
              (purTwistIntegralTensor Y l E (Opposite.op V) 1
                (x (Fin.last (n + 1)))))) hβ
      refine (β.positive n V
        (purTwistIntegralTensor Y l E (Opposite.op V) 1 (x (Fin.last (n + 1))))
        (FrobeniusCoefficientTwists.generator l E Y (Opposite.op V) a (n + 1)
          (fun i ↦ x i.castSucc))).trans ?_
      exact congrArg₂
        (fun z w ↦ SheafOfModules.siteSheafTensorTmul
          (FrobeniusCoefficientTwists.positiveLine l E X (n + 1))
          (purTwistIntegralModule X l E)
          (Opposite.op ((proEtaleBaseChange g).obj V)) z w)
        (ih V a (fun i ↦ x i.castSucc)) (hb.trans hlast')
  exact ⟨τ, hτ⟩

/-- Maps from a positive completed root power are determined by local pure roots.
Source: `def-coefficient-twists-detailed`, positive tensor powers, and the
uniqueness argument of `def-sf-orientation`, coefficient-line comparisons.
(blueprint: lem-sf-positive-root-generator-ext).
Proof: at exponent zero the generator is any section of the scalar unit. At one,
forget to additive sheaves and use the scalar-extension sheafification adjunction.
Before sheafification the tensor is generated by b tensor x. Its image is the
completed scalar image of b times the image of one tensor x, by the defining
completed action. Thus the assumed formulas determine the map on every tensor.
For exponent n+2 use the ordinary tensor sheafification adjunction. Tensor
induction reduces equality to sections v tensor w. Apply the induction hypothesis
to the first variable and the exponent-one argument to the second variable.
The prescribed generator is exactly their ordered tensor, with the scalar in
the first factor. Equality before sheafification implies equality of sheaf maps.
These universal properties also cover the empty scheme; no global basis is used. -/
theorem sfPositiveRootGenerator_hom_ext
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (X : Scheme.{u}) (d : ℕ)
    {N : integralTowerModules l E X}
    {f g : FrobeniusCoefficientTwists.positiveLine l E X d ⟶ N}
    (h : ∀ (U : X.ProEtᵒᵖ)
      (a : (completedIntegralCoefficientSheafUnrestricted l E X).obj.obj U)
      (x : Fin d → (purTwistZlOne X l).obj.obj U),
      f.val.app U (FrobeniusCoefficientTwists.generator l E X U a d x) =
        g.val.app U (FrobeniusCoefficientTwists.generator l E X U a d x)) : f = g := by
  exact integralRootPower_hom_ext l E X
    (fun d U a x ↦ FrobeniusCoefficientTwists.generator l E X U a d x)
    (fun _ _ _ ↦ rfl) (fun _ _ _ ↦ rfl) (fun _ _ _ _ ↦ rfl) d N f g h

end WeilConjectures
