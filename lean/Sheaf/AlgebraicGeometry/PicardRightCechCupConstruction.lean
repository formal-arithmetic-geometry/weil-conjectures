/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R1
-/
module

public import Sheaf.AlgebraicGeometry.PicardExternalRightCechModels
public import Sheaf.Paper.CechCupProduct
public import Sheaf.AlgebraicGeometry.TensorPullbackAdjunction

/-! # The right external Cech cup construction

Source: Stacks Project, Varieties, Tag 0BED; Cohomology, Tags 01FD and 07MB.
(blueprint: lem-sc-picard-right-cech-cup-construction).
-/

@[expose] public section

universe w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped TensorProduct
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section
variable {k : Type w} [Field k] {X Y : Scheme.{w}}

/-- Pull a section to a smaller open using the canonical tensor-pullback unit.
Source: Stacks, Tag 01FD
(blueprint: lem-sc-picard-right-cech-cup-construction). -/
def picardCechPullSection {A B : Scheme.{w}} (a : A ⟶ B) (M : B.Modules)
    (Q : B.Opens) (W : A.Opens) (h : W ≤ a ⁻¹ᵁ Q) (s : Γ(M, Q)) :
    Γ((tensorPullback a).obj M, W) :=
  ((tensorPullback a).obj M).presheaf.map (homOfLE h).op
    (((Classical.choose (exists_tensorPullbackAdjunction a)).unit.app M).val.app (op Q) s)

/-- The product intersection lies in the pullback of either selected face intersection.
Source: Stacks, Tag 01FD
(blueprint: lem-sc-picard-right-cech-cup-construction). -/
theorem picardProductCechFace {ι κ : Type w}
    (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k))
    (U : ι → X.Opens) (V : κ → Y.Opens) {m n : ℕ}
    (y : Fin n → ι × κ) (face : Fin m → Fin n) :
    (⨅ l, pullback.fst f g ⁻¹ᵁ U (y l).1 ⊓ pullback.snd f g ⁻¹ᵁ V (y l).2) ≤
      pullback.fst f g ⁻¹ᵁ (⨅ l, U (y (face l)).1) ∧
    (⨅ l, pullback.fst f g ⁻¹ᵁ U (y l).1 ⊓ pullback.snd f g ⁻¹ᵁ V (y l).2) ≤
      pullback.snd f g ⁻¹ᵁ (⨅ l, V (y (face l)).2) := by
  constructor <;> intro x hx
  · change (pullback.fst f g).base x ∈ ⨅ l, U (y (face l)).1
    rw [← SetLike.mem_coe, TopologicalSpace.Opens.coe_iInf, Set.mem_iInter]
    intro l
    exact (iInf_le (fun j ↦ pullback.fst f g ⁻¹ᵁ U (y j).1 ⊓
      pullback.snd f g ⁻¹ᵁ V (y j).2) (face l) hx).1
  · change (pullback.snd f g).base x ∈ ⨅ l, V (y (face l)).2
    rw [← SetLike.mem_coe, TopologicalSpace.Opens.coe_iInf, Set.mem_iInter]
    intro l
    exact (iInf_le (fun j ↦ pullback.fst f g ⁻¹ᵁ U (y j).1 ⊓
      pullback.snd f g ⁻¹ᵁ V (y j).2) (face l) hx).2

/-- A right Cech transformation has the Alexander--Whitney external cup coordinates.
This is a cochain formula, with no cohomology comparison or exactness assumption.
Source: Stacks, Tags 01FD, 07MB and equation-kunneth-on-cech of 0BED
(blueprint: lem-sc-picard-right-cech-cup-construction). -/
def IsPicardRightCechCup
    (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k))
    {ι κ : Type w} (U : ι → X.Opens) (V : κ → Y.Opens) (F : X.Modules)
    (θ : picardRightTensorCechFunctor f g U V F ⟶
      picardRightProductCechFunctor f g U V F) : Prop :=
  ∀ G : Y.Modules,
    ∃ c : HomologicalComplex.mapBifunctor ((picardCechFunctor f U).obj F)
        ((picardCechFunctor g V).obj G) (curriedTensor (ModuleCat.{w} k))
          (ComplexShape.up ℕ) ⟶
      (picardCechFunctor (pullback.fst f g ≫ f)
        (fun ij : ι × κ ↦ pullback.fst f g ⁻¹ᵁ U ij.1 ⊓
          pullback.snd f g ⁻¹ᵁ V ij.2)).obj (externalCupCoefficients f g F G),
      θ.app G = HomologicalComplex.extendMap c ComplexShape.embeddingUpNat ∧
      ∀ (p q : ℕ) (a : ((picardCechFunctor f U).obj F).X p)
        (b : ((picardCechFunctor g V).obj G).X q) (y : Fin (p + q + 1) → ι × κ),
        TopCat.Presheaf.cechComplexFunctorXAddEquiv
          (fun ij : ι × κ ↦ pullback.fst f g ⁻¹ᵁ U ij.1 ⊓
            pullback.snd f g ⁻¹ᵁ V ij.2)
          (scalarPresheaf (pullback.fst f g ≫ f) (externalCupCoefficients f g F G))
          (p + q) (c.f (p + q)
            (HomologicalComplex.ιMapBifunctor ((picardCechFunctor f U).obj F)
              ((picardCechFunctor g V).obj G) (curriedTensor (ModuleCat.{w} k))
                (ComplexShape.up ℕ) p q (p + q) rfl (a ⊗ₜ[k] b))) y =
          tmulSection
            (picardCechPullSection (pullback.fst f g) F
              (⨅ l, U (y (cupFront p q l)).1) _
              (picardProductCechFace f g U V y (cupFront p q)).1
              (TopCat.Presheaf.cechComplexFunctorXAddEquiv U (scalarPresheaf f F) p a
                (fun l ↦ (y (cupFront p q l)).1)))
            (picardCechPullSection (pullback.snd f g) G
              (⨅ l, V (y (cupBack p q l)).2) _
              (picardProductCechFace f g U V y (cupBack p q)).2
              (TopCat.Presheaf.cechComplexFunctorXAddEquiv V (scalarPresheaf g G) q b
                (fun l ↦ (y (cupBack p q l)).2)))

/-- The external Alexander--Whitney cup is natural in the right coefficient.
Source: Stacks, Tags 01FD, 07MB and 0BED, equation-kunneth-on-cech.
(blueprint: lem-sc-picard-right-cech-cup-construction).

Proof: For each pair of degrees, pull the front-face section from X and the
back-face section from Y to their common product intersection, and apply the
canonical tensor-section pairing. These maps are k-bilinear since both projections
are over Spec k. The product universal property and the tensor universal property
give the degree components on each summand of the tensor total. Expand the Cech
differential as an alternating sum. The front and back omitted vertices give the
two terms of the Leibniz identity; the shared vertex terms cancel, with the back
term sign (-1)^p. Hence the components define c. Adjunction-unit naturality,
restriction naturality and tensor-section naturality give coefficient naturality
on each tuple and pure tensor, hence on every total term. Extend by zero to get θ.
The same computation proves the displayed formula. This works for arbitrary
covers and coefficients, including empty covers and zero modules. -/
theorem picardRightCechCup_exists
    (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k))
    {ι κ : Type w} (U : ι → X.Opens) (V : κ → Y.Opens) (F : X.Modules) :
    ∃ θ : picardRightTensorCechFunctor f g U V F ⟶
      picardRightProductCechFunctor f g U V F, IsPicardRightCechCup f g U V F θ := by sorry

end
end AlgebraicGeometry.Scheme.Modules
