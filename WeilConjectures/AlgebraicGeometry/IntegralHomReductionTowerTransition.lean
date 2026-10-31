/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.IntegralHomReductionModels
import WeilConjectures.AlgebraicGeometry.SignedHomTensorComparison
import WeilConjectures.AlgebraicGeometry.IntegralHomReductionTowerTensorModels

/-! # Transition compatibility for integral Hom reduction towers

Source: blueprint order 2478, proof steps 4-8; Stacks Tags 07A6, 08J9 and 08TC
(blueprint: lem-sf-integral-hom-tower-components-transition).

The finite signed comparison is natural for the consecutive quotient maps. This
intermediate statement isolates that transition part of the component-comparison
argument; the augmentation equation is recorded separately.
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe d t u

open CategoryTheory CategoryTheory.Limits Opposite

namespace WeilConjectures.IntegralHom

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (Y : AlgebraicGeometry.Scheme.{t}) (D : FiniteFieldDatum.{d}) (hl : l ≠ D.p)

/--
The normalized finite Hom comparison admits components compatible with every
consecutive transition in the integral reduction towers. This is the transition
part of `reductionTower_components`; the component construction and its proof are
exactly the naturality calculation on the two-term quotient complexes described
in Stacks Tags 07A6, 08J9 and 08TC.

Source: blueprint order 2478, proof steps 4-8; Stacks Tags 07A6, 08J9 and 08TC
(blueprint: lem-sf-integral-hom-tower-components-transition).

Proof: use separate tensor representatives A,I and the common two-term free
coefficient tower Q. Whisker the natural signed tensor--Hom map by Q and by
localization. Its component in every cochain degree is invertible by the
existing two-term free component lemma, so its complex components and then
its localized natural transformation are isomorphisms. Invert that natural
isomorphism and conjugate by the two model isomorphisms. Its naturality at
the consecutive quotient map is exactly the displayed transition square.
-/
theorem reductionTower_components_transition
    (K : completedIntegralDerivedCategory l E Y D hl)
    (P G P' G' : CochainComplex (completedIntegralModuleSheaves l E Y D hl) ℤ)
    (q : P ⟶ G) (q' : P' ⟶ G')
    (hq : CochainComplex.IsKFlatResolutionIndependentCoefficients
      (J := AlgebraicGeometry.Scheme.ProEt.topology Y)
      (R := completedIntegralCommRingSheaf l E Y D hl) q)
    (hq' : CochainComplex.IsKFlatResolutionIndependentCoefficients
      (J := AlgebraicGeometry.Scheme.ProEt.topology Y)
      (R := completedIntegralCommRingSheaf l E Y D hl) q')
    (e : DerivedCategory.Q.obj G' ≅
      (hom.{t, u} Y (completedIntegralCommRingSheaf l E Y D hl)).obj
        (op K, DerivedCategory.Q.obj G)) :
    let H := (Functor.curry.obj
      (hom.{t, u} Y (completedIntegralCommRingSheaf l E Y D hl))).obj (op K)
    ∃ θ : ∀ n : ℕ, H.obj ((integralReductionTower l E Y D hl P).obj (op n)) ≅
        (integralReductionTower l E Y D hl P').obj (op n),
      ∀ n : ℕ,
        H.map ((integralReductionTower l E Y D hl P).map (homOfLE n.le_succ).op) ≫
            (θ n).hom =
          (θ (n + 1)).hom ≫
            (integralReductionTower l E Y D hl P').map (homOfLE n.le_succ).op := by
  obtain ⟨A, I, Q, hQ, ⟨s⟩, ⟨t⟩⟩ :=
    reductionTower_tensor_models l E Y D hl K P G P' G' q q' hq hq' e
  obtain ⟨α, hα⟩ := signedHomTensorComparison_exists Y
    (completedIntegralCommRingSheaf l E Y D hl) A I
  let β := Functor.whiskerRight (Functor.whiskerLeft Q α) DerivedCategory.Q
  have (n : ℕᵒᵖ) : IsIso (β.app n) := by
    obtain ⟨hz, ⟨eNeg⟩, ⟨eZero⟩⟩ := hQ n.unop
    have (j : ℤ) : IsIso ((α.app (Q.obj n)).f j) :=
      twoTermFreeHomTensor_component_isIso Y _ A I (Q.obj n)
        hz eNeg eZero (α.app (Q.obj n)) (hα (Q.obj n)) j
    have : IsIso (α.app (Q.obj n)) :=
      HomologicalComplex.Hom.isIso_of_components _
    change IsIso (DerivedCategory.Q.map (α.app (Q.obj n)))
    infer_instance
  have : IsIso β := NatIso.isIso_of_isIso_app β
  let τ := s ≪≫ (asIso β).symm ≪≫ t.symm
  refine ⟨fun n ↦ τ.app (op n), ?_⟩
  intro n
  exact τ.hom.naturality (homOfLE n.le_succ).op

end WeilConjectures.IntegralHom
