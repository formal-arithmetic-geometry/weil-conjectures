/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategoryBraided
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Braided

/-!
# Biduality of a perfect complex

Source: latest blueprint, part-duality-trace-formula/sec-lefschetz-verdier/
sec-kunneth-formulas-and-external-duality/sk-thm-sf-kunneth-verdier/
sk-prop-sf-dualizable-biduality/_section.md
(blueprint: sk-prop-sf-dualizable-biduality).

The ambient category is the ordinary unbounded derived category of internal modules over
`Λ_X = p_X^* Λ`. Perfectness uses the statement's explicit dualizability convention.
Evaluation is already `(derivedTensorHomAdjunction Λ K).counit.app (𝟙_ _)`, equivalently
`(ihom.ev K).app (𝟙_ _)`; it is not asserted to be invertible. Biduality uses the published
Koszul braiding, supplied explicitly rather than as an additional hypothesis.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory Limits MonoidalCategory Opposite
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- The coefficient dual `RHom_{Λ_X}(K, Λ_X)`.
Source: latest blueprint, part-duality-trace-formula/sec-lefschetz-verdier/
sec-kunneth-formulas-and-external-duality/sk-thm-sf-kunneth-verdier/
sk-prop-sf-dualizable-biduality/_section.md
(blueprint: sk-prop-sf-dualizable-biduality).
-/
noncomputable def coefficientDual
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u})
    (K : DerivedCategory (CategoryTheory.Mod
      (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))) :
    DerivedCategory (CategoryTheory.Mod
      (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :=
  ((derivedHom Λ X).obj (op K)).obj (𝟙_ _)

/-- The specified evaluation `K ⊗ᴸ K^∨ ⟶ Λ_X`, namely the counit of
`K ⊗ᴸ - ⊣ RHom_{Λ_X}(K, -)` at the coefficient unit.
Source: latest blueprint, part-duality-trace-formula/sec-lefschetz-verdier/
sec-kunneth-formulas-and-external-duality/sk-thm-sf-kunneth-verdier/
sk-prop-sf-dualizable-biduality/_section.md
(blueprint: sk-prop-sf-dualizable-biduality).
-/
noncomputable def coefficientDualEvaluation
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u})
    (K : DerivedCategory (CategoryTheory.Mod
      (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))) :
    ((derivedTensor Λ X).obj K).obj (coefficientDual Λ X K) ⟶ 𝟙_ _ :=
  (derivedTensorHomAdjunction Λ K).counit.app (𝟙_ _)

/-- The coefficient dual of a perfect complex is perfect; its canonical biduality and
its coefficient-dual tensor comparison with every unbounded target are isomorphisms.
The coefficient dual is `((derivedHom Λ X).obj (op K)).obj (𝟙_ _)`, and evaluation is the
counit at the coefficient unit of `derivedTensorHomAdjunction Λ K`.

Source: latest blueprint, part-duality-trace-formula/sec-lefschetz-verdier/
sec-kunneth-formulas-and-external-duality/sk-thm-sf-kunneth-verdier/
sk-prop-sf-dualizable-biduality/_section.md
and sk-prop-sf-dualizable-biduality.proof.md; Stacks Project, Tag 08JJ
(blueprint: sk-prop-sf-dualizable-biduality).

Proof: the ambient derived category is braided monoidal closed, with the published
Koszul braiding supplied locally. The generic rigid-category lemmas show that the internal
dual `(ihom K).obj (𝟙_ _)` is dualizable whenever `K` is dualizable, that
`toIhomIhomUnit K` is an isomorphism, and that
`ihomUnitTensorToIhom K M` is an isomorphism for every `M` after swapping the exact pairing
coming from a right dual of `K`. The definition of `coefficientDual` unfolds to that internal
dual, so these three generic conclusions give the theorem directly. -/
theorem dualizable_biduality
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u})
    (K : DerivedCategory (CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)))
    (_hK : IsDualizable K) :
    IsDualizable (coefficientDual Λ X K) ∧
      IsIso (@MonoidalClosed.toIhomIhomUnit _ _ _
        (DerivedCategory.braidedCategory' _) _ K) ∧
      ∀ M : DerivedCategory (CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj Λ X)),
        IsIso (MonoidalClosed.ihomUnitTensorToIhom K M) := by
  let := DerivedCategory.braidedCategory'
    (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
  have hDual : IsDualizable (coefficientDual Λ X K) := by
    change IsDualizable ((ihom K).obj (𝟙_ _))
    exact _hK.ihom_unit
  refine ⟨hDual, MonoidalClosed.isIso_toIhomIhomUnit_of_isDualizable _hK, ?_⟩
  obtain ⟨_⟩ := _hK
  let := BraidedCategory.exactPairing_swap K Kᘁ
  intro M
  exact MonoidalClosed.isIso_ihomUnitTensorToIhom Kᘁ K M

end AlgebraicGeometry.ProEtale.CondensedRing
