/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.RationalVerdier.RationalVerdierModels
import WeilConjectures.SixFunctors.RationalVerdier.RationalVerdierIntegralBetaNaturality

/-! # Naturality of the localized integral beta components

Source: blueprint thm-coef-rational-verdier, proof
(blueprint: lem-coef-rational-verdier-comparison-naturality). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option linter.style.haveILetI false

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open CategoryTheory.Pretriangulated CategoryTheory.Pretriangulated.Opposite
open scoped TensorProduct

namespace WeilConjectures.RationalVerdier

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]

/-- Naturality of the localized integral beta components.
Source: current blueprint thm-coef-rational-verdier.proof.md, paragraph 3;
lem-coef-integral-finite-extension.proof.md, evaluation and transposition paragraphs.
(blueprint: lem-coef-rational-verdier-comparison-naturality).

Proof: work first with integral arrows f. The ordinary coefficient Hom map is the
transpose of scalar-extended evaluation. Conjugating by the normalized completion
maps gives the completed evaluation transpose: the representative equations agree
on every local homogeneous tensor generator, and K-flat resolutions extend that
agreement to the derived category. Naturality of A.evaluation and B.evaluation
then makes the two naturality composites have equal uncurried maps. The localized
tensor-Hom adjunction is injective on transposes, so the composites agree for
integral f. The pure-tensor equations of A.dual, B.dual and scalar extension
multiply this equality by the image of each localized coefficient. Every rational
arrow is a sum of pure tensors; additivity gives the equation for all arrows.
The component normalization transfers this result to any supplied family c.
Zero objects, identity embeddings and empty schemes use the same calculation -/
theorem localizedBeta_naturality
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
    (i : E →ₐ[Padic l] L)
    (wE : IntegralFiniteExtension.DualizingDatum l X D hl E)
    (wL : IntegralFiniteExtension.DualizingDatum l X D hl L)
    (A : Datum D l hl X E wE) (B : Datum D l hl X L wL)
    (c : ∀ K : sfRationalConstructibleCategory l E X,
      (scalar l X E L i).obj (A.dual.obj (op K)) ⟶
        B.dual.obj (op ((scalar l X E L i).obj K)))
    (hc : (∀ K : sfIntegralConstructibleCategory l E X,
    HEq (c ((sfRationalConstructibleLocalization l E X).obj K))
      ((sfRationalConstructibleLocalization l L X).map
        (ObjectProperty.homMk
          (X := (integralScalar l X E L i).obj
            ((IntegralVerdier.restrictedDual l E X wE.omega.obj A.preserves).obj (op K)))
          (Y := (IntegralVerdier.restrictedDual l L X wL.omega.obj B.preserves).obj
            (op ((integralScalar l X E L i).obj K)))
          (IntegralFiniteExtension.beta l E L i X D hl wE wL A.ordinary B.ordinary
            K.obj K.property.1))))) :
    ∀ (K M : sfRationalConstructibleCategory l E X) (f : K ⟶ M),
      (A.dual ⋙ scalar l X E L i).map f.op ≫ c K =
      c M ≫ ((scalar l X E L i).op ⋙ B.dual).map f.op := by
  classical
  letI := A.additive
  letI := B.additive
  intro K M f
  cases K with
  | mk K =>
    cases M with
    | mk M =>
      induction f using TensorProduct.induction_on with
      | zero =>
          simp only [Functor.comp_map]
          rw [op_zero, Functor.map_zero A.dual, Functor.map_zero (scalar l X E L i),
            Functor.map_zero ((scalar l X E L i).op), Functor.map_zero B.dual,
            zero_comp, comp_zero]
      | add f g hf hg =>
          simp only [Functor.comp_map]
          rw [op_add, Functor.map_add A.dual, Functor.map_add (scalar l X E L i),
            Functor.map_add ((scalar l X E L i).op), Functor.map_add B.dual,
            Preadditive.add_comp, Preadditive.comp_add]
          exact congrArg₂ (fun x y => x + y) hf hg
      | tmul a f =>
          exact integralBeta_naturality D l hl X E L i wE wL A B c hc K M a f

end WeilConjectures.RationalVerdier
