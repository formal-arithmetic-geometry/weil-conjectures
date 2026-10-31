/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RationalPurityCoefficientModels
import all WeilConjectures.AlgebraicGeometry.CompletedIntegralFiniteFree
import all WeilConjectures.AlgebraicGeometry.CompletedCoefficientPresentationTransport
import WeilConjectures.AlgebraicGeometry.FiniteFreeProperScalarComparison

/-! # Invertibility of the lifted integral compact-support scalar mate -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry WeilConjectures
namespace AlgebraicGeometry.Scheme

private theorem liftedScalar_finiteFree (l : ℕ) [Fact l.Prime]
    (E F : Type u) [Field E] [Field F] [Algebra (Padic l) E] [Algebra (Padic l) F]
    [FiniteDimensional (Padic l) E] [FiniteDimensional (Padic l) F]
    (i : E →ₐ[Padic l] F) (W : Scheme.{u}) :
    let := i.toAlgebra
    Nonempty
      ((pbcRestrict (pbcScalarCoefficientMap l E F i W)).obj
          (SheafOfModules.unit ((adicLisseForget W).obj
            ((pbcPurityCoefficients l F).ring W))) ≅
        ∏ᶜ fun _ : Fin (Module.finrank E F) ↦
          SheafOfModules.unit ((adicLisseForget W).obj
            ((pbcPurityCoefficients l E).ring W))) := by
  let := i.toAlgebra
  let C := adicLisseForget W
  let eE := C.mapIso (purCoefficientIso l E W)
  let eF := C.mapIso (purCoefficientIso l F W)
  let φ := integralCompletedScalarMap l E F i W
  obtain ⟨b⟩ := completedIntegralFiniteFree l E W F i φ
    (fun n ↦ (integralCompletedScalarMap_existsUnique l E F i W).exists.choose_spec n)
  apply freeTransport eE.symm eF.symm (C.map φ)
    (C.map (pbcScalarCoefficientMap l E F i W)) _ _ b
  have h := congrArg C.map (coefficientScalar_square l E F i W)
  simp only [Functor.map_comp] at h
  change eE.hom ≫ C.map φ = C.map (pbcScalarCoefficientMap l E F i W) ≫ eF.hom at h
  apply (Iso.comp_inv_eq eF).mpr
  rw [Category.assoc]
  apply (Iso.eq_inv_comp eE).mpr
  exact h

-- The finite-free proof is more general than the recorded geometric interface.
set_option linter.unusedVariables false

/-- Finite coefficient extension makes the actual integral proper/open scalar mate
invertible on a complete PBC lattice. Only the coefficient maps of the change
matter; its commutative-square proofs carry no additional choice.

Source: Bhatt--Scholze, Lemmas 6.7.7 and 6.8.2(1); blueprint
prop-pur-rational-purity-transitivity-summands, Step 3, and
lem-pur-compact-support-integral-coefficient-comparison, proper/open factorization.
(blueprint: lem-pur-lifted-compact-scalar-invertible).

Proof: transport completedIntegralFiniteFree along purCoefficientIso. The proved
coefficientScalar_square identifies the transported scalar action with the specified
lifted coefficient map. Apply properComparison_isIso_of_finiteFree to this basis:
its iterated-mate calculation identifies the finite-free direct-image comparison
with the specified inverse scalar mate, up to the unique isomorphisms of left
adjoints. Combine this with openComparison_isIso using comparison_factorization.
The argument also applies to ramified and identity extensions, the zero input and
empty schemes. It uses no integral representative of a rational idempotent. -/
theorem pbcPurityCompactScalar_integral_isIso (l : ℕ) [Fact l.Prime]
    (E F : Type u) [Field E] [Field F] [Algebra (Padic l) E] [Algebra (Padic l) F]
    [FiniteDimensional (Padic l) E] [FiniteDimensional (Padic l) F]
    (i : E →ₐ[Padic l] F)
    (a : PurCompactSupport.Change
      (pbcPurityCoefficients l E)
      (pbcPurityCoefficients l F))
    (ha : ∀ W, a.map W = pbcScalarCoefficientMap l E F i W)
    {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] (c : Compactification f)
    [IsNoetherian X] [IsNoetherian Y]
    [dX : Fact (∃ n : ℕ, topologicalKrullDim X ≤ (n : WithBot ℕ∞))]
    [dY : Fact (∃ n : ℕ, topologicalKrullDim Y ≤ (n : WithBot ℕ∞))]
    [iX : Fact (∀ x : X, IsUnit (l : X.presheaf.stalk x))]
    [iY : Fact (∀ y : Y, IsUnit (l : Y.presheaf.stalk y))]
    (K : PbcBoundedConstructibleComplete X (pbcIntegralDatum l E)) :
    IsIso ((PurCompactSupport.comparison a c).app K.obj) := by
  let := i.toAlgebra
  have hfree := liftedScalar_finiteFree l E F i Y
  rw [← ha Y] at hfree
  have hproper := PurCompactSupport.properComparison_isIso_of_finiteFree a c.g
    (Module.finrank E F) hfree
    ((PurCompactSupport.openExtension (pbcPurityCoefficients l E) c.i).mapDerivedCategory.obj
      K.obj)
  have hopen := PurCompactSupport.openComparison_isIso a c.i K.obj
  rw [PurCompactSupport.comparison_factorization]
  infer_instance

end AlgebraicGeometry.Scheme
