/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.LatticeSheafBasic
public import Sheaf.Paper.ContinuousIntegralLocalization
public import Sheaf.NumberTheory.Padics.CoefficientExtension

/-! # Local fractions for lattice scalar extension -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits Opposite
open scoped ChangeOfRings CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale

attribute [local instance] latticeWeakSheafifyOver latticeWEqualsOver

variable (ell : ℕ) [Fact ell.Prime] (E : Type u) [NormedField E]
  [NormedAlgebra ℚ_[ell] E] [FiniteDimensional ℚ_[ell] E]

/-- Scalar extension along the integral inclusion is localization at ell, on every slice.
Source: Bhatt--Scholze, Lemma 6.8.2(2); Stacks Project, Tags 00CM and 03EK.
(blueprint: lem-sfb-lattice-scalar-extension-fractions).

Proof. On a compact profinite test, boundedness of a continuous E-valued function
clears its norm by a power of ell. Thus the regular rational coefficient module
is the filtered colimit of regular integral modules with transition ell.
Sheafification, inverse image from the point, and restriction to a slice preserve
this colimit. Tensoring with M preserves it and identifies the vertex with
restricted sheafified scalar extension. The nth leg is m ↦ ell^(-n) tensor m:
this formula is balanced, respects restrictions, and satisfies the cocone relation.
The inverse formula follows by balancing the integral numerator a across the tensor.
For the local assertion, sections of a sheafified filtered colimit locally lift to
the presheaf colimit; each such lift is represented at a finite stage. Multiplying
that representative by ell^n identifies it with the zeroth leg. These covers allow
different exponents on different members, including non-quasi-compact objects. -/
theorem lattice_scalar_extension_fractions (X : Scheme.{u}) (U : X.ProEt)
    (M : SheafOfModules.{u + 1}
      ((latticeModuleRing X (Padic.coefficientExtensionIntegers ell E)).over U)) :
    let a := latticeCoefficientSheafMap X
      (Padic.coefficientExtensionIntegers ell E).subtype continuous_subtype_val
    let N := SheafOfModules.changeOfRings.{u, u + 1, u + 1} (latticeScalarMap a U) M
    let Q := (SheafOfModules.restrictScalars.{u + 1}
      ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
        (latticeScalarMap a U))).obj N
    (∃ c : Cocone (CondensedRing.integralLocalizationSequence ell M),
      Nonempty (IsColimit c) ∧ ∃ e : c.pt ≅ Q,
        (∀ (n : ℕ) (T : (Over U)ᵒᵖ) (m : M.val.obj T),
          e.hom.val.app T ((c.ι.app n).val.app T m) =
            (latticeTensorUnit a U M).app T
              (latticeConstantCoefficient X E T.unop.left ((ell : E) ^ n)⁻¹ ⊗ₜ[
                (latticeCoefficientSheaf X
                  (Padic.coefficientExtensionIntegers ell E)).obj.obj (op T.unop.left),
                ((a.hom.app (op T.unop.left)).hom)] m)) ∧
        (∀ (n : ℕ) (T : (Over U)ᵒᵖ)
          (b : (latticeCoefficientSheaf X
            (Padic.coefficientExtensionIntegers ell E)).obj.obj (op T.unop.left))
          (m : M.val.obj T),
          e.inv.val.app T ((latticeTensorUnit a U M).app T
            ((a.hom.app (op T.unop.left) b *
              latticeConstantCoefficient X E T.unop.left ((ell : E) ^ n)⁻¹) ⊗ₜ[
                (latticeCoefficientSheaf X
                  (Padic.coefficientExtensionIntegers ell E)).obj.obj (op T.unop.left),
                ((a.hom.app (op T.unop.left)).hom)] m)) =
                  (c.ι.app n).val.app T (b • m))) ∧
    (∀ (T : Over U) (x : N.val.obj (op T)),
      ∃ s : Sieve T, s ∈ ((Scheme.ProEt.topology X).over U) T ∧
        ∀ (V : Over U) (f : V ⟶ T), s f →
          ∃ (n : ℕ) (m : M.val.obj (op V)),
            ell ^ n • N.val.map f.op x =
              (latticeTensorUnit a U M).app (op V)
                ((1 : (latticeCoefficientSheaf X E).obj.obj (op V.left)) ⊗ₜ[
                  (latticeCoefficientSheaf X
                    (Padic.coefficientExtensionIntegers ell E)).obj.obj (op V.left),
                  ((a.hom.app (op V.left)).hom)] m)) := by
  sorry

end AlgebraicGeometry.ProEtale
