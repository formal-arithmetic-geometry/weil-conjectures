/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.NativeConstantSupportModel
public import Sheaf.Paper.ConstantScalarTowerAdjunction
public import Sheaf.Paper.FiniteFreeCompletedScalarComparison

/-! # Existence of the ordinary compact-support coefficient comparison

This is the existence part of the ordinary constant/completed scalar comparison.
(blueprint: lem-pur-compact-support-coefficient-models)
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (F : Type u) [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]
  (i : E →ₐ[ℚ_[l]] F)

/-- The ordinary balancing map exists on the constant coefficient model.
Source: Bhatt--Scholze 6.8.2(1), Definition 3.4.10.
(blueprint: lem-pur-compact-support-coefficient-models-ordinary-existence).
Proof: put A = O_E, B = O_F and write R and S for the completed coefficient
sheaves. Choose a finite A-basis b_i of B. Its quotient bases identify S with the
finite free R-module with basis completion(b_i): a finite direct sum commutes with
the inverse limit defining the completed coefficients. Thus the multiplication map
R tensor_A B to S is an isomorphism, sending r tensor b to r * completion(b).
For the fixed R-module sheaf M, associate the tensor products and use this ring
isomorphism to identify M tensor_A B with M tensor_R S. Equivalently, the forward
map is b tensor x to completion(b) tensor x. To invert it, write a local coefficient
s of S uniquely as sum_i r_i * completion(b_i), and send s tensor x to
sum_i b_i tensor (r_i * x). Uniqueness of the coordinates makes this balanced over R;
the multiplication matrices of B in the basis prove B-linearity. The two composites
are the identity on pure tensors. The maps commute with restrictions, so the
presheaf tensor maps induce inverse morphisms after sheafification. Their formula
is the displayed one for every local b and x. This argument constructs each
component only; naturality in M and uniqueness are proved in the parent. -/
theorem compactSupportCoefficientModels_ordinary_exists (W : Scheme.{u})
    [HasSheafify (ProEt.topology W) AddCommGrpCat.{u + 1}]
    [(ProEt.topology W).WEqualsLocallyBijective AddCommGrpCat.{u + 1}] :
    ∀ M : scalarReductionSource l E W,
      ∃ β : (pbcExtend (PurStrictScalar.constantMap l E F i W)).obj
          ((PurStrictScalar.constantRestriction l E W).obj M) ≅
        (PurStrictScalar.constantRestriction l F W).obj
          ((pbcExtend (completedCoefficientMap l E F i W)).obj M),
      ∀ (U : W.ProEtᵒᵖ)
        (b : ((PurStrictScalar.constants l F).ring W).obj.obj U) (x : M.val.obj U),
        β.hom.val.app U
            (pbcTensorSection (PurStrictScalar.constantMap l E F i W)
              ((PurStrictScalar.constantRestriction l E W).obj M) U b x) =
          pbcTensorSection (completedCoefficientMap l E F i W) M U
            (((integralConstantToCompletionOfUniverses l F W).hom.app U) b) x := by
  sorry

end WeilConjectures
