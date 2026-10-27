/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NE
-/
module

public import Sheaf.Paper.SfQbarLocalizationFiniteData
import WeilConjectures.CategoryTheory.StageSystem.Preadditive
import Mathlib.CategoryTheory.Preadditive.Biproducts
import Sheaf.Paper.SfQbarLocalizationShiftDescent

/-! # Exact descent on the general rational coefficient stages

Source: the algebraically closed-stage localization argument, coefficient
comparison and adjunction compatibility steps.
(blueprint: lem-sf-qbar-localization-exact-descent).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genInjectivity false
set_option genSizeOf false
set_option genCtorIdx false
set_option genSizeOfSpec false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated AlgebraicGeometry
namespace WeilConjectures
open GeneralAlgebraicallyClosedCoefficients
open AlgebraicallyClosedCoefficients (Index Coefficient)
variable (l : ℕ) [Fact l.Prime]
  (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]

private theorem localizationPreadditive (V : Scheme.{u}) :
    GeneralAlgebraicallyClosedCoefficients.preadditive (l := l) (Ω := Ω) (Y := V) =
      StageSystem.PairCategory.preadditive (S := stageSystem l Ω V) := by
  exact Subsingleton.elim _ _

private theorem localizationAdditive {V W : Scheme.{u}}
    (F : (stageSystem l Ω V).Morphism (stageSystem l Ω W))
    (h : ∀ E, (F.Φ E).Additive) : F.functor.Additive := by
  let := h
  rw [localizationPreadditive l Ω V, localizationPreadditive l Ω W]
  infer_instance

/-- A finite exact family with shift-compatible coefficient comparisons descends
exactly, with its stage-inclusion comparison commuting with shifts.
Source: localization proof, algebraically closed-stage steps 3--4.
(blueprint: lem-sf-qbar-localization-exact-descent).

Proof: use the descended shift comparison. Additivity follows from the unique
preadditive structure on a category with binary biproducts and the upstream
additive pair-functor construction. Every distinguished triangle is isomorphic
to an included finite-stage triangle. The inclusion comparison identifies its
functor image with the included finite-functor image, distinguished by finite
exactness. Transport along the resulting triangle isomorphism.
-/
theorem sfLocalizationExactDescent {V W : Scheme.{u}}
    (F : (stageSystem l Ω V).Morphism (stageSystem l Ω W))
    (h : SfLocalizationFiniteExact l Ω F) :
    ∃ s : F.functor.CommShift ℤ,
      letI := s
      F.functor.Additive ∧ F.functor.IsTriangulated ∧
        ∀ E : Index l Ω,
          let := h.shift E
          NatTrans.CommShift (F.ιCompFunctorIso E).hom ℤ := by
  obtain ⟨s, hs⟩ := sfLocalizationShiftDescent l Ω F h.shift h.beta_shift
  let := s
  refine ⟨s, localizationAdditive l Ω F h.additive, ?_, hs⟩
  constructor
  intro T hT
  obtain ⟨E, K, hK, ⟨e⟩⟩ := (distinguished_iff T).mp hT
  let := h.shift E
  let := h.exact E
  let := hs E
  have : ((inclusion (Y := V) E) ⋙ F.functor).IsTriangulated :=
    Functor.isTriangulated_of_iso (F.ιCompFunctorIso E).symm
  exact isomorphic_distinguished _
    (((inclusion (Y := V) E) ⋙ F.functor).map_distinguished K hK) _
    (F.functor.mapTriangle.mapIso e ≪≫
      (Functor.mapTriangleCompIso (inclusion (Y := V) E) F.functor).symm.app K)

end WeilConjectures
