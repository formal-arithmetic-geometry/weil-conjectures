/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q1
-/
import Sheaf.Paper.LisseAdicSheaves

/-!
# The fibre functors of lisse adic sheaves

Source: Deligne, Weil II (1.1.1) b)-d), SGA 5 VI
(blueprint: def-pod-lisse-adic-fibre-functors).
The objects are the recorded integral, rational and algebraic fibres.
-/

universe d
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

variable (l : ℕ) [Fact l.Prime] (E : Type (d + 1)) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (Y : Scheme.{d})
  [IsNoetherian Y] [Y.IsSeparated] [∀ x : Y, Invertible (l : Y.residueField x)]
  {Ω : Type d} [Field Ω] [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ Y)

/-- The integral fibre on objects and compatible families of maps.
Source: Weil II (1.1.1) b) (blueprint: def-pod-lisse-adic-fibre-functors). -/
noncomputable def lisseIntegralFiberFunctor :
    LisseIntegralSheaf l E Y ⥤ ModuleCat.{d + 1} (Padic.coefficientExtensionIntegers l E) :=
  ObjectProperty.ι _ ⋙
    (Functor.whiskeringRight _ _ _).obj (pointSmallEtale y).ulift.{d + 1}.sheafFiber ⋙ lim

/-- The rational fibre map is scalar extension of the integral map.
Source: Weil II (1.1.1) c) (blueprint: def-pod-lisse-adic-fibre-functors).
Proof: extend `(a,f) ↦ a • (f_y ⊗ 1)` by the balanced-tensor universal property.
Integral fibre maps respect the coefficient action, so this is balanced. Identity and
composition follow on pure tensors from the defining rational composition and from
functoriality of the integral fibre, and then everywhere by additivity. -/
theorem lisseRationalFiberFunctor_exists :
    ∃ T : LisseRationalSheaf l E Y ⥤ ModuleCat.{d + 1} E,
      ∃ h : ∀ F, T.obj F = lisseRationalFiber l E Y y F,
        ∀ (F H : LisseRationalSheaf l E Y) (a : E) (f : F.integral ⟶ H.integral),
          T.map (TensorProduct.tmul _ a f) =
            eqToHom (h F) ≫ ModuleCat.ofHom
              (a • LinearMap.baseChange E ((lisseIntegralFiberFunctor l E Y y).map f).hom) ≫
                eqToHom (h H).symm := by
  sorry

/-- The rational fibre functor with its prescribed maps on pure tensors.
Source: Weil II (1.1.1) c) (blueprint: def-pod-lisse-adic-fibre-functors). -/
noncomputable def lisseRationalFiberFunctor : LisseRationalSheaf l E Y ⥤ ModuleCat.{d + 1} E :=
  (lisseRationalFiberFunctor_exists l E Y y).choose

/-- Its object value is exactly the recorded rational fibre.
Source: Weil II (1.1.1) c) (blueprint: def-pod-lisse-adic-fibre-functors).
Proof: the functor was selected from the existence theorem with precisely these
object values; use its first specification. -/
theorem lisseRationalFiberFunctor_obj (F : LisseRationalSheaf l E Y) :
    (lisseRationalFiberFunctor l E Y y).obj F = lisseRationalFiber l E Y y F := by
  sorry

section Algebraic

variable (K : Type (d + 1)) [Field K] [Algebra ℚ_[l] K] [IsAlgClosure ℚ_[l] K]

/-- The arrow on a fixed rational model in the coefficient localization.
Source: Weil II (1.1.1) d) (blueprint: def-pod-lisse-adic-fibre-functors). -/
noncomputable def lisseAlgebraicModelMap (E₀ : Padic.FiniteCoefficientFields l K)
    {F H : LisseRationalSheaf l E₀.val Y} (f : F ⟶ H) :
    lisseAlgebraicOfModel l Y K E₀ F ⟶ lisseAlgebraicOfModel l Y K E₀ H :=
  (lisseCoefficientCocartesian l Y K).Q.map
    { base := 𝟙 E₀
      fiber := ((lisseCoefficientDiagramData l Y K).diagram.mapId ⟨E₀⟩).hom.toNatTrans.app _ ≫
        (eqToHom ((lisseCoefficientDiagramData l Y K).obj_eq E₀).symm).toFunctor.map f }

/-- Fixed-model arrows preserve identities.
Source: Weil II (1.1.1) d) (blueprint: def-pod-lisse-adic-fibre-functors).
Proof: the Grothendieck identity is the pseudofunctor identity constraint itself;
localization and the category-value transport preserve identities. -/
theorem lisseAlgebraicModelMap_id (E₀ : Padic.FiniteCoefficientFields l K)
    (F : LisseRationalSheaf l E₀.val Y) :
    lisseAlgebraicModelMap l Y K E₀ (𝟙 F) = 𝟙 _ := by
  sorry

/-- Fixed-model arrows preserve composition.
Source: Weil II (1.1.1) d) (blueprint: def-pod-lisse-adic-fibre-functors).
Proof: the pseudofunctor triangle identity cancels its identity constraints in the
Grothendieck composite. Category-value transport and localization preserve composition. -/
theorem lisseAlgebraicModelMap_comp (E₀ : Padic.FiniteCoefficientFields l K)
    {F H J : LisseRationalSheaf l E₀.val Y} (f : F ⟶ H) (g : H ⟶ J) :
    lisseAlgebraicModelMap l Y K E₀ (f ≫ g) =
      lisseAlgebraicModelMap l Y K E₀ f ≫ lisseAlgebraicModelMap l Y K E₀ g := by
  sorry

/-- The canonical functor of a rational coefficient model into algebraic coefficients.
Source: Weil II (1.1.1) d) (blueprint: def-pod-lisse-adic-fibre-functors). -/
noncomputable def lisseAlgebraicModelFunctor (E₀ : Padic.FiniteCoefficientFields l K) :
    LisseRationalSheaf l E₀.val Y ⥤ LisseAlgebraicSheaf l Y K where
  obj := lisseAlgebraicOfModel l Y K E₀
  map := lisseAlgebraicModelMap l Y K E₀
  map_id := lisseAlgebraicModelMap_id l Y K E₀
  map_comp := lisseAlgebraicModelMap_comp l Y K E₀

/-- The fibre of a displayed rational model is its specified scalar extension.
Source: Weil II (1.1.1) d) (blueprint: def-pod-lisse-adic-fibre-functors).
Proof: the localization keeps objects. The coefficient pair of the model has base
E₀ and fibre F, transported along the recorded category-value equality and back;
these inverse transports cancel. Unfold the recorded algebraic fibre. -/
theorem lisseAlgebraicFiber_ofModel (E₀ : Padic.FiniteCoefficientFields l K)
    (F : LisseRationalSheaf l E₀.val Y) :
    lisseAlgebraicFiber l Y K y (lisseAlgebraicOfModel l Y K E₀ F) =
      ModuleCat.of K (TensorProduct E₀.val K (lisseRationalFiber l E₀.val Y y F)) := by
  sorry

/-- The fibre extends to the coefficient localization with the prescribed object values
and with scalar extension on each rational model.
Source: Weil II (1.1.1) d) (blueprint: def-pod-lisse-adic-fibre-functors).
Proof: on a coefficient pair use K tensor_E its rational fibre. On an arrow extend
its rational fibre map to K. Tensor associativity identifies fibres after a coefficient
inclusion; its pure-tensor formula makes all cocartesian arrows invertible and all
coherence diagrams commute. Localization therefore gives the functor, with the
specified scalar-extension isomorphisms on rational models. -/
theorem lisseAlgebraicFiberFunctor_exists :
    ∃ T : LisseAlgebraicSheaf l Y K ⥤ ModuleCat.{d + 1} K,
      ∃ h : ∀ F, T.obj F = lisseAlgebraicFiber l Y K y F,
        ∀ E₀ : Padic.FiniteCoefficientFields l K,
          ∃ τ : lisseAlgebraicModelFunctor l Y K E₀ ⋙ T ≅
              lisseRationalFiberFunctor l E₀.val Y y ⋙
                ModuleCat.extendScalars (algebraMap E₀.val K),
            ∀ (F : LisseRationalSheaf l E₀.val Y) (a : K)
              (z : (lisseRationalFiberFunctor l E₀.val Y y).obj F),
              eqToHom (h (lisseAlgebraicOfModel l Y K E₀ F))
                (τ.inv.app F (TensorProduct.tmul _ a z)) =
                eqToHom (lisseAlgebraicFiber_ofModel l Y y K E₀ F).symm
                  (TensorProduct.tmul _ a
                    (eqToHom (lisseRationalFiberFunctor_obj l E₀.val Y y F) z)) := by
  sorry

/-- The algebraic fibre functor induced on the coefficient localization.
Source: Weil II (1.1.1) d) (blueprint: def-pod-lisse-adic-fibre-functors). -/
noncomputable def lisseAlgebraicFiberFunctor :
    LisseAlgebraicSheaf l Y K ⥤ ModuleCat.{d + 1} K :=
  (lisseAlgebraicFiberFunctor_exists l Y y K).choose

/-- Its object value is the recorded algebraic fibre.
Source: Weil II (1.1.1) d) (blueprint: def-pod-lisse-adic-fibre-functors).
Proof: the object specification is the first clause of the selected existence theorem. -/
theorem lisseAlgebraicFiberFunctor_obj (F : LisseAlgebraicSheaf l Y K) :
    (lisseAlgebraicFiberFunctor l Y y K).obj F = lisseAlgebraicFiber l Y K y F := by
  sorry

end Algebraic
end AlgebraicGeometry.Scheme
