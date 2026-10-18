/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q1
-/
module

public import Sheaf.Paper.LisseAdicSheaves
import WeilConjectures.CategoryTheory.Sites.Point.Linear

/-!
# The fibre functors of lisse adic sheaves

Source: Deligne, Weil II (1.1.1) b)-d), SGA 5 VI
(blueprint: def-pod-lisse-adic-fibre-functors).
The objects are the recorded integral, rational and algebraic fibres.
-/

@[expose] public section

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

private lemma integralFiber_map_add {F G : LisseIntegralSheaf l E Y}
    (f g : F ⟶ G) :
    (lisseIntegralFiberFunctor l E Y y).map (f + g) =
      (lisseIntegralFiberFunctor l E Y y).map f +
        (lisseIntegralFiberFunctor l E Y y).map g := by
  apply limit.hom_ext
  intro j
  simp only [lisseIntegralFiberFunctor, Functor.comp_map, ObjectProperty.ι_map,
    Functor.whiskeringRight_obj_map, lim, limMap_π, Preadditive.add_comp]
  change _ ≫ ((pointSmallEtale y).ulift.{d + 1}.sheafFiber).map
    (f.hom.app j + g.hom.app j) = _
  let := Functor.additive_of_preserves_binary_products
    ((pointSmallEtale y).ulift.{d + 1}.sheafFiber
      (A := ModuleCat.{d + 1} (Padic.coefficientExtensionIntegers l E)))
  rw [Functor.map_add, Preadditive.comp_add]
  rfl

private lemma integralFiber_map_smul {F G : LisseIntegralSheaf l E Y}
    (r : Padic.coefficientExtensionIntegers l E) (f : F ⟶ G) :
    (lisseIntegralFiberFunctor l E Y y).map (r • f) =
      r • (lisseIntegralFiberFunctor l E Y y).map f := by
  apply limit.hom_ext
  intro j
  simp only [lisseIntegralFiberFunctor, Functor.comp_map, ObjectProperty.ι_map,
    Functor.whiskeringRight_obj_map, lim, limMap_π, Linear.smul_comp]
  change _ ≫ ((pointSmallEtale y).ulift.{d + 1}.sheafFiber).map
    (r • f.hom.app j) = _
  rw [GrothendieckTopology.Point.sheafFiber_map_smul, Linear.comp_smul]
  rfl

private noncomputable def rationalFiberMap (F G : LisseRationalSheaf l E Y) :
    lisseRationalHom l E Y F G →ₗ[E]
      (lisseRationalFiber l E Y y F →ₗ[E] lisseRationalFiber l E Y y G) :=
  let R := Padic.coefficientExtensionIntegers l E
  let m : (F.integral ⟶ G.integral) →ₗ[R]
      ((lisseIntegralFiber l E Y y F.integral) →ₗ[R]
        (lisseIntegralFiber l E Y y G.integral)) :=
    { toFun f := ((lisseIntegralFiberFunctor l E Y y).map f).hom
      map_add' f g := congrArg ModuleCat.Hom.hom (integralFiber_map_add l E Y y f g)
      map_smul' r f := congrArg ModuleCat.Hom.hom (integralFiber_map_smul l E Y y r f) }
  TensorProduct.AlgebraTensorModule.lift
    { toFun a := a • ((LinearMap.baseChangeHom R E _ _).comp m)
      map_add' a b := by ext; simp [add_smul]
      map_smul' a b := by ext; simp [mul_smul] }

private lemma rationalFiberMap_tmul (F G : LisseRationalSheaf l E Y)
    (a : E) (f : F.integral ⟶ G.integral) :
    rationalFiberMap l E Y y F G (TensorProduct.tmul _ a f) =
      a • LinearMap.baseChange E ((lisseIntegralFiberFunctor l E Y y).map f).hom := rfl

private lemma rationalFiberMap_id (F : LisseRationalSheaf l E Y) :
    rationalFiberMap l E Y y F F (TensorProduct.tmul _ 1 (𝟙 F.integral)) =
      LinearMap.id := by
  rw [rationalFiberMap_tmul]
  change 1 • LinearMap.baseChange E
    (((lisseIntegralFiberFunctor l E Y y).map (𝟙 F.integral)).hom) =
      (LinearMap.id :
        TensorProduct (Padic.coefficientExtensionIntegers l E) E
          ((lisseIntegralFiberFunctor l E Y y).obj F.integral) →ₗ[E] _)
  rw [(lisseIntegralFiberFunctor l E Y y).map_id]
  simp

private lemma rationalFiberMap_comp (F G H : LisseRationalSheaf l E Y)
    (f : F ⟶ G) (g : G ⟶ H) :
    rationalFiberMap l E Y y F H ((lisseRationalComposition l E Y).comp F G H f g) =
      (rationalFiberMap l E Y y G H g).comp (rationalFiberMap l E Y y F G f) := by
  induction f using TensorProduct.induction_on with
  | zero => simp
  | tmul a f =>
    induction g using TensorProduct.induction_on with
    | zero => simp
    | tmul b g =>
      rw [(lisseRationalComposition l E Y).comp_tmul, rationalFiberMap_tmul,
        rationalFiberMap_tmul, rationalFiberMap_tmul, Functor.map_comp]
      change (a * b) • LinearMap.baseChange E
        ((((lisseIntegralFiberFunctor l E Y y).map g).hom).comp
          (((lisseIntegralFiberFunctor l E Y y).map f).hom)) = _
      rw [LinearMap.baseChange_comp, LinearMap.smul_comp, LinearMap.comp_smul,
        smul_smul, mul_comm a b]
    | add g h hg hh => simp [hg, hh, LinearMap.add_comp]
  | add f g hf hg => simp [hf, hg, LinearMap.comp_add]

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
  let T : LisseRationalSheaf l E Y ⥤ ModuleCat.{d + 1} E :=
    { obj F := lisseRationalFiber l E Y y F
      map {F G} f := ModuleCat.ofHom (rationalFiberMap l E Y y F G f)
      map_id F := congrArg ModuleCat.ofHom (rationalFiberMap_id l E Y y F)
      map_comp {F G H} f g :=
        congrArg ModuleCat.ofHom (rationalFiberMap_comp l E Y y F G H f g) }
  refine ⟨T, (fun _ ↦ rfl), ?_⟩
  intro F G a f
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  exact congrArg ModuleCat.ofHom (rationalFiberMap_tmul l E Y y F G a f)

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
  exact (lisseRationalFiberFunctor_exists l E Y y).choose_spec.choose F

private def grothendieckFiberInclusion {B : Type*} [Category B]
    (P : Pseudofunctor (LocallyDiscrete B) Cat.{d + 1, d + 2}) (b : B) :
    P.obj ⟨b⟩ ⥤ Pseudofunctor.Grothendieck P where
  obj X := ⟨b, X⟩
  map {X Z} f := { base := 𝟙 b, fiber := (P.mapId ⟨b⟩).hom.toNatTrans.app X ≫ f }
  map_id X := by
    refine Pseudofunctor.Grothendieck.Hom.ext _ _ rfl ?_
    simp
  map_comp {X Z W} f g := by
    refine Pseudofunctor.Grothendieck.Hom.ext _ _ (by simp) ?_
    simp [P.mapComp_id_left_hom_app, Bicategory.Strict.leftUnitor_eqToIso,
      PrelaxFunctor.map₂_eqToHom]

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
  let T := (eqToHom ((lisseCoefficientDiagramData l Y K).obj_eq E₀).symm).toFunctor ⋙
    grothendieckFiberInclusion (lisseCoefficientDiagramData l Y K).diagram E₀ ⋙
      (lisseCoefficientCocartesian l Y K).Q
  exact T.map_id F

/-- Fixed-model arrows preserve composition.
Source: Weil II (1.1.1) d) (blueprint: def-pod-lisse-adic-fibre-functors).
Proof: the pseudofunctor triangle identity cancels its identity constraints in the
Grothendieck composite. Category-value transport and localization preserve composition. -/
theorem lisseAlgebraicModelMap_comp (E₀ : Padic.FiniteCoefficientFields l K)
    {F H J : LisseRationalSheaf l E₀.val Y} (f : F ⟶ H) (g : H ⟶ J) :
    lisseAlgebraicModelMap l Y K E₀ (f ≫ g) =
      lisseAlgebraicModelMap l Y K E₀ f ≫ lisseAlgebraicModelMap l Y K E₀ g := by
  let T := (eqToHom ((lisseCoefficientDiagramData l Y K).obj_eq E₀).symm).toFunctor ⋙
    grothendieckFiberInclusion (lisseCoefficientDiagramData l Y K).diagram E₀ ⋙
      (lisseCoefficientCocartesian l Y K).Q
  exact T.map_comp f g

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
  change ModuleCat.of K (TensorProduct E₀.val K
    (lisseRationalFiber l E₀.val Y y
      ((eqToHom ((lisseCoefficientDiagramData l Y K).obj_eq E₀)).toFunctor.obj
        ((eqToHom ((lisseCoefficientDiagramData l Y K).obj_eq E₀).symm).toFunctor.obj F))))
    = _
  have cancel (C D : Cat.{d + 1, d + 2}) (h : C = D) (X : D) :
      (eqToHom h).toFunctor.obj ((eqToHom h.symm).toFunctor.obj X) = X := by
    cases h
    rfl
  exact congrArg (fun X ↦ ModuleCat.of K (TensorProduct E₀.val K
    (lisseRationalFiber l E₀.val Y y X)))
    (cancel _ (Cat.of (LisseRationalSheaf l E₀.val Y))
      ((lisseCoefficientDiagramData l Y K).obj_eq E₀) F)

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
  exact (lisseAlgebraicFiberFunctor_exists l Y y K).choose_spec.choose F

end Algebraic
end AlgebraicGeometry.Scheme
