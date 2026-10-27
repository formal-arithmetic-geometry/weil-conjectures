/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q21
-/
module

public import Sheaf.Paper.DerivedCompleteOnSlices
public import Sheaf.Paper.CompletedIntegralCoefficientGerm
public import Sheaf.CategoryTheory.ScalarLocalizationTriangulated
public import Mathlib.CategoryTheory.Triangulated.Triangulated
public import Sheaf.Paper.IntegralConstructibleLinear
public import Mathlib.CategoryTheory.Triangulated.Opposite.Triangulated
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import Mathlib.CategoryTheory.ObjectProperty.Retract
public import Mathlib.CategoryTheory.ObjectProperty.FiniteProducts
public import Mathlib.Algebra.Module.TransferInstance

import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.HomModule
public import Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses

public import Sheaf.CategoryTheory.RingedSiteModules

public import Mathlib.Algebra.Homology.DerivedCategory.Basic

public import Sheaf.Paper.IntegralDerivedOperationsOnSlices

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Sheaf.CategoryTheory.ScalarLocalization

/-!
# Integral and rational evaluation data on slices

Source: Weil blueprint, sec-six-functors/sk-prop-sf-dualizable-biduality,
first proof paragraph, exact functors and preservation of direct summands
(blueprint: lem-sf-rational-thick-evaluation).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
open CategoryTheory.Pretriangulated.Opposite
namespace WeilConjectures.IntegralOnSlice

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (X : AlgebraicGeometry.Scheme.{t}) (U : Option X.ProEt)

/-- Restrict the published constant scalar section to the actual over-site.
Source: blueprint, sk-def-sf-operations (blueprint: lem-sf-rational-thick-evaluation). -/
def scalarConstant (V : (Site X U)ᵒᵖ) (a : Padic.coefficientExtensionIntegers l E) :
    (ring l E X U).obj.obj V :=
  match U, V with
  | none, V => integralScalarConstant l E X V a
  | some _W, V => integralScalarConstant l E X (op V.unop.left) a

private theorem scalar_ext (U : X.ProEtᵒᵖ)
    {x y : (completedIntegralCoefficientSheafUnrestricted l E X).obj.obj U}
    (h : ∀ n : ℕ,
      ((CategoryTheory.Limits.limit.π (integralCoefficientSheafSystem l E X)
        (op n)).hom.app U) x =
      ((CategoryTheory.Limits.limit.π (integralCoefficientSheafSystem l E X)
        (op n)).hom.app U) y) : x = y := by
  let h₁ := CategoryTheory.Limits.isLimitOfPreserves
    (sheafToPresheaf (AlgebraicGeometry.Scheme.ProEt.topology X) RingCat)
    (CategoryTheory.Limits.limit.isLimit (integralCoefficientSheafSystem l E X))
  let h₂ := CategoryTheory.Limits.isLimitOfPreserves ((evaluation _ _).obj U) h₁
  apply Concrete.isLimit_ext _ h₂
  intro n
  exact h n.unop

private theorem scalar_naturality {U V : X.ProEtᵒᵖ} (f : U ⟶ V)
    (a : Padic.coefficientExtensionIntegers l E) :
    (completedIntegralCoefficientSheafUnrestricted l E X).obj.map f
      (integralScalarConstant l E X U a) = integralScalarConstant l E X V a := by
  apply scalar_ext l E X V
  intro n
  have hn := congrArg (fun k ↦ k.hom (integralScalarConstant l E X U a))
    ((CategoryTheory.Limits.limit.π (integralCoefficientSheafSystem l E X)
      (op n)).hom.naturality f)
  change ((CategoryTheory.Limits.limit.π (integralCoefficientSheafSystem l E X)
      (op n)).hom.app V)
      ((completedIntegralCoefficientSheafUnrestricted l E X).obj.map f
        (integralScalarConstant l E X U a)) =
      (integralCoefficientSheaf l E X n).obj.map f
        (((CategoryTheory.Limits.limit.π (integralCoefficientSheafSystem l E X)
          (op n)).hom.app U) (integralScalarConstant l E X U a)) at hn
  rw [hn]
  erw [(integralScalarConstant_existsUnique l E X U a).exists.choose_spec n,
    (integralScalarConstant_existsUnique l E X V a).exists.choose_spec n]
  exact (congrArg
    (fun k ↦ k.hom
      (ULift.up ((Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1))) a)))
    ((toSheafify (AlgebraicGeometry.Scheme.ProEt.topology X)
      ((Functor.const X.ProEtᵒᵖ).obj
        (CommRingCat.of
          (ULift.{t + 1} (Padic.coefficientExtensionRing l E (n + 1)))))).naturality f)).symm

private noncomputable abbrev finiteConstantMap (n : ℕ) (U : X.ProEtᵒᵖ) :=
  ((toSheafify (AlgebraicGeometry.Scheme.ProEt.topology X)
    ((Functor.const X.ProEtᵒᵖ).obj
      (CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionRing l E (n + 1)))))).app U).hom

private noncomputable def scalarSections : Padic.coefficientExtensionIntegers l E →+*
    RingCat.sectionsSubring
      ((completedIntegralCommRingSheafUnrestricted l E X).obj ⋙
        forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)}) where
  toFun a := ⟨fun U ↦ integralScalarConstant l E X U a,
    fun f ↦ scalar_naturality l E X f a⟩
  map_one' := by
    apply Subtype.ext
    funext U
    apply scalar_ext l E X U
    intro n
    erw [(integralScalarConstant_existsUnique l E X U 1).exists.choose_spec n]
    simp only [integralScalarFiniteConstant, Functor.comp_obj,
      CommRingCat.forgetToRingCat_obj, OneMemClass.coe_one, Pi.one_apply, map_one]
    exact map_one (finiteConstantMap l E X n U)
  map_mul' a b := by
    apply Subtype.ext
    funext U
    apply scalar_ext l E X U
    intro n
    change _ = (CategoryTheory.Limits.limit.π
      (integralCoefficientSheafSystem l E X) (op n)).hom.app U
        (integralScalarConstant l E X U a * integralScalarConstant l E X U b)
    rw [map_mul]
    erw [(integralScalarConstant_existsUnique l E X U (a * b)).exists.choose_spec n,
      (integralScalarConstant_existsUnique l E X U a).exists.choose_spec n,
      (integralScalarConstant_existsUnique l E X U b).exists.choose_spec n]
    simp only [integralScalarFiniteConstant, map_mul]
    exact map_mul (finiteConstantMap l E X n U) _ _
  map_zero' := by
    apply Subtype.ext
    funext U
    apply scalar_ext l E X U
    intro n
    erw [(integralScalarConstant_existsUnique l E X U 0).exists.choose_spec n]
    simp only [integralScalarFiniteConstant, Functor.comp_obj,
      CommRingCat.forgetToRingCat_obj, ZeroMemClass.coe_zero, Pi.zero_apply, map_zero]
    exact map_zero (finiteConstantMap l E X n U)
  map_add' a b := by
    apply Subtype.ext
    funext U
    apply scalar_ext l E X U
    intro n
    change _ = (CategoryTheory.Limits.limit.π
      (integralCoefficientSheafSystem l E X) (op n)).hom.app U
        (integralScalarConstant l E X U a + integralScalarConstant l E X U b)
    rw [map_add]
    erw [(integralScalarConstant_existsUnique l E X U (a + b)).exists.choose_spec n,
      (integralScalarConstant_existsUnique l E X U a).exists.choose_spec n,
      (integralScalarConstant_existsUnique l E X U b).exists.choose_spec n]
    simp only [integralScalarFiniteConstant, map_add]
    exact map_add (finiteConstantMap l E X n U) _ _

private def sliceScalarSections : Padic.coefficientExtensionIntegers l E →+*
    RingCat.sectionsSubring (rings l E X U).obj where
  toFun a := ⟨fun V ↦ scalarConstant l E X U V a, by
    intro V W f
    cases U with
    | none => exact scalar_naturality l E X f a
    | some B => exact scalar_naturality l E X ((Over.forget B).op.map f) a⟩
  map_one' := by
    apply Subtype.ext
    funext V
    cases U with
    | none => exact congrArg (fun s ↦ s.val V) (map_one (scalarSections l E X))
    | some B =>
      exact congrArg (fun s ↦ s.val (op V.unop.left)) (map_one (scalarSections l E X))
  map_mul' a b := by
    apply Subtype.ext
    funext V
    cases U with
    | none => exact congrArg (fun s ↦ s.val V) (map_mul (scalarSections l E X) a b)
    | some B =>
      exact congrArg (fun s ↦ s.val (op V.unop.left)) (map_mul (scalarSections l E X) a b)
  map_zero' := by
    apply Subtype.ext
    funext V
    cases U with
    | none => exact congrArg (fun s ↦ s.val V) (map_zero (scalarSections l E X))
    | some B =>
      exact congrArg (fun s ↦ s.val (op V.unop.left)) (map_zero (scalarSections l E X))
  map_add' a b := by
    apply Subtype.ext
    funext V
    cases U with
    | none => exact congrArg (fun s ↦ s.val V) (map_add (scalarSections l E X) a b)
    | some B =>
      exact congrArg (fun s ↦ s.val (op V.unop.left)) (map_add (scalarSections l E X) a b)

@[instance_reducible]
private def moduleLinear : Linear (Padic.coefficientExtensionIntegers l E) (Mod l E X U) := by
  letI : Linear (RingCat.sectionsSubring (rings l E X U).obj) (Mod l E X U) :=
    SheafOfModules.homLinear (ring l E X U).obj (rings l E X U).property
  exact
    { homModule := fun M N ↦ Module.compHom (M ⟶ N) (sliceScalarSections l E X U)
      smul_comp := fun M N P r f g ↦
        Linear.smul_comp M N P (sliceScalarSections l E X U r) f g
      comp_smul := fun M N P f r g ↦
        Linear.comp_smul M N P f (sliceScalarSections l E X U r) g }

section ScalarLinear

attribute [local instance] moduleLinear

/-- Scalars act on complexes by multiplication by the specified constant section.
Source: blueprint, sk-def-sf-operations (blueprint: lem-sf-rational-thick-evaluation).
Proof: the scalar sections commute with restriction, since they do at every finite
projection. Commutativity makes multiplication linear. It commutes with differentials
and all module maps. These equations give the chain maps and their naturality;
equality on each degree and section proves uniqueness. -/
theorem scalarChain_existsUnique (a : Padic.coefficientExtensionIntegers l E) :
    ∃! σ : 𝟭 (Cx l E X U) ⟶ 𝟭 (Cx l E X U),
      ∀ (P : Cx l E X U) (n : ℤ) (V : (Site X U)ᵒᵖ) (x : (P.X n).val.obj V),
        ((σ.app P).f n).val.app V x = scalarConstant l E X U V a • x := by
  let σ : 𝟭 (Cx l E X U) ⟶ 𝟭 (Cx l E X U) :=
    { app := fun P ↦ a • 𝟙 P
      naturality := fun P Q f ↦ by simp }
  refine ⟨σ, ?_, ?_⟩
  · intro P n V x
    rfl
  · intro σ' hσ'
    apply NatTrans.ext
    funext P
    apply HomologicalComplex.hom_ext
    intro n
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro V
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact hσ' P n V x

/-- The uniquely determined scalar action on complexes. Source: blueprint, sk-def-sf-operations
(blueprint: lem-sf-rational-thick-evaluation). -/
def scalarChain (a : Padic.coefficientExtensionIntegers l E) :=
  (scalarChain_existsUnique l E X U a).exists.choose

/-- The same scalar action after the actual quasi-isomorphism localization.
Source: Stacks 05RR (blueprint: lem-sf-rational-thick-evaluation). -/
def scalarDerived (a : Padic.coefficientExtensionIntegers l E) :
    𝟭 (D l E X U) ⟶ 𝟭 (D l E X U) :=
  (Localization.fullyFaithfulWhiskeringLeft
    (DerivedCategory.Q : Cx l E X U ⥤ D l E X U)
    (HomologicalComplex.quasiIso (Mod l E X U) (ComplexShape.up ℤ)) (D l E X U)).preimage
      (Functor.whiskerRight (scalarChain l E X U a) DerivedCategory.Q)

private theorem scalarChain_eq (a : Padic.coefficientExtensionIntegers l E) :
    scalarChain l E X U a =
      (Linear.toCatCenter (Padic.coefficientExtensionIntegers l E) (Cx l E X U)) a := by
  apply NatTrans.ext
  funext P
  apply HomologicalComplex.hom_ext
  intro n
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro V
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact (scalarChain_existsUnique l E X U a).exists.choose_spec P n V x

private theorem scalarDerived_eq (a : Padic.coefficientExtensionIntegers l E) :
    scalarDerived l E X U a =
      CatCenter.localization
        ((Linear.toCatCenter (Padic.coefficientExtensionIntegers l E) (Cx l E X U)) a)
        DerivedCategory.Q (HomologicalComplex.quasiIso (Mod l E X U) (.up ℤ)) := by
  apply CatCenter.ext_of_localization DerivedCategory.Q
    (HomologicalComplex.quasiIso (Mod l E X U) (.up ℤ))
  intro P
  have h := NatTrans.congr_app
    ((Localization.fullyFaithfulWhiskeringLeft
      (DerivedCategory.Q : Cx l E X U ⥤ D l E X U)
      (HomologicalComplex.quasiIso (Mod l E X U) (.up ℤ))
      (D l E X U)).map_preimage
        (X := 𝟭 (D l E X U)) (Y := 𝟭 (D l E X U))
        (Functor.whiskerRight (scalarChain l E X U a) DerivedCategory.Q)) P
  change (scalarDerived l E X U a).app (DerivedCategory.Q.obj P) = _ at h
  change (scalarDerived l E X U a).app (DerivedCategory.Q.obj P) = _
  rw [h, CatCenter.localization_app, scalarChain_eq]
  rfl

private theorem linear_ext
    {R : Type*} [Ring R] {C : Type*} [Category* C] [Preadditive C]
    (s t : Linear R C)
    (h : ∀ (A B : C) (a : R) (f : A ⟶ B),
      (letI := s; a • f) = (letI := t; a • f)) : s = t := by
  cases s with
  | mk s sm sc =>
    cases t with
    | mk t tm tc =>
      have heq : s = t := by
        funext A B
        exact Module.ext' _ _ (fun a f ↦ h A B a f)
      cases heq
      rfl

end ScalarLinear

set_option linter.unusedVariables false in
/-- The canonical scalar action determines the linear structure, including localized maps.
Source: Stacks 05RR (blueprint: lem-sf-rational-thick-evaluation).
Proof: the ring and module identities hold on sections, hence on complexes. Whiskering
by the quasi-isomorphism localization is fully faithful, so they descend to the displayed
central derived endomorphisms. Define a f by precomposition with that endomorphism.
Centrality gives bilinear composition, and the formula determines every Hom action. -/
theorem linear_existsUnique :
    ∃! s : Linear (Padic.coefficientExtensionIntegers l E) (D l E X U),
      (fun [linearInst : Linear (Padic.coefficientExtensionIntegers l E) (D l E X U)] ↦
        ∀ (a : Padic.coefficientExtensionIntegers l E) (A B : D l E X U) (f : A ⟶ B),
          a • f = (scalarDerived l E X U a).app A ≫ f) (linearInst := s) := by
  let := moduleLinear l E X U
  let s := Localization.linear (Padic.coefficientExtensionIntegers l E)
    (DerivedCategory.Q : Cx l E X U ⥤ D l E X U)
    (HomologicalComplex.quasiIso (Mod l E X U) (.up ℤ))
  have hs : (fun [_linearInst : Linear (Padic.coefficientExtensionIntegers l E)
      (D l E X U)] ↦
      ∀ (a : Padic.coefficientExtensionIntegers l E) (A B : D l E X U) (f : A ⟶ B),
        a • f = (scalarDerived l E X U a).app A ≫ f) (_linearInst := s) := by
    intro a A B f
    rw [scalarDerived_eq]
    rfl
  refine ⟨s, hs, ?_⟩
  intro t ht
  exact linear_ext t s (fun A B a f ↦ (ht a A B f).trans (hs a A B f).symm)

/-- Use the canonical constant-section linear structure, not an arbitrary scalar action.
Source: Stacks 05RR (blueprint: lem-sf-rational-thick-evaluation). -/
instance linear : Linear (Padic.coefficientExtensionIntegers l E) (D l E X U) :=
  (linear_existsUnique l E X U).exists.choose

/-- The opposite uses the same scalar action on reversed Hom modules.
Source: Stacks 08JC (blueprint: lem-sf-rational-thick-evaluation). -/
instance linearOpposite : Linear (Padic.coefficientExtensionIntegers l E) (D l E X U)ᵒᵖ where
  homModule A B := (opEquiv A B).module (Padic.coefficientExtensionIntegers l E)
  smul_comp A B C a f g := Quiver.Hom.unop_inj
    (Linear.comp_smul C.unop B.unop A.unop g.unop a f.unop)
  comp_smul A B C f a g := Quiver.Hom.unop_inj
    (Linear.smul_comp C.unop B.unop A.unop a g.unop f.unop)

/-- The canonical integer shifts preserve this coefficient action. Source: Stacks 05RR
(blueprint: lem-sf-rational-thick-evaluation).
Proof: translation and its signed differential commute with scalar multiplication
in each degree; fully faithful localization of natural transformations gives the
same assertion on all derived maps. -/
theorem shift_linear (n : ℤ) :
    (shiftFunctor (D l E X U) n).Linear (Padic.coefficientExtensionIntegers l E) := by
  let := moduleLinear l E X U
  have hs : linear l E X U =
      Localization.linear (Padic.coefficientExtensionIntegers l E)
        (DerivedCategory.Q : Cx l E X U ⥤ D l E X U)
        (HomologicalComplex.quasiIso (Mod l E X U) (.up ℤ)) := by
    apply linear_ext
    intro A B a f
    rw [(linear_existsUnique l E X U).exists.choose_spec]
    rw [scalarDerived_eq]
    rfl
  rw [hs]
  let := Localization.linear (Padic.coefficientExtensionIntegers l E)
    (DerivedCategory.Q : Cx l E X U ⥤ D l E X U)
    (HomologicalComplex.quasiIso (Mod l E X U) (.up ℤ))
  let := Localization.functor_linear (Padic.coefficientExtensionIntegers l E)
    (DerivedCategory.Q : Cx l E X U ⥤ D l E X U)
    (HomologicalComplex.quasiIso (Mod l E X U) (.up ℤ))
  exact Shift.linear_of_localization (Padic.coefficientExtensionIntegers l E)
    (DerivedCategory.Q : Cx l E X U ⥤ D l E X U)
    (HomologicalComplex.quasiIso (Mod l E X U) (.up ℤ)) n

/-- The shifts use the preceding canonical linearity proof. Source: Stacks 05RR
(blueprint: lem-sf-rational-thick-evaluation). -/
instance shiftLinear (n : ℤ) :
    (shiftFunctor (D l E X U) n).Linear (Padic.coefficientExtensionIntegers l E) :=
  shift_linear l E X U n

/-- The coefficient sheaf in degree zero. Source: Stacks 08JD
(blueprint: lem-sf-rational-thick-evaluation). -/
def coefficient : D l E X U := ringedSiteDualityUnit (topology X U) (ring l E X U)

/-- Psi is actual derived internal Hom with fixed second argument. Source: Stacks 08J7
(blueprint: lem-sf-rational-thick-evaluation). -/
def psi (M : D l E X U) : (D l E X U)ᵒᵖ ⥤ D l E X U :=
  (Functor.curry.obj (hom l E X U)).flip.obj M

/-- Ordinary dual tensor M before completing. Source: Stacks 08JE
(blueprint: lem-sf-rational-thick-evaluation). -/
def ordinaryPhi (M : D l E X U) : (D l E X U)ᵒᵖ ⥤ D l E X U :=
  psi l E X U (coefficient l E X U) ⋙
    Prod.sectL (D l E X U) M ⋙ (duality l E X U).closed.tensor

/-- Phi is completed dual tensor M. Source: Bhatt--Scholze, Definition 3.4.10
(blueprint: lem-sf-rational-thick-evaluation). -/
def phi (M : D l E X U) : (D l E X U)ᵒᵖ ⥤ D l E X U :=
  psi l E X U (coefficient l E X U) ⋙
    Prod.sectL (D l E X U) M ⋙ completedTensor l E X U

/-- The actual ordinary adjunct of evaluation, with the Koszul symmetry in the node's order.
Source: Stacks 08JD, 08JE (blueprint: lem-sf-rational-thick-evaluation). -/
def ordinaryEvaluation (L M : D l E X U) :
    (ordinaryPhi l E X U M).obj (op L) ⟶ (psi l E X U M).obj (op L) :=
  ringedSiteDualEvaluationLeft (duality l E X U).closed (duality l E X U).symmetric
    (coefficient l E X U) (duality l E X U).unitIso L M

/-- The scalar localization uses the specified coefficient ring and uniformizer.
Source: blueprint, sk-def-sf-operations (blueprint: lem-sf-rational-thick-evaluation). -/
abbrev Rational := ScalarLocalization (Padic.coefficientExtensionIntegers l E)
  (D l E X U) (Padic.coefficientExtensionUniformizer l E)

/-- The actual tensor-with-one localization functor. Source: blueprint, sk-def-sf-operations
(blueprint: lem-sf-rational-thick-evaluation). -/
abbrev q : D l E X U ⥤ Rational l E X U :=
  ScalarLocalization.localization (Padic.coefficientExtensionIntegers l E)
    (D l E X U) (Padic.coefficientExtensionUniformizer l E)

/-- Membership tests the actual localized evaluation component on the unchanged object.
Source: blueprint, sk-prop-sf-dualizable-biduality
(blueprint: lem-sf-rational-thick-evaluation). -/
def evaluationLocus (M : D l E X U) (α : phi l E X U M ⟶ psi l E X U M) :
    ObjectProperty (Rational l E X U) :=
  fun L ↦ IsIso ((q l E X U).map (α.app (op L.obj)))

end WeilConjectures.IntegralOnSlice
