/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G1
-/
module

public import Sheaf.NumberTheory.Padics.CoefficientExtension
public import Sheaf.NumberTheory.Padics.FiniteCoefficientFields
public import WeilConjectures.ConstructibleSheaf.Defs
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Point.Basic
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.ConcreteCoefficients
public import Mathlib.CategoryTheory.Linear.FunctorCategory
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Limits
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.CategoryTheory.Sites.Monoidal
public import Mathlib.CategoryTheory.Monoidal.FunctorCategory
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import WeilConjectures.Algebra.Category.ModuleCat.RingScalarExtension
public import Mathlib.CategoryTheory.Sites.Point.Basic
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Mathlib.CategoryTheory.Bicategory.Grothendieck
public import Mathlib.CategoryTheory.Localization.Construction
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
import WeilConjectures.ConstructibleSheaf.InternalHom
import WeilConjectures.Mathlib.CategoryTheory.Sites.Point.ConstantSheaf
import Mathlib.LinearAlgebra.TensorProduct.RightExactness

/-! # Lisse adic sheaves

Source: Deligne, Weil II, (0.1), (1.1.1) b)-d), pp. 144, 146-147
(blueprint: def-pod-lisse-l-adic-sheaves).

## Main definitions

* `LisseIntegralSheaf`: finite locally constant compatible coefficient systems.
* `LisseRationalSheaf`: integral models with rationalized morphisms.
* `lisseIntegralScalarExtension` and `lisseRationalScalarExtension`: coefficient extension.
* `LisseAlgebraicSheaf`: the coefficient-category 2-colimit.
* The `lisseIntegral`, `lisseRational` and `lisseAlgebraic` fibre, tensor and unit constructions.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite

noncomputable section

namespace AlgebraicGeometry.Scheme

attribute [local irreducible] GrothendieckTopology.Point.sheafFiber

private theorem tensorComposition_exists {R A : Type*} [CommRing R] [CommRing A]
    [Algebra R A] (C : Type*) [Category C] [Preadditive C] [Linear R C] :
    ∃ c : ∀ F G H : C, TensorProduct R A (F ⟶ G) →ₗ[A]
        TensorProduct R A (G ⟶ H) →ₗ[A] TensorProduct R A (F ⟶ H),
      (∀ (F G H : C) (a b : A) (f : F ⟶ G) (g : G ⟶ H),
        c F G H (TensorProduct.tmul R a f) (TensorProduct.tmul R b g) =
          TensorProduct.tmul R (a * b) (f ≫ g)) ∧
      (∀ (F G : C) (f : TensorProduct R A (F ⟶ G)),
        c F F G (TensorProduct.tmul R 1 (𝟙 F)) f = f) ∧
      (∀ (F G : C) (f : TensorProduct R A (F ⟶ G)),
        c F G G f (TensorProduct.tmul R 1 (𝟙 G)) = f) ∧
      (∀ (F G H K : C) (f : TensorProduct R A (F ⟶ G))
        (g : TensorProduct R A (G ⟶ H)) (h : TensorProduct R A (H ⟶ K)),
        c F H K (c F G H f g) h = c F G K f (c G H K g h)) := by
  let c (F G H : C) :
      TensorProduct R A (F ⟶ G) →ₗ[A]
        TensorProduct R A (G ⟶ H) →ₗ[A] TensorProduct R A (F ⟶ H) :=
    TensorProduct.AlgebraTensorModule.lift
      (LinearMap.mk₂' A R
        (fun a f ↦ a • ((LinearMap.baseChangeHom R A _ _).comp
          (Linear.comp F G H)) f)
        (by intros; exact add_smul _ _ _)
        (by intro a b f; exact mul_smul a b _)
        (by intros; rw [map_add, smul_add])
        (by intros; rw [map_smul]; exact smul_comm _ _ _))
  have ct (F G H : C) (a b : A)
      (f : F ⟶ G) (g : G ⟶ H) :
      c F G H (TensorProduct.tmul R a f) (TensorProduct.tmul R b g) =
        TensorProduct.tmul R (a * b) (f ≫ g) := by
    change a • (TensorProduct.tmul R b (f ≫ g)) = _
    rw [TensorProduct.smul_tmul', smul_eq_mul]
  refine ⟨c, ct, ?_, ?_, ?_⟩
  · intro F G f
    induction f using TensorProduct.induction_on with
    | zero => exact map_zero _
    | tmul a f => rw [ct, one_mul, Category.id_comp]
    | add f g hf hg => rw [map_add, hf, hg]
  · intro F G f
    induction f using TensorProduct.induction_on with
    | zero => rw [map_zero, LinearMap.zero_apply]
    | tmul a f => rw [ct, mul_one, Category.comp_id]
    | add f g hf hg => rw [map_add, LinearMap.add_apply, hf, hg]
  · intro F G H K f g h
    induction f using TensorProduct.induction_on with
    | zero => simp only [map_zero, LinearMap.zero_apply]
    | tmul a f =>
      induction g using TensorProduct.induction_on with
      | zero => simp only [map_zero, LinearMap.zero_apply]
      | tmul b g =>
        induction h using TensorProduct.induction_on with
        | zero => simp only [map_zero]
        | tmul d h => rw [ct, ct, ct, ct, mul_assoc, Category.assoc]
        | add h k hh hk => simp only [map_add, hh, hk]
      | add g h hg hh =>
        simp only [map_add, LinearMap.add_apply, hg, hh]
    | add f g hf hg => simp only [map_add, LinearMap.add_apply, hf, hg]


private theorem tensor_transition_kernel {R : Type*} [CommRing R]
    {M N M' N' : Type*} [AddCommGroup M] [AddCommGroup N]
    [AddCommGroup M'] [AddCommGroup N'] [Module R M] [Module R N]
    [Module R M'] [Module R N'] (I : Ideal R) (f : M →ₗ[R] M') (g : N →ₗ[R] N')
    (hf : Function.Surjective f) (hg : Function.Surjective g)
    (hkf : LinearMap.ker f = I • ⊤) (hkg : LinearMap.ker g = I • ⊤) :
    Function.Surjective (TensorProduct.map f g) ∧
      LinearMap.ker (TensorProduct.map f g) = I • ⊤ := by
  constructor
  · exact TensorProduct.map_surjective hf hg
  · rw [TensorProduct.map_ker f.exact_subtype_ker_map hf g.exact_subtype_ker_map hg]
    apply le_antisymm
    · apply sup_le
      · rintro _ ⟨z, rfl⟩
        induction z using TensorProduct.induction_on with
        | zero => simpa only [map_zero] using (I • (⊤ : Submodule R (TensorProduct R M N))).zero_mem
        | tmul x y =>
          change TensorProduct.tmul R x y.val ∈ I • ⊤
          have hy : y.val ∈ I • (⊤ : Submodule R N) := by
            rw [← hkg]; exact y.property
          refine Submodule.smul_induction_on hy ?_ ?_
          · intro a ha y _
            rw [← TensorProduct.smul_tmul, ← TensorProduct.smul_tmul']
            exact Submodule.smul_mem_smul ha Submodule.mem_top
          · intro y z hy hz
            rw [TensorProduct.tmul_add]
            exact Submodule.add_mem _ hy hz
        | add x y hx hy =>
          rw [map_add]
          exact Submodule.add_mem _ hx hy
      · rintro _ ⟨z, rfl⟩
        induction z using TensorProduct.induction_on with
        | zero => simpa only [map_zero] using (I • (⊤ : Submodule R (TensorProduct R M N))).zero_mem
        | tmul x y =>
          change TensorProduct.tmul R x.val y ∈ I • ⊤
          have hx : x.val ∈ I • (⊤ : Submodule R M) := by
            rw [← hkf]; exact x.property
          refine Submodule.smul_induction_on hx ?_ ?_
          · intro a ha x _
            rw [← TensorProduct.smul_tmul']
            exact Submodule.smul_mem_smul ha Submodule.mem_top
          · intro x z hx hz
            rw [TensorProduct.add_tmul]
            exact Submodule.add_mem _ hx hz
        | add x y hx hy =>
          rw [map_add]
          exact Submodule.add_mem _ hx hy
    · apply Submodule.smul_le.mpr
      intro a ha z hz
      clear hz
      induction z using TensorProduct.induction_on with
      | zero => rw [smul_zero]; exact Submodule.zero_mem _
      | tmul x y =>
        refine (le_sup_right : (LinearMap.rTensor N f.ker.subtype).range ≤ _) ?_
        refine ⟨TensorProduct.tmul R ⟨a • x, ?_⟩ y, ?_⟩
        · rw [hkf]
          exact Submodule.smul_mem_smul ha Submodule.mem_top
        · exact (TensorProduct.smul_tmul' a x y).symm
      | add x y hx hy =>
        rw [smul_add]
        exact Submodule.add_mem _ hx hy

private theorem quotientFactor_id {R : Type*} [CommRing R] (I : Ideal R) :
    (Ideal.Quotient.factorₐ R (le_refl I)).toLinearMap = LinearMap.id := by
  apply LinearMap.ext
  intro x
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
  rfl

private theorem quotientFactor_comp {R : Type*} [CommRing R]
    (I J K : Ideal R) (h : I ≤ J) (k : J ≤ K) :
    (Ideal.Quotient.factorₐ R (h.trans k)).toLinearMap =
      (Ideal.Quotient.factorₐ R k).toLinearMap.comp
        (Ideal.Quotient.factorₐ R h).toLinearMap := by
  apply LinearMap.ext
  intro x
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
  rfl

private theorem quotientFactor_kernel {R : Type*} [CommRing R]
    (I J : Ideal R) (h : J ≤ I) :
    LinearMap.ker (Ideal.Quotient.factorₐ R h).toLinearMap =
      I • (⊤ : Submodule R (R ⧸ J)) := by
  apply le_antisymm
  · intro x hx
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
    have hr : r ∈ I := Ideal.Quotient.eq_zero_iff_mem.mp hx
    apply Submodule.map_le_smul_top I (Ideal.Quotient.mkₐ R J).toLinearMap
    exact ⟨r, hr, rfl⟩
  · apply Submodule.smul_le.mpr
    intro a ha x _
    change (Ideal.Quotient.factorₐ R h).toLinearMap (a • x) = 0
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (I.mul_mem_right r ha)

/-- Sheafification for module coefficients on the small étale site.
Source: Weil II (1.1.1), coefficient sheaves
(blueprint: def-pod-lisse-l-adic-sheaves). -/
local instance (priority := 100000) lisseModuleSheafify
    (Y : Scheme.{u}) (R : Type (u + 1)) [Ring R] :
    HasWeakSheafify Y.smallEtaleTopology (ModuleCat.{u + 1} R) :=
  (GrothendieckTopology.hasSheafify_smallEtaleTopology
    (ModuleCat.{u + 1} R) Y).isRightAdjoint

/-- Lisse finite-ring module sheaves are finite locally constant module sheaves.
Source: Weil II (1.1.1) a), b) (blueprint: def-pod-lisse-l-adic-sheaves). -/
abbrev LisseFiniteModuleSheaf (Y : Scheme.{u}) (A : Type (u + 1)) [Ring A] [Finite A] :=
  ObjectProperty.FullSubcategory
    (fun F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A) =>
      IsFiniteLocallyConstantSheaf F)

variable (l : ℕ) [Fact l.Prime] (E : Type (u + 1)) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (Y : Scheme.{u})

/-- The inverse diagrams of sheaves of `𝒪_E`-modules, indexed by `n + 1`.
Source: Weil II (1.1.1) b) (blueprint: def-pod-lisse-l-adic-sheaves). -/
abbrev AdicIntegralDiagram :=
  ℕᵒᵖ ⥤ Sheaf Y.smallEtaleTopology
    (ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l E))

/-- A lisse integral system: each level is finite locally constant, killed by
`I^(n+1)` for `I = (ϖ_E)`, and on every geometric stalk the transition is surjective with
kernel `I^(n+1)` times the source, in the adic-limit form of lem-pod-adic-limit-finite-modules.
The last condition is tested on all geometric stalks, which form a conservative
family of exact functors. It is the reduction-isomorphism clause of Weil II (1.1.1) b).
Source: Weil II (1.1.1) b) (blueprint: def-pod-lisse-l-adic-sheaves). -/
def IsLisseIntegralDiagram (F : AdicIntegralDiagram l E Y) : Prop :=
  let R := Padic.coefficientExtensionIntegers l E
  let I := Ideal.span ({Padic.coefficientExtensionUniformizer l E} : Set R)
  (∀ n : ℕ, IsFiniteLocallyConstantSheaf (F.obj (op n))) ∧
  (∀ n : ℕ, ∀ U : Y.Etale,
    I ^ (n + 1) • (⊤ : Submodule R ((F.obj (op n)).obj.obj (op U))) = ⊥) ∧
  ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ Y) (n : ℕ),
    let T := (pointSmallEtale y).ulift.{u + 1}.sheafFiber (A := ModuleCat.{u + 1} R)
    let t := (T.map (F.map (homOfLE (Nat.le_succ n)).op)).hom
    Function.Surjective t ∧
      LinearMap.ker t = I ^ (n + 1) • (⊤ : Submodule R (T.obj (F.obj (op (n + 1)))))

/-- The category of lisse `𝒪_E`-sheaves. Morphisms are natural transformations,
hence exactly the compatible families of coefficient-linear maps.
Source: Weil II (1.1.1) b) (blueprint: def-pod-lisse-l-adic-sheaves). -/
abbrev LisseIntegralSheaf [IsNoetherian Y] [Y.IsSeparated]
    [∀ x : Y, Invertible (l : Y.residueField x)] :=
  ObjectProperty.FullSubcategory (IsLisseIntegralDiagram l E Y)

variable [IsNoetherian Y] [Y.IsSeparated] [∀ x : Y, Invertible (l : Y.residueField x)]

local instance (priority := 10000) lisseIntegralPreadditive :
    Preadditive (LisseIntegralSheaf l E Y) := inferInstance

local instance (priority := 10000) lisseIntegralLinear :
    Linear (Padic.coefficientExtensionIntegers l E) (LisseIntegralSheaf l E Y) :=
  inferInstance

/-- Cache the additive integral Hom structure inherited from module sheaves.
Source: Weil II (1.1.1) c) (blueprint: def-pod-lisse-l-adic-sheaves). -/
local instance (priority := 10000) lisseIntegralHomAddCommGroup
    (F G : LisseIntegralSheaf l E Y) : AddCommGroup (F ⟶ G) := inferInstance

/-- Cache the integral Hom module structure inherited from module sheaves.
Source: Weil II (1.1.1) c) (blueprint: def-pod-lisse-l-adic-sheaves). -/
local instance (priority := 10000) lisseIntegralHomModule
    (F G : LisseIntegralSheaf l E Y) :
    Module (Padic.coefficientExtensionIntegers l E) (F ⟶ G) := inferInstance

/-- The integral fibre is the inverse limit of the geometric stalks.
Source: Weil II (1.1.1) b), SGA 5 VI (1.2.5)
(blueprint: def-pod-lisse-l-adic-sheaves). -/
def lisseIntegralFiber {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (y : Spec (.of Ω) ⟶ Y) (F : LisseIntegralSheaf l E Y) :
    ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l E) :=
  limit (F.obj ⋙ (pointSmallEtale y).ulift.{u + 1}.sheafFiber)

/-- An `E`-sheaf is an integral lattice considered up to rational morphisms.
Source: Weil II (1.1.1) c) (blueprint: def-pod-lisse-l-adic-sheaves). -/
structure LisseRationalSheaf where
  /-- Its chosen integral model; different models may be isomorphic. -/
  integral : LisseIntegralSheaf l E Y

/-- Rational Hom, `E ⊗_{𝒪_E} Hom(F,G)`.
Source: Weil II (1.1.1) c) (blueprint: def-pod-lisse-l-adic-sheaves). -/
abbrev lisseRationalHom (F G : LisseRationalSheaf l E Y) :=
  TensorProduct (Padic.coefficientExtensionIntegers l E) E (F.integral ⟶ G.integral)

/-- The bilinear composition and its laws. All data are prescribed on pure tensors;
only verification of the laws is postponed in `lisseRationalComposition_exists`.
Source: Weil II (1.1.1) c) (blueprint: def-pod-lisse-l-adic-sheaves). -/
structure LisseRationalComposition where
  /-- The extension of integral composition by `E`-bilinearity. -/
  comp (F G H : LisseRationalSheaf l E Y) :
    lisseRationalHom l E Y F G →ₗ[E]
      lisseRationalHom l E Y G H →ₗ[E] lisseRationalHom l E Y F H
  /-- The defining pure-tensor formula. -/
  comp_tmul (F G H : LisseRationalSheaf l E Y) (a b : E)
      (f : F.integral ⟶ G.integral) (g : G.integral ⟶ H.integral) :
    comp F G H (TensorProduct.tmul _ a f) (TensorProduct.tmul _ b g) =
      TensorProduct.tmul _ (a * b) (f ≫ g)
  /-- Identity on the left. -/
  id_comp (F G : LisseRationalSheaf l E Y) (f : lisseRationalHom l E Y F G) :
    comp F F G (TensorProduct.tmul _ 1 (𝟙 F.integral)) f = f
  /-- Identity on the right. -/
  comp_id (F G : LisseRationalSheaf l E Y) (f : lisseRationalHom l E Y F G) :
    comp F G G f (TensorProduct.tmul _ 1 (𝟙 G.integral)) = f
  /-- Associativity. -/
  assoc (F G H K : LisseRationalSheaf l E Y)
      (f : lisseRationalHom l E Y F G) (g : lisseRationalHom l E Y G H)
      (h : lisseRationalHom l E Y H K) :
    comp F H K (comp F G H f g) h = comp F G K f (comp G H K g h)

/-- Rational composition exists and satisfies the category laws.
Source: Weil II (1.1.1) c) (blueprint: def-pod-lisse-l-adic-sheaves).
Proof: integral composition is `𝒪_E`-bilinear. Extend it using the balanced tensor
universal property twice, prescribing `(a ⊗ f, b ⊗ g) ↦ ab ⊗ (f ≫ g)`.
The balancing identities follow from scalar-linear integral composition; the category
laws follow on pure tensors from the integral laws and associativity of field multiplication,
and hence hold everywhere by tensor induction and bilinearity. -/
theorem lisseRationalComposition_exists : Nonempty (LisseRationalComposition l E Y) := by
  obtain ⟨c, ht, hi, hc, ha⟩ := tensorComposition_exists
    (R := Padic.coefficientExtensionIntegers l E) (A := E) (LisseIntegralSheaf l E Y)
  exact ⟨{ comp F G H := c F.integral G.integral H.integral
           comp_tmul F G H := ht F.integral G.integral H.integral
           id_comp F G := hi F.integral G.integral
           comp_id F G := hc F.integral G.integral
           assoc F G H K := ha F.integral G.integral H.integral K.integral }⟩

/-- The unique bilinear composition with the prescribed pure-tensor formula.
Source: Weil II (1.1.1) c) (blueprint: def-pod-lisse-l-adic-sheaves). -/
@[irreducible]
def lisseRationalComposition : LisseRationalComposition l E Y :=
  Classical.choice (lisseRationalComposition_exists l E Y)

/-- The category with the stated rational Hom and induced composition.
Source: Weil II (1.1.1) c) (blueprint: def-pod-lisse-l-adic-sheaves). -/
instance lisseRationalCategory : Category (LisseRationalSheaf l E Y) where
  Hom := lisseRationalHom l E Y
  id F := TensorProduct.tmul _ 1 (𝟙 F.integral)
  comp {F G H} f g := (lisseRationalComposition l E Y).comp F G H f g
  id_comp := (lisseRationalComposition l E Y).id_comp _ _
  comp_id := (lisseRationalComposition l E Y).comp_id _ _
  assoc := (lisseRationalComposition l E Y).assoc _ _ _ _

/-- Rational Hom has its tensor-product additive group.
Source: Weil II (1.1.1) c) (blueprint: def-pod-lisse-l-adic-sheaves). -/
instance lisseRationalHomAddCommGroup (F G : LisseRationalSheaf l E Y) :
    AddCommGroup (F ⟶ G) := inferInstanceAs (AddCommGroup (lisseRationalHom l E Y F G))

/-- The rational fibre is `E ⊗_{𝒪_E} F_y`.
Source: Weil II (1.1.1) c), SGA 5 VI (1.2.5)
(blueprint: def-pod-lisse-l-adic-sheaves). -/
def lisseRationalFiber {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (y : Spec (.of Ω) ⟶ Y) (F : LisseRationalSheaf l E Y) : ModuleCat.{u + 1} E :=
  ModuleCat.of E (TensorProduct (Padic.coefficientExtensionIntegers l E) E
    (lisseIntegralFiber l E Y y F.integral))

-- Cache the sheaf Hom actions before the tensor proof, rather than repeatedly
-- unfolding the full-subcategory and presheaf linear-category instances.
local instance (priority := 10000) lisseSheafHomAddCommGroup
    {R : Type (u + 1)} [Ring R]
    (F G : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R)) :
    AddCommGroup (F ⟶ G) := inferInstance

local instance (priority := 10000) lisseSheafHomModule
    {R : Type (u + 1)} [CommRing R]
    (F G : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R)) :
    Module R (F ⟶ G) := inferInstance

section TensorConstruction

attribute [local instance] CategoryTheory.Sheaf.monoidalCategory
attribute [local instance] CategoryTheory.Sheaf.braidedCategory

set_option backward.isDefEq.respectTransparency false in
/-- Tensor of integral systems is lisse.
Source: Weil II (1.1.1) b), SGA 5 VI
(blueprint: def-pod-lisse-l-adic-sheaves).
Proof: tensor levelwise. At level n both factors are killed by `ϖ_E^(n+1)`, so tensor
 over `𝒪_E` agrees with tensor over the quotient `A_{E,n+1}`. On common local
trivializations the tensor is the constant tensor of finite modules. Right exactness of
scalar extension gives the reduction comparison at the next level. Thus the stalk
quotient condition and the annihilation condition are preserved. -/
theorem lisseIntegralTensor_isLisse (F G : LisseIntegralSheaf l E Y) :
    IsLisseIntegralDiagram l E Y (F.obj ⊗ G.obj) := by
  let R := Padic.coefficientExtensionIntegers l E
  let I := Ideal.span ({Padic.coefficientExtensionUniformizer l E} : Set R)
  refine ⟨?_, ?_, ?_⟩
  · intro n
    rw [CategoryTheory.Monoidal.tensorObj_obj]
    exact (F.property.1 n).tensorObj (G.property.1 n)
  · intro n U
    apply bot_unique
    apply Submodule.smul_le.mpr
    intro a ha x _
    change (F.obj.obj (op n) ⊗ G.obj.obj (op n)).obj.obj (op U) at x
    have hz : a • (𝟙 (F.obj.obj (op n))) = 0 := by
      apply Sheaf.hom_ext
      apply NatTrans.ext
      funext V
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro z
      exact (Submodule.mem_bot R).mp ((F.property.2.1 n V.unop) ▸
        Submodule.smul_mem_smul ha (Submodule.mem_top : z ∈ ⊤))
    have hz' : a • (𝟙 (F.obj.obj (op n) ⊗ G.obj.obj (op n))) = 0 := by
      rw [← MonoidalCategory.id_whiskerRight, ← MonoidalLinear.smul_whiskerRight,
        hz, MonoidalPreadditive.zero_whiskerRight]
    exact congrArg (fun f ↦ f.hom.app (op U) x) hz'
  · intro Ω _ _ y n
    let T := (pointSmallEtale y).ulift.{u + 1}.sheafFiber (A := ModuleCat.{u + 1} R)
    let f := F.obj.map (homOfLE (Nat.le_succ n)).op
    let g := G.obj.map (homOfLE (Nat.le_succ n)).op
    let e₁ := (Functor.Monoidal.μIso T (F.obj.obj (op (n + 1)))
      (G.obj.obj (op (n + 1)))).toLinearEquiv
    let e₂ := (Functor.Monoidal.μIso T (F.obj.obj (op n))
      (G.obj.obj (op n))).toLinearEquiv
    let t := (T.map ((F.obj ⊗ G.obj).map (homOfLE (Nat.le_succ n)).op)).hom
    let q := TensorProduct.map (T.map f).hom (T.map g).hom
    have hF := F.property.2.2 Ω y n
    have hG := G.property.2.2 Ω y n
    obtain ⟨hq, hk⟩ := tensor_transition_kernel (I ^ (n + 1))
      (T.map f).hom (T.map g).hom hF.1 hG.1 hF.2 hG.2
    have hn (x) : t (e₁ x) = e₂ (q x) := by
      dsimp only [t]
      rw [CategoryTheory.Monoidal.tensorObj_map]
      exact congrArg (fun f ↦ f x) (congrArg ModuleCat.Hom.hom
        (Functor.LaxMonoidal.μ_natural T f g)).symm
    constructor
    · intro x
      obtain ⟨z, hz⟩ := hq (e₂.symm x)
      refine ⟨e₁ z, ?_⟩
      rw [hn, hz, e₂.apply_symm_apply]
    · have he : (I ^ (n + 1) • (⊤ : Submodule R _)).comap
          e₁.symm.toLinearMap = I ^ (n + 1) • ⊤ := by
        rw [Submodule.comap_smul_top_of_surjective _ _ e₁.symm.surjective,
          LinearMap.ker_eq_bot.mpr e₁.symm.injective, sup_bot_eq]
      rw [← he, ← hk]
      ext x
      change t x = 0 ↔ q (e₁.symm x) = 0
      rw [← e₂.injective.eq_iff, map_zero, ← hn, e₁.apply_symm_apply]

/-- Levelwise tensor, with the tensor of transition maps.
Source: Weil II (1.1.1) b), SGA 5 VI
(blueprint: def-pod-lisse-l-adic-sheaves). -/
def lisseIntegralTensor (F G : LisseIntegralSheaf l E Y) : LisseIntegralSheaf l E Y :=
  ⟨F.obj ⊗ G.obj, lisseIntegralTensor_isLisse l E Y F G⟩

/-- Tensor of rational objects uses the tensor of their integral models.
Source: Weil II (1.1.1) c), SGA 5 VI
(blueprint: def-pod-lisse-l-adic-sheaves). -/
def lisseRationalTensor (F G : LisseRationalSheaf l E Y) : LisseRationalSheaf l E Y :=
  ⟨lisseIntegralTensor l E Y F.integral G.integral⟩

end TensorConstruction

/-- The quotient transition viewed as an `𝒪_E`-linear map, for any two levels.
Source: Weil II (1.1.1) b) (blueprint: def-pod-lisse-l-adic-sheaves). -/
def lisseUnitModuleMap (i j : ℕᵒᵖ) (f : i ⟶ j) :
    ModuleCat.of (Padic.coefficientExtensionIntegers l E)
      (Padic.coefficientExtensionRing l E (i.unop + 1)) ⟶
    ModuleCat.of (Padic.coefficientExtensionIntegers l E)
      (Padic.coefficientExtensionRing l E (j.unop + 1)) :=
  ModuleCat.ofHom (Ideal.Quotient.factorₐ (Padic.coefficientExtensionIntegers l E)
    (Ideal.pow_le_pow_right (Nat.add_le_add_right (leOfHom f.unop) 1))).toLinearMap

/-- The quotient maps preserve identities.
Source: Weil II (1.1.1) b) (blueprint: def-pod-lisse-l-adic-sheaves).
Proof: each factor map sends the class of a scalar to the same class; quotient classes
exhaust the quotient, so the map for the identity index map is the identity. -/
theorem lisseUnitModuleMap_id (i : ℕᵒᵖ) :
    lisseUnitModuleMap l E i i (𝟙 i) = 𝟙 _ := by
  apply ModuleCat.hom_ext
  exact quotientFactor_id _

/-- The quotient maps preserve composition.
Source: Weil II (1.1.1) b) (blueprint: def-pod-lisse-l-adic-sheaves).
Proof: both sides send the class of a scalar to its class in the final quotient.
Quotient classes exhaust the source quotient, so the maps agree. -/
theorem lisseUnitModuleMap_comp (i j k : ℕᵒᵖ) (f : i ⟶ j) (g : j ⟶ k) :
    lisseUnitModuleMap l E i k (f ≫ g) =
      lisseUnitModuleMap l E i j f ≫ lisseUnitModuleMap l E j k g := by
  apply ModuleCat.hom_ext
  exact quotientFactor_comp _ _ _
    (Ideal.pow_le_pow_right (Nat.add_le_add_right (leOfHom f.unop) 1))
    (Ideal.pow_le_pow_right (Nat.add_le_add_right (leOfHom g.unop) 1))

/-- The inverse diagram of constant coefficient sheaves.
Source: Weil II (1.1.1) b), SGA 5 VI
(blueprint: def-pod-lisse-l-adic-sheaves). -/
def lisseIntegralUnitDiagram : AdicIntegralDiagram l E Y :=
  (show ℕᵒᵖ ⥤ ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l E) from
    { obj i := ModuleCat.of _ (Padic.coefficientExtensionRing l E (i.unop + 1))
      map {i j} f := lisseUnitModuleMap l E i j f
      map_id := lisseUnitModuleMap_id l E
      map_comp := lisseUnitModuleMap_comp l E _ _ _ }) ⋙
        constantSheaf Y.smallEtaleTopology _

-- Keep the existing standing hypotheses of this public interface.
set_option linter.unusedSectionVars false in
/-- The constant coefficient system is lisse.
Source: Weil II (1.1.1) b), SGA 5 VI
(blueprint: def-pod-lisse-l-adic-sheaves).
Proof: each coefficient quotient is finite and is a constant module sheaf. It is killed
by the prescribed power of the uniformizer. The quotient map is surjective with kernel
generated by the indicated power; constant-sheaf stalks are the given modules. -/
theorem lisseIntegralUnit_isLisse :
    IsLisseIntegralDiagram l E Y (lisseIntegralUnitDiagram l E Y) := by
  let R := Padic.coefficientExtensionIntegers l E
  let I := Ideal.span ({Padic.coefficientExtensionUniformizer l E} : Set R)
  let Q (n : ℕ) := ModuleCat.of R (Padic.coefficientExtensionRing l E (n + 1))
  let C := constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R)
  refine ⟨?_, ?_, ?_⟩
  · intro n
    have hc : Sheaf.IsConstant Y.smallEtaleTopology (C.obj (Q n)) :=
      Sheaf.isConstant_of_iso _ (X := Q n) (Iso.refl _)
    have hf := isFiniteSheaf_constantSheaf (X := Y) (Q n)
    exact { toIsLocallyConstantSheaf := hc.isLocallyConstantSheaf
            toIsFiniteSheaf := hf }
  · intro n U
    apply bot_unique
    apply Submodule.smul_le.mpr
    intro a ha x _
    have hz : a • (𝟙 (Q n)) = 0 := by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro z
      change R ⧸ I ^ (n + 1) at z
      change (Ideal.Quotient.mk (I ^ (n + 1)) a) * z = 0
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr ha, zero_mul]
    have hz' : a • (𝟙 (C.obj (Q n))) = 0 := by
      rw [← C.map_id, ← Functor.map_smul, hz, C.map_zero]
    exact congrArg (fun f ↦ f.hom.app (op U) x) hz'
  · intro Ω _ _ y n
    let p := (pointSmallEtale y).ulift.{u + 1}
    let e₁ := (p.sheafFiberConstantSheafIso (Q (n + 1))).toLinearEquiv
    let e₂ := (p.sheafFiberConstantSheafIso (Q n)).toLinearEquiv
    let t := (p.sheafFiber.map
      ((lisseIntegralUnitDiagram l E Y).map (homOfLE (Nat.le_succ n)).op)).hom
    let q := (lisseUnitModuleMap l E (op (n + 1)) (op n)
      (homOfLE (Nat.le_succ n)).op).hom
    have hn (x) : e₂ (t x) = q (e₁ x) := by
      exact congrArg (fun f ↦ f x)
        (congrArg ModuleCat.Hom.hom (p.sheafFiberConstantSheafIso_hom_naturality
          (lisseUnitModuleMap l E (op (n + 1)) (op n)
            (homOfLE (Nat.le_succ n)).op)))
    constructor
    · intro x
      obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (e₂ x)
      refine ⟨e₁.symm (Ideal.Quotient.mk (I ^ (n + 2)) r), e₂.injective ?_⟩
      rw [hn, e₁.apply_symm_apply]
      exact hr
    · have hq : LinearMap.ker q = I ^ (n + 1) • (⊤ : Submodule R (Q (n + 1))) :=
        quotientFactor_kernel (I ^ (n + 1)) (I ^ (n + 2))
          (Ideal.pow_le_pow_right (Nat.le_succ (n + 1)))
      have he : (I ^ (n + 1) • (⊤ : Submodule R (Q (n + 1)))).comap
          e₁.toLinearMap = I ^ (n + 1) • ⊤ := by
        rw [Submodule.comap_smul_top_of_surjective _ _ e₁.surjective,
          LinearMap.ker_eq_bot.mpr e₁.injective, sup_bot_eq]
      rw [← he, ← hq]
      ext x
      change t x = 0 ↔ q (e₁ x) = 0
      rw [← e₂.injective.eq_iff, map_zero, hn]

/-- The tensor unit, the constant coefficient system.
Source: Weil II (1.1.1) b), SGA 5 VI
(blueprint: def-pod-lisse-l-adic-sheaves). -/
def lisseIntegralUnit : LisseIntegralSheaf l E Y :=
  ⟨lisseIntegralUnitDiagram l E Y, lisseIntegralUnit_isLisse l E Y⟩

/-- The rational tensor unit is the rationalization of the constant coefficient system.
Source: Weil II (1.1.1) c), SGA 5 VI
(blueprint: def-pod-lisse-l-adic-sheaves). -/
def lisseRationalUnit : LisseRationalSheaf l E Y := ⟨lisseIntegralUnit l E Y⟩

section ScalarExtension

variable (L : Type (u + 1)) [Field L] [Algebra ℚ_[l] L]
  [FiniteDimensional ℚ_[l] L] (ι : E →ₐ[ℚ_[l]] L)

/-- A field inclusion induces the inclusion of rings of integers.
Source: Weil II (1.1.1) d), SGA 5 VI
(blueprint: def-pod-lisse-l-adic-sheaves).
Proof: uniqueness of the extended absolute value shows that `ι` preserves absolute
values. It therefore maps elements of absolute value at most one into the ring of
integers. Restrict the field homomorphism to these subrings; the displayed equality
characterizes that restriction uniquely. -/
theorem lisseIntegerInclusion_exists :
    ∃ f : Padic.coefficientExtensionIntegers l E →+*
      Padic.coefficientExtensionIntegers l L, ∀ x, (f x : L) = ι (x : E) := by
  have hE := (Padic.extension_integers_dvr l E (Padic.coefficientExtensionAbsoluteValue l E)
    (spectralNorm_extends (K := ℚ_[l]) (L := E))).choose_spec.choose_spec.1
  have hL := (Padic.extension_integers_dvr l L (Padic.coefficientExtensionAbsoluteValue l L)
    (spectralNorm_extends (K := ℚ_[l]) (L := L))).choose_spec.choose_spec.1
  have hmap (a : E) : spectralNorm ℚ_[l] L (ι a) = spectralNorm ℚ_[l] E a := by
    unfold spectralNorm
    rw [minpoly.algHom_eq ι ι.injective]
  let f : Padic.coefficientExtensionIntegers l E →+*
      Padic.coefficientExtensionIntegers l L :=
    { toFun := fun x ↦ ⟨ι (x : E), by
        apply (hL _).mpr
        change spectralNorm ℚ_[l] L (ι (x : E)) ≤ 1
        rw [hmap]
        exact (hE _).mp x.property⟩
      map_one' := Subtype.ext (map_one ι)
      map_mul' x y := Subtype.ext (map_mul ι (x : E) (y : E))
      map_zero' := Subtype.ext (map_zero ι)
      map_add' x y := Subtype.ext (map_add ι (x : E) (y : E)) }
  exact ⟨f, fun _ ↦ rfl⟩

/-- Restriction of the given field inclusion to the rings of integers.
Source: Weil II (1.1.1) d) (blueprint: def-pod-lisse-l-adic-sheaves). -/
def lisseIntegerInclusion : Padic.coefficientExtensionIntegers l E →+*
    Padic.coefficientExtensionIntegers l L :=
  (lisseIntegerInclusion_exists l E L ι).choose

/-- The positive ramification index is characterized by the image of the maximal ideal.
Source: Weil II (1.1.1) d), local-field scalar extension, SGA 5 VI
(blueprint: def-pod-lisse-l-adic-sheaves).
Proof: both rings of integers are discrete valuation rings. The inclusion maps the
nonzero maximal ideal to a nonzero proper ideal of the larger ring. Every such ideal
is a unique positive power of its maximal ideal; its exponent is the ramification index. -/
theorem lisseRamificationIndex_exists :
    ∃ e : ℕ, 0 < e ∧
      Ideal.map (lisseIntegerInclusion l E L ι) (Padic.coefficientExtensionMaximalIdeal l E) =
        Padic.coefficientExtensionMaximalIdeal l L ^ e := by
  have hE := (Padic.extension_integers_dvr l E (Padic.coefficientExtensionAbsoluteValue l E)
    (spectralNorm_extends (K := ℚ_[l]) (L := E))).choose_spec.choose_spec
  have hL := (Padic.extension_integers_dvr l L (Padic.coefficientExtensionAbsoluteValue l L)
    (spectralNorm_extends (K := ℚ_[l]) (L := L))).choose_spec.choose_spec
  rcases hE with ⟨_, hmE, _, _, _, _, _, _, _, hneE, _⟩
  rcases hL with ⟨_, hmL, _, _, hmaxL, _, _, hdvrL, _⟩
  have : IsDiscreteValuationRing (Padic.coefficientExtensionIntegers l L) := hdvrL
  have hi (x : Padic.coefficientExtensionIntegers l E) :
      (lisseIntegerInclusion l E L ι x : L) = ι (x : E) :=
    (lisseIntegerInclusion_exists l E L ι).choose_spec x
  have hinj : Function.Injective (lisseIntegerInclusion l E L ι) := by
    intro x y h
    apply Subtype.ext
    apply ι.injective
    have hc := congrArg
      (fun z : Padic.coefficientExtensionIntegers l L ↦ (z : L)) h
    exact (hi x).symm.trans (hc.trans (hi y))
  have hne : Ideal.map (lisseIntegerInclusion l E L ι)
      (Padic.coefficientExtensionMaximalIdeal l E) ≠ ⊥ :=
    (Ideal.map_eq_bot_iff_of_injective hinj).not.mpr hneE
  have hle : Ideal.map (lisseIntegerInclusion l E L ι)
      (Padic.coefficientExtensionMaximalIdeal l E) ≤
        Padic.coefficientExtensionMaximalIdeal l L := by
    apply Ideal.map_le_iff_le_comap.mpr
    intro x hx
    apply (hmL _).mpr
    change spectralNorm ℚ_[l] L _ < 1
    rw [hi]
    have heq : spectralNorm ℚ_[l] L (ι (x : E)) = spectralNorm ℚ_[l] E (x : E) := by
      unfold spectralNorm
      rw [minpoly.algHom_eq ι ι.injective]
    rw [heq]
    exact (hmE _).mp hx
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible
    (Padic.coefficientExtensionIntegers l L)
  obtain ⟨e, he⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible hne hπ
  have hmax : Padic.coefficientExtensionMaximalIdeal l L =
      Ideal.span ({π} : Set (Padic.coefficientExtensionIntegers l L)) :=
    (IsLocalRing.eq_maximalIdeal hmaxL).trans hπ.maximalIdeal_eq
  refine ⟨e, ?_, ?_⟩
  · by_contra h
    have hz : e = 0 := by omega
    rw [he, hz, pow_zero, Ideal.span_singleton_one] at hle
    exact hmaxL.ne_top (top_le_iff.mp hle)
  · rw [hmax, Ideal.span_singleton_pow]
    exact he

/-- The ramification index of the coefficient inclusion.
Source: Weil II (1.1.1) d) (blueprint: def-pod-lisse-l-adic-sheaves). -/
def lisseRamificationIndex : ℕ := (lisseRamificationIndex_exists l E L ι).choose

/-- The source index, zero-based, corresponding to `ceil((m+1)/e)`.
Source: Weil II (1.1.1) d), scalar extension on cofinal systems
(blueprint: def-pod-lisse-l-adic-sheaves). -/
def lisseScalarSourceIndex (m : ℕ) : ℕ :=
  (m + 1 + lisseRamificationIndex l E L ι - 1) / lisseRamificationIndex l E L ι - 1

/-- The ceiling source index is nondecreasing.
Source: the ceiling formula in coefficient scalar extension, SGA 5 VI
(blueprint: def-pod-lisse-l-adic-sheaves).
Proof: the ramification index is positive; addition, division by a fixed positive
integer and truncated subtraction by one preserve order. Apply them to `m ≤ m+1`. -/
theorem lisseScalarSourceIndex_le (m : ℕ) :
    lisseScalarSourceIndex l E L ι m ≤ lisseScalarSourceIndex l E L ι (m + 1) := by
  unfold lisseScalarSourceIndex
  apply Nat.sub_le_sub_right
  apply Nat.div_le_div_right
  omega

/-- The scalar map to the target finite quotient.
Source: Weil II (1.1.1) d) (blueprint: def-pod-lisse-l-adic-sheaves). -/
def lisseScalarCoefficientMap (m : ℕ) : Padic.coefficientExtensionIntegers l E →+*
    Padic.coefficientExtensionRing l L (m + 1) :=
  (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l L (m + 1))).comp
    (lisseIntegerInclusion l E L ι)

/-- The level `F_n ⊗_{A_E,n} A_L,m`, as a sheaf of `𝒪_L`-modules.
Here `n = ceil(m/e)`; extending directly from `𝒪_E` gives the same balanced tensor
because `F_n` is killed by `ϖ_E^n` and `ϖ_E^n` maps to zero in `A_L,m`.
Source: Weil II (1.1.1) d), SGA 5 VI
(blueprint: def-pod-lisse-l-adic-sheaves). -/
def lisseIntegralScalarLevel (F : LisseIntegralSheaf l E Y) (m : ℕ) :
    Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l L)) :=
  (sheafCompose Y.smallEtaleTopology
    (ModuleCat.restrictScalars.{u + 1}
      (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l L (m + 1))))).obj
    ((Sheaf.ringExtendScalars.{u + 1, u + 1} Y.smallEtaleTopology
      (lisseScalarCoefficientMap l E L ι m)).obj
        (F.obj.obj (op (lisseScalarSourceIndex l E L ι m))))

/-- The local pure tensor generator in the scalar-extended finite level.
Source: Weil II (1.1.1) d), SGA 5 VI
(blueprint: def-pod-lisse-l-adic-sheaves). -/
def lisseIntegralScalarGenerator (F : LisseIntegralSheaf l E Y) (m : ℕ) (U : Y.Etale)
    (a : Padic.coefficientExtensionRing l L (m + 1))
    (s : (F.obj.obj (op (lisseScalarSourceIndex l E L ι m))).obj.obj (op U)) :
    (lisseIntegralScalarLevel l E Y L ι F m).obj.obj (op U) :=
  ((toSheafification Y.smallEtaleTopology
    (ModuleCat.{u + 1} (Padic.coefficientExtensionRing l L (m + 1)))).app
      ((F.obj.obj (op (lisseScalarSourceIndex l E L ι m))).obj ⋙
        ModuleCat.ringExtendScalars.{u + 1, u + 1}
          (lisseScalarCoefficientMap l E L ι m))).app (op U)
          (ModuleCat.ringExtensionTmul.{u + 1, u + 1}
            (lisseScalarCoefficientMap l E L ι m) _ a s)

/-- Scalar extension with its prescribed levels, transitions and action on morphisms.
The level identifications are module-sheaf isomorphisms, and all transition and morphism
maps are fixed by their action on the sheafification of pure tensors.
Source: Weil II (1.1.1) d), SGA 5 VI
(blueprint: def-pod-lisse-l-adic-sheaves). -/
structure LisseIntegralScalarExtensionData where
  /-- The functor on integral systems. -/
  functor : LisseIntegralSheaf l E Y ⥤ LisseIntegralSheaf l L Y
  /-- The displayed finite-level formula. -/
  levelIso (F : LisseIntegralSheaf l E Y) (m : ℕ) :
    (functor.obj F).obj.obj (op m) ≅ lisseIntegralScalarLevel l E Y L ι F m
  /-- Transition maps are induced by the coefficient and source transition maps. -/
  transition (F : LisseIntegralSheaf l E Y) (m : ℕ) (U : Y.Etale)
      (a : Padic.coefficientExtensionRing l L (m + 2))
      (s : (F.obj.obj (op (lisseScalarSourceIndex l E L ι (m + 1)))).obj.obj (op U)) :
    (levelIso F m).hom.hom.app (op U)
      (((functor.obj F).obj.map (homOfLE (Nat.le_succ m)).op).hom.app (op U)
        ((levelIso F (m + 1)).inv.hom.app (op U)
          (lisseIntegralScalarGenerator l E Y L ι F (m + 1) U a s))) =
      lisseIntegralScalarGenerator l E Y L ι F m U
        (Padic.coefficientExtensionTransition l L (m + 1) a)
        ((F.obj.map (homOfLE (lisseScalarSourceIndex_le l E L ι m)).op).hom.app (op U) s)
  /-- The map of a morphism is the scalar extension of each of its levels. -/
  map (F G : LisseIntegralSheaf l E Y) (f : F ⟶ G) (m : ℕ) (U : Y.Etale)
      (a : Padic.coefficientExtensionRing l L (m + 1))
      (s : (F.obj.obj (op (lisseScalarSourceIndex l E L ι m))).obj.obj (op U)) :
    (levelIso G m).hom.hom.app (op U)
      (((functor.map f).hom.app (op m)).hom.app (op U)
        ((levelIso F m).inv.hom.app (op U)
          (lisseIntegralScalarGenerator l E Y L ι F m U a s))) =
      lisseIntegralScalarGenerator l E Y L ι G m U a
        ((f.hom.app (op (lisseScalarSourceIndex l E L ι m))).hom.app (op U) s)

/-- The prescribed scalar extension exists.
Source: Weil II (1.1.1) d), SGA 5 VI
(blueprint: def-pod-lisse-l-adic-sheaves).
Proof: set each finite level equal to the displayed balanced tensor followed by
sheafification. Since `e ceil(m/e) ≥ m`, the coefficient map kills the source
annihilator. The source transition and coefficient quotient maps induce the displayed
maps on pure tensors. Balancing and naturality give module-sheaf maps, which extend
uniquely through sheafification. Successive scalar extensions and reduction commute by
tensor associativity, giving the reduction isomorphism. Common trivializations show
lissity. The same formula on morphisms commutes with transitions and preserves
identities and composition on pure tensors; uniqueness proves the functor laws. -/
theorem lisseIntegralScalarExtension_exists :
    Nonempty (LisseIntegralScalarExtensionData l E Y L ι) := by
  sorry

/-- The integral coefficient extension functor, with precisely the finite-level formula.
Source: Weil II (1.1.1) d) (blueprint: def-pod-lisse-l-adic-sheaves). -/
@[irreducible]
def lisseIntegralScalarExtensionData : LisseIntegralScalarExtensionData l E Y L ι :=
  Classical.choice (lisseIntegralScalarExtension_exists l E Y L ι)

/-- Scalar extension `F ↦ F ⊗_{𝒪_E} 𝒪_L`.
Source: Weil II (1.1.1) d) (blueprint: def-pod-lisse-l-adic-sheaves). -/
@[irreducible]
def lisseIntegralScalarExtension : LisseIntegralSheaf l E Y ⥤ LisseIntegralSheaf l L Y :=
  (lisseIntegralScalarExtensionData l E Y L ι).functor

/-- The rational scalar-extension maps are additive and prescribed on pure tensors.
Source: Weil II (1.1.1) c), d) (blueprint: def-pod-lisse-l-adic-sheaves). -/
structure LisseRationalScalarExtensionData where
  /-- Extend every morphism's scalar coefficient and integral map. -/
  map (F G : LisseRationalSheaf l E Y) : lisseRationalHom l E Y F G →
    lisseRationalHom l L Y
      ⟨(lisseIntegralScalarExtension l E Y L ι).obj F.integral⟩
      ⟨(lisseIntegralScalarExtension l E Y L ι).obj G.integral⟩
  /-- Additivity fixes the map on sums of pure tensors. -/
  map_add (F G : LisseRationalSheaf l E Y) (f g : lisseRationalHom l E Y F G) :
    map F G (f + g) = map F G f + map F G g
  /-- The defining pure tensor formula. -/
  map_tmul (F G : LisseRationalSheaf l E Y) (a : E) (f : F.integral ⟶ G.integral) :
    map F G (TensorProduct.tmul _ a f) =
      TensorProduct.tmul _ (ι a) ((lisseIntegralScalarExtension l E Y L ι).map f)
  /-- Identity preservation. -/
  map_id (F : LisseRationalSheaf l E Y) :
    map F F (TensorProduct.tmul _ 1 (𝟙 F.integral)) =
    TensorProduct.tmul _ 1 (𝟙 ((lisseIntegralScalarExtension l E Y L ι).obj F.integral))
  /-- Composition preservation. -/
  map_comp (F G H : LisseRationalSheaf l E Y)
      (f : lisseRationalHom l E Y F G) (g : lisseRationalHom l E Y G H) :
    map F H ((lisseRationalComposition l E Y).comp F G H f g) =
      (lisseRationalComposition l L Y).comp
        ⟨(lisseIntegralScalarExtension l E Y L ι).obj F.integral⟩
        ⟨(lisseIntegralScalarExtension l E Y L ι).obj G.integral⟩
        ⟨(lisseIntegralScalarExtension l E Y L ι).obj H.integral⟩
        (map F G f) (map G H g)

set_option maxRecDepth 100 in
private def quotientRestrictedHom {S A : Type (u + 1)} [CommRing S] [CommRing A]
    (q : S →+* A) (hq : Function.Surjective q) (M N : ModuleCat.{u + 1} A)
    (f : (ModuleCat.restrictScalars.{u + 1} q).obj M ⟶
      (ModuleCat.restrictScalars.{u + 1} q).obj N) :
    M ⟶ N :=
  ModuleCat.ofHom (X := M) (Y := N)
    { toFun := f
      map_add' := f.hom.map_add
      map_smul' := by
        intro a x
        obtain ⟨b, rfl⟩ := hq a
        exact f.hom.map_smul b x }

set_option maxRecDepth 100 in
private def quotientRestrictedSheafHom {S A : Type (u + 1)} [CommRing S] [CommRing A]
    (q : S →+* A) (hq : Function.Surjective q)
    (M N : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A))
    (f : (sheafCompose Y.smallEtaleTopology (ModuleCat.restrictScalars.{u + 1} q)).obj M ⟶
      (sheafCompose Y.smallEtaleTopology (ModuleCat.restrictScalars.{u + 1} q)).obj N) : M ⟶ N :=
  ⟨{ app U := quotientRestrictedHom q hq _ _ (f.hom.app U)
     naturality U V v := by
       apply ModuleCat.hom_ext
       apply LinearMap.ext
       intro x
       exact congrArg (fun h ↦ h x) (congrArg ModuleCat.Hom.hom (f.hom.naturality v)) }⟩

set_option maxRecDepth 100 in
private theorem scalarLevel_hom_ext (F G : LisseIntegralSheaf l E Y) (m : ℕ)
    (f g : lisseIntegralScalarLevel l E Y L ι F m ⟶
      lisseIntegralScalarLevel l E Y L ι G m)
    (h : ∀ (U : Y.Etale) (a : Padic.coefficientExtensionRing l L (m + 1))
      (s : (F.obj.obj (op (lisseScalarSourceIndex l E L ι m))).obj.obj (op U)),
      f.hom.app (op U) (lisseIntegralScalarGenerator l E Y L ι F m U a s) =
        g.hom.app (op U) (lisseIntegralScalarGenerator l E Y L ι F m U a s)) : f = g := by
  let q := Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l L (m + 1))
  let r := lisseScalarCoefficientMap l E L ι m
  let EF := ModuleCat.ringExtendScalars.{u + 1, u + 1} r
  let P := (F.obj.obj (op (lisseScalarSourceIndex l E L ι m))).obj ⋙ EF
  let Q := (G.obj.obj (op (lisseScalarSourceIndex l E L ι m))).obj ⋙ EF
  let f' := quotientRestrictedSheafHom Y q Ideal.Quotient.mk_surjective
    ((presheafToSheaf Y.smallEtaleTopology _).obj P)
    ((presheafToSheaf Y.smallEtaleTopology _).obj Q) f
  let g' := quotientRestrictedSheafHom Y q Ideal.Quotient.mk_surjective
    ((presheafToSheaf Y.smallEtaleTopology _).obj P)
    ((presheafToSheaf Y.smallEtaleTopology _).obj Q) g
  have he : f' = g' := by
    apply Sheaf.hom_ext
    apply sheafify_hom_ext _ _ _ ((presheafToSheaf Y.smallEtaleTopology _).obj Q).property
    apply NatTrans.ext
    funext U
    apply ((ModuleCat.ringExtendScalarsAdj.{u + 1, u + 1} r).homEquiv _ _).injective
    simp only [Adjunction.homEquiv_apply]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    simpa only [lisseIntegralScalarGenerator, ModuleCat.ringExtensionTmul, one_smul,
      ModuleCat.comp_apply, NatTrans.comp_app, ModuleCat.restrictScalars.map_apply] using!
      h U.unop 1 x
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact congrArg (fun h ↦ h.hom.app U x) he


private theorem scalarFunctor_add (D : LisseIntegralScalarExtensionData l E Y L ι)
    {F G : LisseIntegralSheaf l E Y} (f g : F ⟶ G) :
    D.functor.map (f + g) = D.functor.map f + D.functor.map g := by
  apply ObjectProperty.hom_ext
  apply NatTrans.ext
  funext m
  apply (cancel_mono (D.levelIso G m.unop).hom).mp
  apply (cancel_epi (D.levelIso F m.unop).inv).mp
  apply scalarLevel_hom_ext l E Y L ι F G m.unop
  intro U a s
  change (D.levelIso G m.unop).hom.hom.app (op U)
    (((D.functor.map (f + g)).hom.app m).hom.app (op U)
      ((D.levelIso F m.unop).inv.hom.app (op U)
        (lisseIntegralScalarGenerator l E Y L ι F m.unop U a s))) =
    (D.levelIso G m.unop).hom.hom.app (op U)
      ((((D.functor.map f).hom.app m).hom.app (op U)
        ((D.levelIso F m.unop).inv.hom.app (op U)
          (lisseIntegralScalarGenerator l E Y L ι F m.unop U a s))) +
      (((D.functor.map g).hom.app m).hom.app (op U)
        ((D.levelIso F m.unop).inv.hom.app (op U)
          (lisseIntegralScalarGenerator l E Y L ι F m.unop U a s))))
  rw [map_add]
  rw [D.map, D.map, D.map]
  change lisseIntegralScalarGenerator l E Y L ι G m.unop U a
    (((f.hom.app (op (lisseScalarSourceIndex l E L ι m.unop))).hom.app (op U) s) +
      ((g.hom.app (op (lisseScalarSourceIndex l E L ι m.unop))).hom.app (op U) s)) = _
  simp only [lisseIntegralScalarGenerator, ModuleCat.ringExtensionTmul,
    map_add, smul_add]

private theorem scalarFunctor_smul (D : LisseIntegralScalarExtensionData l E Y L ι)
    {F G : LisseIntegralSheaf l E Y} (r : Padic.coefficientExtensionIntegers l E)
    (f : F ⟶ G) : D.functor.map (r • f) =
      lisseIntegerInclusion l E L ι r • D.functor.map f := by
  apply ObjectProperty.hom_ext
  apply NatTrans.ext
  funext m
  apply (cancel_mono (D.levelIso G m.unop).hom).mp
  apply (cancel_epi (D.levelIso F m.unop).inv).mp
  apply scalarLevel_hom_ext l E Y L ι F G m.unop
  intro U a s
  let z := lisseIntegralScalarGenerator l E Y L ι F m.unop U a s
  change (D.levelIso G m.unop).hom.hom.app (op U)
    (((D.functor.map (r • f)).hom.app m).hom.app (op U)
      ((D.levelIso F m.unop).inv.hom.app (op U) z)) =
    (D.levelIso G m.unop).hom.hom.app (op U)
      (lisseIntegerInclusion l E L ι r •
        (((D.functor.map f).hom.app m).hom.app (op U)
          ((D.levelIso F m.unop).inv.hom.app (op U) z)))
  rw [map_smul]
  dsimp only [z]
  rw [D.map, D.map]
  change lisseIntegralScalarGenerator l E Y L ι G m.unop U a
    (r • ((f.hom.app (op (lisseScalarSourceIndex l E L ι m.unop))).hom.app (op U) s)) = _
  let B := Padic.coefficientExtensionRing l L (m.unop + 1)
  let k := lisseScalarCoefficientMap l E L ι m.unop
  let M := (G.obj.obj (op (lisseScalarSourceIndex l E L ι m.unop))).obj.obj (op U)
  let η := (ModuleCat.ringExtendScalarsAdj.{u + 1, u + 1} k).unit.app M
  let t := ((toSheafification Y.smallEtaleTopology (ModuleCat.{u + 1} B)).app
    ((G.obj.obj (op (lisseScalarSourceIndex l E L ι m.unop))).obj ⋙
      ModuleCat.ringExtendScalars.{u + 1, u + 1} k)).app (op U)
  let x := (f.hom.app (op (lisseScalarSourceIndex l E L ι m.unop))).hom.app (op U) s
  change t (a • (show (ModuleCat.ringExtendScalars.{u + 1, u + 1} k).obj M from
    η (r • x))) = k r • t (a • (show
      (ModuleCat.ringExtendScalars.{u + 1, u + 1} k).obj M from η x))
  have hh := η.hom.map_smul r x
  have hh' : (show (ModuleCat.ringExtendScalars.{u + 1, u + 1} k).obj M from
      η (r • x)) = k r • (show
        (ModuleCat.ringExtendScalars.{u + 1, u + 1} k).obj M from η x) := hh
  have hhh := congrArg (fun y : (ModuleCat.ringExtendScalars.{u + 1, u + 1} k).obj M ↦
    t (a • y)) hh'
  simpa only [smul_comm a (k r), map_smul] using! hhh

private theorem scalarMap_add {F G : LisseIntegralSheaf l E Y} (f g : F ⟶ G) :
    (lisseIntegralScalarExtension l E Y L ι).map (f + g) =
      (lisseIntegralScalarExtension l E Y L ι).map f +
        (lisseIntegralScalarExtension l E Y L ι).map g := by
  let D := lisseIntegralScalarExtensionData l E Y L ι
  have he : lisseIntegralScalarExtension l E Y L ι = D.functor := by
    rw [lisseIntegralScalarExtension]
  have h : ∀ S : LisseIntegralSheaf l E Y ⥤ LisseIntegralSheaf l L Y,
      S = D.functor → S.map (f + g) = S.map f + S.map g := by
    intro S h
    subst S
    exact scalarFunctor_add l E Y L ι D f g
  exact h _ he

private theorem scalarMap_smul {F G : LisseIntegralSheaf l E Y}
    (r : Padic.coefficientExtensionIntegers l E) (f : F ⟶ G) :
    (lisseIntegralScalarExtension l E Y L ι).map (r • f) =
      lisseIntegerInclusion l E L ι r • (lisseIntegralScalarExtension l E Y L ι).map f := by
  let D := lisseIntegralScalarExtensionData l E Y L ι
  have he : lisseIntegralScalarExtension l E Y L ι = D.functor := by
    rw [lisseIntegralScalarExtension]
  have h : ∀ S : LisseIntegralSheaf l E Y ⥤ LisseIntegralSheaf l L Y,
      S = D.functor → S.map (r • f) = lisseIntegerInclusion l E L ι r • S.map f := by
    intro S h
    subst S
    exact scalarFunctor_smul l E Y L ι D r f
  exact h _ he

@[irreducible]
private def scalarBilinear (F G : LisseRationalSheaf l E Y) :
    E →+ (F.integral ⟶ G.integral) →+
      lisseRationalHom l L Y
        ⟨(lisseIntegralScalarExtension l E Y L ι).obj F.integral⟩
        ⟨(lisseIntegralScalarExtension l E Y L ι).obj G.integral⟩ :=
  { toFun := fun a ↦
      { toFun := fun f ↦ TensorProduct.tmul _ (ι a)
          ((lisseIntegralScalarExtension l E Y L ι).map f)
        map_zero' := by
          have h := scalarMap_add l E Y L ι (0 : F.integral ⟶ G.integral) 0
          rw [zero_add] at h
          have hz : (lisseIntegralScalarExtension l E Y L ι).map
              (0 : F.integral ⟶ G.integral) = 0 := by
            exact (add_eq_left.mp h.symm)
          rw [hz, TensorProduct.tmul_zero]
        map_add' := by intro f g; rw [scalarMap_add, TensorProduct.tmul_add] }
    map_zero' := by
      ext f
      exact congrArg (fun x ↦ TensorProduct.tmul _ x
        ((lisseIntegralScalarExtension l E Y L ι).map f)) ι.map_zero |>.trans
          (TensorProduct.zero_tmul _ _)
    map_add' := by
      intro a b
      ext f
      exact congrArg (fun x ↦ TensorProduct.tmul _ x
        ((lisseIntegralScalarExtension l E Y L ι).map f)) (ι.map_add a b) |>.trans
          (TensorProduct.add_tmul _ _ _) }

private theorem scalarBilinear_apply (F G : LisseRationalSheaf l E Y)
    (a : E) (f : F.integral ⟶ G.integral) :
    scalarBilinear l E Y L ι F G a f = TensorProduct.tmul _ (ι a)
      ((lisseIntegralScalarExtension l E Y L ι).map f) := by
  rw [scalarBilinear]
  rfl

private theorem scalarBilinear_balanced (F G : LisseRationalSheaf l E Y)
    (r : Padic.coefficientExtensionIntegers l E) (a : E) (f : F.integral ⟶ G.integral) :
    scalarBilinear l E Y L ι F G (r • a) f =
      scalarBilinear l E Y L ι F G a (r • f) := by
  rw [scalarBilinear_apply, scalarBilinear_apply, scalarMap_smul,
    ← TensorProduct.smul_tmul]
  congr 1
  change ι ((r : E) * a) = (lisseIntegerInclusion l E L ι r : L) * ι a
  have hi : (lisseIntegerInclusion l E L ι r : L) = ι (r : E) :=
    (lisseIntegerInclusion_exists l E L ι).choose_spec r
  rw [map_mul, hi]

@[irreducible]
private def rationalScalarMap (F G : LisseRationalSheaf l E Y) :
    lisseRationalHom l E Y F G →+
      lisseRationalHom l L Y
        ⟨(lisseIntegralScalarExtension l E Y L ι).obj F.integral⟩
        ⟨(lisseIntegralScalarExtension l E Y L ι).obj G.integral⟩ :=
  TensorProduct.liftAddHom (scalarBilinear l E Y L ι F G)
    (scalarBilinear_balanced l E Y L ι F G)

private theorem rationalScalarMap_tmul (F G : LisseRationalSheaf l E Y)
    (a : E) (f : F.integral ⟶ G.integral) :
    rationalScalarMap l E Y L ι F G (TensorProduct.tmul _ a f) =
      TensorProduct.tmul _ (ι a) ((lisseIntegralScalarExtension l E Y L ι).map f) := by
  rw [rationalScalarMap, TensorProduct.liftAddHom_tmul, scalarBilinear_apply]

set_option maxRecDepth 200 in
/-- Scalar extension of rational morphisms exists with the stated formula.
Source: Weil II (1.1.1) c), d) (blueprint: def-pod-lisse-l-adic-sheaves).
Proof: the integral scalar functor respects the rings-of-integers scalar actions by
its pure-tensor construction. Thus `(a,f) ↦ ι(a) ⊗ S(f)` is balanced and additive in
both arguments. The tensor universal property gives the additive map. Identity and
composition follow on pure tensors from the corresponding integral functor laws and
the rational composition formula, and then on all tensors by additivity. -/
theorem lisseRationalScalarExtension_exists :
    Nonempty (LisseRationalScalarExtensionData l E Y L ι) := by
  refine ⟨{ map := fun F G ↦ rationalScalarMap l E Y L ι F G
            map_add := fun F G f g ↦ (rationalScalarMap l E Y L ι F G).map_add f g
            map_tmul := rationalScalarMap_tmul l E Y L ι
            map_id := ?_
            map_comp := ?_ }⟩
  · intro F
    rw [rationalScalarMap_tmul, map_one, CategoryTheory.Functor.map_id]
  · intro F G H f g
    induction f using TensorProduct.induction_on with
    | zero => simp only [map_zero, LinearMap.zero_apply]
    | add f₁ f₂ ih₁ ih₂ => simp only [map_add, LinearMap.add_apply, ih₁, ih₂]
    | tmul a f =>
      induction g using TensorProduct.induction_on with
      | zero => simp only [map_zero]
      | add g₁ g₂ ih₁ ih₂ => simp only [map_add, ih₁, ih₂]
      | tmul b g =>
        rw [(lisseRationalComposition l E Y).comp_tmul, rationalScalarMap_tmul,
          rationalScalarMap_tmul, rationalScalarMap_tmul,
          (lisseRationalComposition l L Y).comp_tmul, map_mul, Functor.map_comp]

/-- The prescribed additive scalar-extension maps.
Source: Weil II (1.1.1) d) (blueprint: def-pod-lisse-l-adic-sheaves). -/
@[irreducible]
def lisseRationalScalarExtensionData : LisseRationalScalarExtensionData l E Y L ι :=
  Classical.choice (lisseRationalScalarExtension_exists l E Y L ι)

/-- Scalar extension `F ⊗ E ↦ (F ⊗_{𝒪_E} 𝒪_L) ⊗ L`.
Source: Weil II (1.1.1) d) (blueprint: def-pod-lisse-l-adic-sheaves). -/
def lisseRationalScalarExtension : LisseRationalSheaf l E Y ⥤ LisseRationalSheaf l L Y where
  obj F := ⟨(lisseIntegralScalarExtension l E Y L ι).obj F.integral⟩
  map {F G} f := (lisseRationalScalarExtensionData l E Y L ι).map F G f
  map_id := (lisseRationalScalarExtensionData l E Y L ι).map_id
  map_comp := (lisseRationalScalarExtensionData l E Y L ι).map_comp _ _ _

end ScalarExtension

section AlgebraicCoefficients

variable (K : Type (u + 1)) [Field K] [Algebra ℚ_[l] K] [IsAlgClosure ℚ_[l] K]

/-- The scalar-extension diagram, with objects and arrows specified by the integral
and rational constructions above. Its pseudofunctor coherence is tensor associativity.
Source: Weil II (1.1.1) d) (blueprint: def-pod-lisse-l-adic-sheaves). -/
structure LisseCoefficientDiagramData where
  /-- Coherent diagram over the directed set of finite coefficient fields. -/
  diagram : Pseudofunctor (LocallyDiscrete (Padic.FiniteCoefficientFields l K))
    Cat.{u + 1, u + 2}
  /-- Its value at E is the category of lisse E-sheaves. -/
  obj_eq (E₀ : Padic.FiniteCoefficientFields l K) :
    diagram.obj ⟨E₀⟩ = Cat.of (LisseRationalSheaf l E₀.val Y)
  /-- Its scalar-extension arrows are the prescribed rational functors. -/
  map_eq (E₀ L₀ : Padic.FiniteCoefficientFields l K) (h : E₀ ≤ L₀) :
    eqToHom (obj_eq E₀).symm ≫ diagram.map (homOfLE h).toLoc ≫ eqToHom (obj_eq L₀) =
      (lisseRationalScalarExtension l E₀.val Y L₀.val
        (IntermediateField.inclusion h)).toCatHom

/-- The prescribed coefficient diagram admits coherent tensor-associativity constraints.
Source: Weil II (1.1.1) d) (blueprint: def-pod-lisse-l-adic-sheaves).
Proof: for identity inclusions use the canonical identity scalar comparison. For E ⊂ L ⊂ M,
reindex the finite-level systems cofinally and use the balanced-tensor associator
`M ⊗_L (L ⊗_E F) ≅ M ⊗_E F`. These comparisons preserve pure tensor sections, so
identity constraints and the associativity pentagon reduce on them to multiplication
in the coefficient fields. Sheafification and rationalization preserve those equalities.
This supplies the pseudofunctor, with exactly the stated values on objects and arrows. -/
theorem lisseCoefficientDiagram_exists : Nonempty (LisseCoefficientDiagramData l Y K) := by
  sorry

/-- The coherent diagram of lisse E-sheaves under coefficient extension.
Source: Weil II (1.1.1) d) (blueprint: def-pod-lisse-l-adic-sheaves). -/
@[irreducible]
def lisseCoefficientDiagramData : LisseCoefficientDiagramData l Y K :=
  Classical.choice (lisseCoefficientDiagram_exists l Y K)

/-- The category of pairs `(E,F)`, before identifying scalar extensions.
Source: Weil II (1.1.1) d) (blueprint: def-pod-lisse-l-adic-sheaves). -/
abbrev LisseCoefficientPairs :=
  Pseudofunctor.Grothendieck (lisseCoefficientDiagramData l Y K).diagram

/-- Cocartesian arrows: a scalar extension followed by an isomorphism.
Inverting these gives the 2-colimit, without identifying objects as raw sets.
Source: Weil II (1.1.1) d) (blueprint: def-pod-lisse-l-adic-sheaves). -/
def lisseCoefficientCocartesian : MorphismProperty (LisseCoefficientPairs l Y K) :=
  fun _ _ f => IsIso f.fiber

/-- Lisse algebraic-coefficient sheaves are the 2-colimit of the lisse E-categories.
The Grothendieck construction has pairs `(E,F)` as objects; localization preserves its
objects and inverts the coefficient-extension arrows.
Source: Weil II (1.1.1) d) (blueprint: def-pod-lisse-l-adic-sheaves). -/
abbrev LisseAlgebraicSheaf := (lisseCoefficientCocartesian l Y K).Localization

/-- The coefficient pair underlying an algebraic-coefficient sheaf.
Localization uses type synonyms on objects, so no representative is chosen here.
Source: Weil II (1.1.1) d) (blueprint: def-pod-lisse-l-adic-sheaves). -/
def lisseAlgebraicPair (F : LisseAlgebraicSheaf l Y K) : LisseCoefficientPairs l Y K :=
  F.as.obj

/-- The rational model of a coefficient pair, transported along its specified category value.
Source: Weil II (1.1.1) d) (blueprint: def-pod-lisse-l-adic-sheaves). -/
def lisseCoefficientPairModel (F : LisseCoefficientPairs l Y K) :
    LisseRationalSheaf l F.base.val Y :=
  (eqToHom ((lisseCoefficientDiagramData l Y K).obj_eq F.base)).toFunctor.obj F.fiber

/-- The algebraic-coefficient fibre is `K ⊗_E F_y`, for the pair `(E,F)`.
Source: Weil II (1.1.1) d), SGA 5 VI
(blueprint: def-pod-lisse-l-adic-sheaves). -/
def lisseAlgebraicFiber {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (y : Spec (.of Ω) ⟶ Y) (F : LisseAlgebraicSheaf l Y K) : ModuleCat.{u + 1} K :=
  let P := lisseAlgebraicPair l Y K F
  ModuleCat.of K (TensorProduct P.base.val K
    (lisseRationalFiber l P.base.val Y y (lisseCoefficientPairModel l Y K P)))

/-- Embed a rational model as the corresponding pair in the 2-colimit.
Source: Weil II (1.1.1) d) (blueprint: def-pod-lisse-l-adic-sheaves). -/
def lisseAlgebraicOfModel (E₀ : Padic.FiniteCoefficientFields l K)
    (F : LisseRationalSheaf l E₀.val Y) : LisseAlgebraicSheaf l Y K :=
  (lisseCoefficientCocartesian l Y K).Q.obj
    { base := E₀
      fiber := (eqToHom ((lisseCoefficientDiagramData l Y K).obj_eq E₀).symm).toFunctor.obj F }

/-- Tensor at algebraic coefficients, formed over the compositum of the coefficient fields.
Source: Weil II (1.1.1) d), SGA 5 VI
(blueprint: def-pod-lisse-l-adic-sheaves). -/
def lisseAlgebraicTensor (F G : LisseAlgebraicSheaf l Y K) : LisseAlgebraicSheaf l Y K :=
  let P := lisseAlgebraicPair l Y K F
  let Q := lisseAlgebraicPair l Y K G
  let L₀ := Padic.finiteCoefficientCompositum l K P.base Q.base
  let f := (lisseRationalScalarExtension l P.base.val Y L₀.val
    (IntermediateField.inclusion (show P.base.val ≤ L₀.val from le_sup_left))).obj
      (lisseCoefficientPairModel l Y K P)
  let g := (lisseRationalScalarExtension l Q.base.val Y L₀.val
    (IntermediateField.inclusion (show Q.base.val ≤ L₀.val from le_sup_right))).obj
      (lisseCoefficientPairModel l Y K Q)
  lisseAlgebraicOfModel l Y K L₀ (lisseRationalTensor l L₀.val Y f g)

/-- The algebraic-coefficient unit is the constant system over the base coefficient field.
Source: Weil II (1.1.1) d), SGA 5 VI
(blueprint: def-pod-lisse-l-adic-sheaves). -/
def lisseAlgebraicUnit : LisseAlgebraicSheaf l Y K :=
  lisseAlgebraicOfModel l Y K (Padic.finiteCoefficientBase l K)
    (lisseRationalUnit l (Padic.finiteCoefficientBase l K).val Y)

end AlgebraicCoefficients

end AlgebraicGeometry.Scheme
