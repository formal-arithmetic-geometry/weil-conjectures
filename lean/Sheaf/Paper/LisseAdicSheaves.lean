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
public import Sheaf.Algebra.Category.ModuleCat.RingScalarExtension
public import Mathlib.CategoryTheory.Sites.Point.Basic
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Mathlib.CategoryTheory.Bicategory.Grothendieck
public import Mathlib.CategoryTheory.Localization.Construction
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Separated

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
  sorry

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

attribute [local instance] CategoryTheory.Sheaf.monoidalCategory
attribute [local instance] CategoryTheory.Sheaf.braidedCategory

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
  sorry

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
  sorry

/-- The quotient maps preserve composition.
Source: Weil II (1.1.1) b) (blueprint: def-pod-lisse-l-adic-sheaves).
Proof: both sides send the class of a scalar to its class in the final quotient.
Quotient classes exhaust the source quotient, so the maps agree. -/
theorem lisseUnitModuleMap_comp (i j k : ℕᵒᵖ) (f : i ⟶ j) (g : j ⟶ k) :
    lisseUnitModuleMap l E i k (f ≫ g) =
      lisseUnitModuleMap l E i j f ≫ lisseUnitModuleMap l E j k g := by
  sorry

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

/-- The constant coefficient system is lisse.
Source: Weil II (1.1.1) b), SGA 5 VI
(blueprint: def-pod-lisse-l-adic-sheaves).
Proof: each coefficient quotient is finite and is a constant module sheaf. It is killed
by the prescribed power of the uniformizer. The quotient map is surjective with kernel
generated by the indicated power; constant-sheaf stalks are the given modules. -/
theorem lisseIntegralUnit_isLisse :
    IsLisseIntegralDiagram l E Y (lisseIntegralUnitDiagram l E Y) := by
  sorry

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
  sorry

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
  sorry

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
  sorry

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

/-- Scalar extension of rational morphisms exists with the stated formula.
Source: Weil II (1.1.1) c), d) (blueprint: def-pod-lisse-l-adic-sheaves).
Proof: the integral scalar functor respects the rings-of-integers scalar actions by
its pure-tensor construction. Thus `(a,f) ↦ ι(a) ⊗ S(f)` is balanced and additive in
both arguments. The tensor universal property gives the additive map. Identity and
composition follow on pure tensors from the corresponding integral functor laws and
the rational composition formula, and then on all tensors by additivity. -/
theorem lisseRationalScalarExtension_exists :
    Nonempty (LisseRationalScalarExtensionData l E Y L ι) := by
  sorry

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
