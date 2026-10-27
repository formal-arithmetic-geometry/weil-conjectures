module

public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Category.FGModuleCat.Basic
public import Mathlib.RingTheory.Coalgebra.Basic
public import Mathlib.LinearAlgebra.Dual.Lemmas

/-! # Data for finite-algebra duality

Source: Milne, Algebraic Groups (2017), §9(d), p.174 and Example 9.36, p.178.
(blueprint: def-sfb-finite-algebra-duality-data)

The categories use the actual underlying finite-dimensional vector spaces. Their morphisms
are linear maps satisfying the action or coaction equation. No existence of a coalgebra on
the algebra's dual is asserted by these definitions.
-/

set_option autoImplicit false

@[expose] public section

universe u v w

open CategoryTheory
open scoped TensorProduct

namespace FiniteAlgebraComoduleDuality

variable {k : Type u} [Field k]
variable {E : Type v} [Ring E] [Algebra k E]

/-- The defining multiplication and unit pairings for the coalgebra on E's linear dual.
Source: Milne, §9(d), p.174 and Example 9.36, p.178.
(blueprint: def-sfb-finite-algebra-duality-data) -/
def IsDualCoalgebra (c : Coalgebra k (Module.Dual k E)) : Prop :=
  (∀ (d : Module.Dual k E) (a b : E),
    TensorProduct.dualDistrib k E E (c.comul d) (a ⊗ₜ[k] b) = d (a * b)) ∧
  ∀ d : Module.Dual k E, c.counit d = d 1

/-- Right coactions of the specified dual coalgebra on a fixed vector space.
The associator and right unitor make both coaction equations well typed.
Source: Milne, §9(d), p.174 and Example 9.36, p.178.
(blueprint: def-sfb-finite-algebra-duality-data) -/
def RightCoaction (c : Coalgebra k (Module.Dual k E))
    (M : Type w) [AddCommGroup M] [Module k M] :=
  {ρ : M →ₗ[k] M ⊗[k] Module.Dual k E //
    (TensorProduct.assoc k M (Module.Dual k E) (Module.Dual k E)).toLinearMap ∘ₗ
        ρ.rTensor (Module.Dual k E) ∘ₗ ρ = c.comul.lTensor M ∘ₗ ρ ∧
    (TensorProduct.rid k M).toLinearMap ∘ₗ c.counit.lTensor M ∘ₗ ρ = LinearMap.id}

/-- Finite-dimensional left E-modules, presented by their bilinear unital associative action.
An algebra map E to End_k(M) encodes exactly these action laws.
Source: Milne, Example 9.36, p.178.
(blueprint: def-sfb-finite-algebra-duality-data) -/
structure LeftModule (k : Type u) [Field k] (E : Type v) [Ring E] [Algebra k E] where
  /-- The unchanged underlying finite-dimensional vector space. -/
  space : FGModuleCat.{w} k
  /-- The left action, including k-bilinearity, associativity and the unit law. -/
  action : E →ₐ[k] Module.End k space

/-- Morphisms of the left modules are the actual k-linear intertwiners.
Source: Milne, Example 9.36, p.178.
(blueprint: def-sfb-finite-algebra-duality-data) -/
instance leftModuleCategory : Category (LeftModule.{u, v, w} k E) where
  Hom X Y := {f : X.space →ₗ[k] Y.space //
    ∀ (a : E) (m : X.space), f (X.action a m) = Y.action a (f m)}
  id _X := ⟨LinearMap.id, fun _ _ ↦ rfl⟩
  comp f g := ⟨g.val.comp f.val,
    fun a m ↦ (congrArg g.val (f.property a m)).trans (g.property a (f.val m))⟩
  id_comp _ := Subtype.ext (LinearMap.ext fun _ ↦ rfl)
  comp_id _ := Subtype.ext (LinearMap.ext fun _ ↦ rfl)
  assoc _ _ _ := Subtype.ext (LinearMap.ext fun _ ↦ rfl)

/-- The left-module forgetful functor keeps the underlying vector space and linear map.
Source: Milne, Example 9.36, p.178.
(blueprint: def-sfb-finite-algebra-duality-data) -/
def forgetLeft : LeftModule.{u, v, w} k E ⥤ FGModuleCat.{w} k where
  obj X := X.space
  map f := FGModuleCat.ofHom f.val

/-- Finite-dimensional right comodules over the specified dual coalgebra.
Source: Milne, Example 9.36, p.178.
(blueprint: def-sfb-finite-algebra-duality-data) -/
structure RightComodule (c : Coalgebra k (Module.Dual k E)) where
  /-- The unchanged underlying finite-dimensional vector space. -/
  space : FGModuleCat.{w} k
  /-- The actual counital coassociative linear coaction. -/
  coaction : RightCoaction c space

/-- Morphisms of right comodules are exactly the colinear k-linear maps.
Source: Milne, Example 9.36, p.178.
(blueprint: def-sfb-finite-algebra-duality-data) -/
instance rightComoduleCategory (c : Coalgebra k (Module.Dual k E)) :
    Category (RightComodule.{u, v, w} c) where
  Hom X Y := {f : X.space →ₗ[k] Y.space //
    ∀ m : X.space, f.rTensor (Module.Dual k E) (X.coaction.val m) =
      Y.coaction.val (f m)}
  id _X := ⟨LinearMap.id, fun _m ↦ LinearMap.rTensor_id_apply _ _ _⟩
  comp f g := ⟨g.val.comp f.val, fun m ↦
    (LinearMap.rTensor_comp_apply _ _ _ _).trans
      ((congrArg (g.val.rTensor (Module.Dual k E)) (f.property m)).trans
        (g.property (f.val m)))⟩
  id_comp _ := Subtype.ext (LinearMap.ext fun _ ↦ rfl)
  comp_id _ := Subtype.ext (LinearMap.ext fun _ ↦ rfl)
  assoc _ _ _ := Subtype.ext (LinearMap.ext fun _ ↦ rfl)

/-- The right-comodule forgetful functor keeps the vector space and linear map.
Source: Milne, Example 9.36, p.178.
(blueprint: def-sfb-finite-algebra-duality-data) -/
def forgetRight (c : Coalgebra k (Module.Dual k E)) :
    RightComodule.{u, v, w} c ⥤ FGModuleCat.{w} k where
  obj X := X.space
  map f := FGModuleCat.ofHom f.val

end FiniteAlgebraComoduleDuality
