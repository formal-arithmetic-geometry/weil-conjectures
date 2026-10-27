module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.CategoryTheory.Endofunctor.Algebra
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.RingTheory.Coalgebra.Basic

/-! # Finite-dimensional right comodules over a coalgebra

Source: Milne, Algebraic Groups (2017), §9(d), pp.174–175.
(blueprint: def-sfb-finite-right-comodule)

The category is a full subcategory of coalgebras for the endofunctor M ↦ M tensor B.
Consequently its morphisms are exactly linear maps commuting with the coactions.
The field and the containing universe of vector spaces are independent.
-/

set_option autoImplicit false

@[expose] public section

universe u w

open CategoryTheory
open scoped TensorProduct

namespace Coalgebra

variable {k : Type u} [Field k] {B : Type w} [AddCommGroup B] [Module k B]

/-- Tensor on the right by B, without imposing a size equality on k and its modules.
Source: Milne §9(d), the endofunctor underlying right coactions.
(blueprint: def-sfb-finite-right-comodule) -/
noncomputable def rightTensorFunctor (B : Type w) [AddCommGroup B] [Module k B] :
    ModuleCat.{w} k ⥤ ModuleCat.{w} k where
  obj M := ModuleCat.of k (M ⊗[k] B)
  map f := ModuleCat.ofHom (f.hom.rTensor B)
  map_id M := ModuleCat.hom_ext (LinearMap.rTensor_id (R := k) B M)
  map_comp {X Y Z} f g := ModuleCat.hom_ext
    (LinearMap.rTensor_comp (R := k) (N := X) (P := Y) (Q := Z) B g.hom f.hom)

/-- Finite dimension and the two right-coaction axioms.
Source: Milne §9(d), pp.174–175, and equation (24), p.84.
(blueprint: def-sfb-finite-right-comodule) -/
def finiteRightComoduleProperty (d : Coalgebra k B) :
    ObjectProperty (Endofunctor.Coalgebra (rightTensorFunctor (k := k) B)) :=
  fun M ↦ FiniteDimensional k M.V ∧
    (TensorProduct.assoc k M.V B B).toLinearMap ∘ₗ M.str.hom.rTensor B ∘ₗ M.str.hom =
      d.comul.lTensor M.V ∘ₗ M.str.hom ∧
    (TensorProduct.rid k M.V).toLinearMap ∘ₗ d.counit.lTensor M.V ∘ₗ M.str.hom =
      LinearMap.id

/-- The category of all finite-dimensional right B-comodules in the containing universe.
Source: Milne §9(d), pp.174–175.
(blueprint: def-sfb-finite-right-comodule) -/
abbrev FiniteRightComodule (d : Coalgebra k B) :=
  (finiteRightComoduleProperty d).FullSubcategory

/-- Forget the coaction, retaining the vector space and the actual underlying linear map.
Source: Milne §9(d), p.175.
(blueprint: def-sfb-finite-right-comodule) -/
noncomputable def finiteRightComoduleForget (d : Coalgebra k B) :
    FiniteRightComodule d ⥤ ModuleCat.{w} k :=
  (finiteRightComoduleProperty d).ι ⋙ Endofunctor.Coalgebra.forget _

end Coalgebra
