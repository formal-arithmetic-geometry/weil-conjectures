module

public import Sheaf.RingTheory.HopfActionModuleData
public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-! # Equivariant commutative algebras on an affine Hopf action

Source: Stacks Project, groupoids.tex, Tag 03LF, applied to algebra objects;
stacks-sheaves.tex, Tag 06WT (blueprint: def-sfb-equivariant-affine-algebra).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v w z

open CategoryTheory
open scoped TensorProduct

namespace HopfAction

variable (k : Type u) [Field k] (H : Type v) [CommRing H] [HopfAlgebra k H]
variable (E : Type w) [CommRing E] [Algebra k E] (ρ : AlgebraCoaction k H E)

/-- A commutative algebra over E with a compatible algebra coaction.
Source: Stacks 03LF, affine algebra-object form
(blueprint: def-sfb-equivariant-affine-algebra). -/
structure EquivariantAffineAlgebra where
  /-- The underlying commutative k-algebra, with no finite-generation condition. -/
  algebra : CommAlgCat.{z} k
  /-- The specified structure map from E. -/
  unit : E →ₐ[k] algebra
  /-- The existing counital, coassociative coaction. -/
  coaction : AlgebraCoaction k H algebra
  /-- The structure map is equivariant. -/
  compatible : ∀ e : E, coaction.map (unit e) =
    Algebra.TensorProduct.map unit (AlgHom.id k H) (ρ.map e)

namespace EquivariantAffineAlgebra

variable {k H E ρ}

/-- Algebra maps preserving the structure map and the coaction.
Source: Stacks 03LF, morphisms (blueprint: def-sfb-equivariant-affine-algebra). -/
@[ext]
structure Hom (B B' : EquivariantAffineAlgebra.{u, v, w, z} k H E ρ) where
  /-- The underlying k-algebra homomorphism. -/
  map : B.algebra →ₐ[k] B'.algebra
  /-- Compatibility with E. -/
  unit : map.comp B.unit = B'.unit
  /-- Compatibility with the coaction. -/
  equivariant : (Algebra.TensorProduct.map map (AlgHom.id k H)).comp B.coaction.map =
    B'.coaction.map.comp map

/-- The category has exactly equivariant algebra homomorphisms.
Source: Stacks 03LF, composition (blueprint: def-sfb-equivariant-affine-algebra). -/
instance category : Category (EquivariantAffineAlgebra.{u, v, w, z} k H E ρ) where
  Hom := Hom
  id B :=
    { map := AlgHom.id k B.algebra
      unit := rfl
      equivariant := by ext b; simp }
  comp f g :=
    { map := g.map.comp f.map
      unit := by rw [AlgHom.comp_assoc, f.unit, g.unit]
      equivariant := by
        have h := Algebra.TensorProduct.map_comp g.map f.map (AlgHom.id k H)
          (AlgHom.id k H)
        simp only [AlgHom.id_comp] at h
        rw [h, AlgHom.comp_assoc, f.equivariant,
          ← AlgHom.comp_assoc, g.equivariant, AlgHom.comp_assoc] }
  id_comp f := Hom.ext rfl
  comp_id f := Hom.ext rfl
  assoc f g h := Hom.ext rfl

/-- Invariants are the actual equalizer subring, with its inclusion in B.
Source: Stacks 06WT, sections via maps from the unit
(blueprint: def-sfb-equivariant-affine-algebra). -/
def invariants (B : EquivariantAffineAlgebra.{u, v, w, z} k H E ρ) : Subring B.algebra :=
  RingHom.eqLocus B.coaction.map.toRingHom Algebra.TensorProduct.includeLeftRingHom

end EquivariantAffineAlgebra

end HopfAction
