module

public import Sheaf.RingTheory.HopfActionModuleData
public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.Algebra.Ring.Subring.Basic

/-! # Equivariant algebras for an algebra coaction

Source: Stacks Project, Tag 03LF, affine form, and Tag 06WT, algebra objects
(blueprint: def-sfb-equivariant-coaction-algebra).
-/

@[expose] public section
set_option autoImplicit false
universe u v w q
open CategoryTheory
open scoped TensorProduct
namespace HopfAction
variable (k : Type u) [Field k] (C : Type v) [CommRing C] [HopfAlgebra k C]
variable (E : Type w) [CommRing E] [Algebra k E] (ρ : AlgebraCoaction k C E)

/-- Arbitrary commutative E-algebras with a rational coaction extending that of E.
Source: Stacks Tags 03LF and 06WT (blueprint: def-sfb-equivariant-coaction-algebra). -/
structure EquivariantAlgebra where
  /-- The underlying k-algebra, without any finite generation condition. -/
  algebra : CommAlgCat.{max u v w q} k
  /-- The rational coaction, including its counit and coassociativity laws. -/
  coaction : AlgebraCoaction k C algebra
  /-- The E-algebra structure. -/
  structureMap : E →ₐ[k] algebra
  /-- The coaction extends the specified one on E. -/
  extends_coaction : ∀ e : E, coaction.map (structureMap e) =
    Algebra.TensorProduct.map structureMap (AlgHom.id k C) (ρ.map e)

namespace EquivariantAlgebra
variable {k C E ρ}

/-- Equivariant E-algebra maps, with no restriction on their underlying algebras.
Source: Stacks Tags 03LF and 06WT (blueprint: def-sfb-equivariant-coaction-algebra). -/
def Hom (A B : EquivariantAlgebra.{u, v, w, q} k C E ρ) :=
  {f : A.algebra →ₐ[k] B.algebra //
    (∀ e : E, f (A.structureMap e) = B.structureMap e) ∧
    ∀ a : A.algebra, B.coaction.map (f a) =
      Algebra.TensorProduct.map f (AlgHom.id k C) (A.coaction.map a)}

/-- Identity and composition are those of the underlying algebra maps.
Source: Stacks Tags 03LF and 06WT (blueprint: def-sfb-equivariant-coaction-algebra). -/
instance category : Category (EquivariantAlgebra.{u, v, w, q} k C E ρ) where
  Hom := Hom
  id A := ⟨AlgHom.id k A.algebra, by constructor <;> intro x <;> simp⟩
  comp {A B D} f g := ⟨g.val.comp f.val, by
    constructor
    · intro e
      simp only [AlgHom.comp_apply, f.property.1, g.property.1]
    · intro a
      simp only [AlgHom.comp_apply, g.property.2, f.property.2]
      exact (congrArg (fun h : A.algebra ⊗[k] C →ₐ[k] D.algebra ⊗[k] C ↦
        h (A.coaction.map a)) (Algebra.TensorProduct.map_comp g.val f.val
          (AlgHom.id k C) (AlgHom.id k C))).symm⟩
  id_comp f := Subtype.ext (AlgHom.comp_id f.val)
  comp_id f := Subtype.ext (AlgHom.id_comp f.val)
  assoc f g h := Subtype.ext (AlgHom.comp_assoc h.val g.val f.val).symm

/-- Forget only the coaction and E-structure, retaining the underlying ring.
Source: Stacks Tag 06WT (blueprint: def-sfb-equivariant-coaction-algebra). -/
def forgetToRings : EquivariantAlgebra.{u, v, w, q} k C E ρ ⥤
    CommRingCat.{max u v w q} where
  obj A := CommRingCat.of A.algebra
  map f := CommRingCat.ofHom f.val.toRingHom

/-- The invariant ring is the actual coaction equalizer.
Source: Stacks Tags 03LF and 06WT (blueprint: def-sfb-equivariant-coaction-algebra). -/
def invariants (A : EquivariantAlgebra.{u, v, w, q} k C E ρ) : Subring A.algebra :=
  RingHom.eqLocus A.coaction.map.toRingHom Algebra.TensorProduct.includeLeftRingHom

end EquivariantAlgebra
end HopfAction
