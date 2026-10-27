module

public import Mathlib.Algebra.Category.CommHopfAlgCat
public import Mathlib.Algebra.Algebra.Subalgebra.Operations
public import Mathlib.FieldTheory.Galois.Basic

/-! # Semilinear Galois actions on commutative Hopf algebras

Source: Milne, Algebraic Groups (2017), Appendix A.64, pp.580--581
(blueprint: def-sfb-semilinear-hopf-algebra).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v w

open CategoryTheory
open scoped TensorProduct

namespace CommHopfAlgCat

variable (k : Type u) (L : Type v) [Field k] [Field L] [Algebra k L]

/-- Semilinear Galois descent data on a commutative Hopf algebra: ring automorphisms
with the scalar rule, commuting with antipode and counit, and with the diagonal tensor
compatibility. Source: Milne A.64 (blueprint: def-sfb-semilinear-hopf-algebra). -/
structure SemilinearAction (B : CommHopfAlgCat.{w} L) where
  /-- The action by additive, multiplicative bijections. -/
  ρ : (L ≃ₐ[k] L) →* (B ≃+* B)
  /-- Semilinearity on scalars. -/
  scalar : ∀ (σ : L ≃ₐ[k] L) (r : L),
    ρ σ (algebraMap L B r) = algebraMap L B (σ r)
  /-- Compatibility with the antipode. -/
  antipode : ∀ (σ : L ≃ₐ[k] L) (b : B),
    ρ σ (HopfAlgebra.antipode L b) = HopfAlgebra.antipode L (ρ σ b)
  /-- The counit is semilinear, with the Galois action on its target. -/
  counit : ∀ (σ : L ≃ₐ[k] L) (b : B),
    Coalgebra.counit (R := L) (ρ σ b) = σ (Coalgebra.counit (R := L) b)
  /-- The diagonal semilinear tensor action commutes with comultiplication. -/
  comul : ∀ (σ : L ≃ₐ[k] L) (b : B),
    Coalgebra.comul (R := L) (ρ σ b) =
      TensorProduct.map
        ({ toFun := ρ σ
           map_add' := (ρ σ).map_add
           map_smul' := fun r x ↦ by
             simp only [Algebra.smul_def, map_mul, scalar]
             rfl } :
          B →ₛₗ[σ.toRingHom] B)
        ({ toFun := ρ σ
           map_add' := (ρ σ).map_add
           map_smul' := fun r x ↦ by
             simp only [Algebra.smul_def, map_mul, scalar]
             rfl } :
          B →ₛₗ[σ.toRingHom] B)
        (Coalgebra.comul (R := L) b)

/-- The category's objects: commutative Hopf algebras with semilinear Galois action.
Source: Milne A.64 (blueprint: def-sfb-semilinear-hopf-algebra). -/
structure GaloisObject where
  /-- The underlying Hopf algebra. -/
  obj : CommHopfAlgCat.{w} L
  /-- Its semilinear Hopf action. -/
  action : SemilinearAction k L obj

variable {k L}

/-- Equivariant, L-linear Hopf maps. Source: Milne A.64 and A.66
(blueprint: def-sfb-semilinear-hopf-algebra). -/
structure GaloisObject.Hom (B C : GaloisObject.{u, v, w} k L) where
  /-- The underlying Hopf map. -/
  hom : B.obj ⟶ C.obj
  /-- Equivariance. -/
  equivariant : ∀ (σ : L ≃ₐ[k] L) (b : B.obj),
    hom.hom (B.action.ρ σ b) = C.action.ρ σ (hom.hom b)

/-- Composition and identities of equivariant Hopf maps.
Source: Milne A.64 (blueprint: def-sfb-semilinear-hopf-algebra). -/
instance GaloisObject.category : Category (GaloisObject.{u, v, w} k L) where
  Hom B C := GaloisObject.Hom B C
  id B := ⟨𝟙 B.obj, fun _ _ ↦ rfl⟩
  comp f g := ⟨f.hom ≫ g.hom, fun σ b ↦ by
    change g.hom.hom (f.hom.hom ( _ )) = _
    rw [f.equivariant, g.equivariant]
    rfl⟩

/-- Restrict the scalar structure along k → L.
Source: Milne A.64 (blueprint: def-sfb-semilinear-hopf-algebra). -/
instance GaloisObject.baseAlgebra (B : GaloisObject.{u, v, w} k L) : Algebra k B.obj :=
  ((algebraMap L B.obj).comp (algebraMap k L)).toAlgebra

/-- The action regarded as a multiplicative semiring action.
Source: Milne A.64 (blueprint: def-sfb-semilinear-hopf-algebra). -/
instance GaloisObject.mulSemiringAction (B : GaloisObject.{u, v, w} k L) :
    MulSemiringAction (L ≃ₐ[k] L) B.obj where
  smul σ b := B.action.ρ σ b
  one_smul b := by change B.action.ρ 1 b = b; rw [map_one]; rfl
  mul_smul σ τ b := by change B.action.ρ (σ * τ) b = _; rw [map_mul]; rfl
  smul_zero σ := map_zero (B.action.ρ σ)
  smul_add σ := map_add (B.action.ρ σ)
  smul_one σ := map_one (B.action.ρ σ)
  smul_mul σ := map_mul (B.action.ρ σ)

/-- The semilinear action fixes the base-field scalars.
Source: Milne A.64 (blueprint: def-sfb-semilinear-hopf-algebra). -/
instance GaloisObject.smulCommClass (B : GaloisObject.{u, v, w} k L) :
    SMulCommClass (L ≃ₐ[k] L) k B.obj where
  smul_comm σ r b := by
    change B.action.ρ σ (r • b) = r • B.action.ρ σ b
    simp only [Algebra.smul_def, map_mul]
    change B.action.ρ σ (algebraMap L B.obj (algebraMap k L r)) * _ =
      algebraMap L B.obj (algebraMap k L r) * _
    rw [B.action.scalar, σ.commutes]

/-- The actual invariant subalgebra, using Mathlib's fixed-point construction.
Source: Milne A.64 (blueprint: def-sfb-semilinear-hopf-algebra). -/
def GaloisObject.invariants (B : GaloisObject.{u, v, w} k L) : Subalgebra k B.obj :=
  FixedPoints.subalgebra k B.obj (L ≃ₐ[k] L)

end CommHopfAlgCat
