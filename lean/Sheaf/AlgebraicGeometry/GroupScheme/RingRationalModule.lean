module

public import Sheaf.AlgebraicGeometry.HopfCoactionLinearization
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.AlgebraicGeometry.Morphisms.Affine

/-! # Rational modules over a ring

Source: Alper, Adequate moduli spaces, Section 9.7, pp.526--528.
(blueprint: def-sfb-ring-rational-module)
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v w

open CategoryTheory
open scoped TensorProduct

namespace AlgebraicGeometry.RingRational

/-- The coordinate Hopf algebra with the given group law and structure map.
Source: Alper, Section 9.7 (blueprint: def-sfb-ring-rational-module). -/
instance coordinateHopf (R : Type u) [CommRing R] (G : Grp (Over (Spec (.of R))))
    [IsAffineHom G.X.hom] : HopfAlgebra R Γ(G.X.left, ⊤) :=
  letI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  @HopfAction.affineCoordinateHopfAlgebra (.of R) G.X.left ⟨G.X.hom⟩
    (inferInstanceAs (GrpObj G.X)) inferInstance

variable (R : Type u) [CommRing R] (C : Type v) [CommRing C] [HopfAlgebra R C]
variable (M : Type w) [AddCommGroup M] [Module R M]

/-- A rational module is a counital coassociative right coordinate comodule.
Source: Alper, Section 9.7 (blueprint: def-sfb-ring-rational-module). -/
structure Coaction where
  /-- The linear coaction. -/
  map : M →ₗ[R] M ⊗[R] C
  /-- The identity law. -/
  counit : (TensorProduct.rid R M).toLinearMap ∘ₗ
    (Coalgebra.counit (R := R) (A := C)).lTensor M ∘ₗ map = LinearMap.id
  /-- The composition law. -/
  coassoc : (TensorProduct.assoc R M C C).toLinearMap ∘ₗ map.rTensor C ∘ₗ map =
    (Coalgebra.comul (R := R) (A := C)).lTensor M ∘ₗ map

variable {R C M}

/-- Invariant endomorphisms are exactly the linear maps commuting with the coaction.
Equivalently they are the fixed vectors for conjugation on End(M).
Source: Alper, Theorem 9.7.5 (blueprint: def-sfb-ring-rational-module). -/
def invariantEnd (ρ : Coaction R C M) : Submodule R (Module.End R M) :=
  LinearMap.ker ((LinearMap.llcomp R M M (M ⊗[R] C) ρ.map) -
    (LinearMap.lcomp R (M ⊗[R] C) ρ.map).comp (LinearMap.rTensorHom C))

/-- Evaluation of an endomorphism with Hopf coefficients on a vector with Hopf
coefficients: (T tensor c)(m tensor d) = T(m) tensor cd.
Source: Alper, Theorem 9.7.5 (blueprint: def-sfb-ring-rational-module). -/
def evaluateTensor : (Module.End R M ⊗[R] C) →ₗ[R] (M ⊗[R] C →ₗ[R] M ⊗[R] C) :=
  TensorProduct.lift
    ((TensorProduct.mapBilinear (RingHom.id R) M C M C).compl₂ (LinearMap.mul R C))

end AlgebraicGeometry.RingRational
