module

public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.Algebra.MvPolynomial.Eval

/-! # Regular SL₂ representations over a ring

Source: Milne, Algebraic Groups, paragraph before Proposition 22.14, printed p.466;
the arbitrary-ring regular action in the orbit-coefficient input
(blueprint: def-sfb-regular-sl2-representation).

Regular matrix entries are represented by polynomials in four matrix coordinates.
On determinant-one matrices this is exactly being a function in the quotient by
`a*d-b*c-1`; choosing representatives does not choose additional action data.
-/

@[expose] public section

universe u v

open scoped TensorProduct

namespace RepresentationTheory

/-- The upper root element `I + z E₁₂`.
Source: Milne, Algebraic Groups, p.466, root subgroup convention
(blueprint: def-sfb-regular-sl2-representation). -/
def sl2Upper {C : Type u} [CommRing C] (z : C) :
    Matrix.SpecialLinearGroup (Fin 2) C :=
  Matrix.SpecialLinearGroup.transvection (i := 0) (j := 1) (by decide) z

/-- The lower root element `I + z E₂₁`.
Source: Milne, Algebraic Groups, p.466, opposite root subgroup convention
(blueprint: def-sfb-regular-sl2-representation). -/
def sl2Lower {C : Type u} [CommRing C] (z : C) :
    Matrix.SpecialLinearGroup (Fin 2) C :=
  Matrix.SpecialLinearGroup.transvection (i := 1) (j := 0) (by decide) z

/-- The Weyl element with rows `(0,1)` and `(-1,0)`.
Source: Milne, Algebraic Groups, Lemma 22.15, pp.466–467, with the orbit lemma's sign
(blueprint: def-sfb-regular-sl2-representation). -/
def sl2Weyl (C : Type u) [CommRing C] : Matrix.SpecialLinearGroup (Fin 2) C :=
  sl2Upper 1 * sl2Lower (-1) * sl2Upper 1

/-- The diagonal torus element with diagonal `(t,t⁻¹)`, written as its root word.
Source: Milne, Algebraic Groups, pp.466–467, torus convention
(blueprint: def-sfb-regular-sl2-representation). -/
def sl2Torus {C : Type u} [CommRing C] (t : Cˣ) :
    Matrix.SpecialLinearGroup (Fin 2) C :=
  sl2Upper (t : C) * sl2Lower (-(↑(t⁻¹) : C)) * sl2Upper (t : C) * (sl2Weyl C)⁻¹

/-- A natural family of linear SL₂ actions with regular matrix entries. The finite
basis and polynomial representatives in `regular` witness a property; they are not
chosen parts of the action. All test algebras live in a universe containing the base.
Source: Milne, Algebraic Groups, p.466, paragraph before Proposition 22.14, with the
arbitrary-ring formulation of the supporting orbit lemma
(blueprint: def-sfb-regular-sl2-representation). -/
structure RegularSL2Representation (B : Type u) [CommRing B]
    (V : Type v) [AddCommGroup V] [Module B V] where
  app (C : Type u) [CommRing C] [Algebra B C] :
    Matrix.SpecialLinearGroup (Fin 2) C →* (C ⊗[B] V ≃ₗ[C] C ⊗[B] V)
  naturality (C D : Type u) [CommRing C] [CommRing D] [Algebra B C] [Algebra B D]
    (f : C →ₐ[B] D) (g : Matrix.SpecialLinearGroup (Fin 2) C) (x : C ⊗[B] V) :
    f.toLinearMap.rTensor V (app C g x) =
      app D (Matrix.SpecialLinearGroup.map f.toRingHom g) (f.toLinearMap.rTensor V x)
  regular : ∃ (n : ℕ) (b : Module.Basis (Fin n) B V)
      (p : Fin n → Fin n → MvPolynomial (Fin 2 × Fin 2) B),
    ∀ (C : Type u) [CommRing C] [Algebra B C]
      (g : Matrix.SpecialLinearGroup (Fin 2) C) (i j : Fin n),
      (b.baseChange C).repr (app C g (1 ⊗ₜ[B] b j)) i =
        MvPolynomial.eval₂ (algebraMap B C) (fun k ↦ g k.1 k.2) (p i j)

end RepresentationTheory
