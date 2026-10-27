module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.LinearAlgebra.Quotient.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.CategoryTheory.Equivalence

/-! # The coefficient quotient of a vector-space-valued functor

Source: Milne, Algebraic Groups (2017), §9(d), Theorem 9.37, pp.175–178;
the explicit quotient presentation in lem-sfb-exact-fibre-coalgebra-reconstruction.
(blueprint: def-sfb-fibre-coefficient-quotient)
-/

set_option autoImplicit false

@[expose] public section

universe u v w s t a

open CategoryTheory
open scoped TensorProduct DirectSum

namespace CategoryTheory.FibreReconstruction

variable {k : Type u} [Field k] {S : Type s} [Category.{t} S]
variable (F : S ⥤ ModuleCat.{w} k)

/-- The summand of matrix coefficients at V.
Source: Milne §9(d), coefficient presentation of C(omega).
(blueprint: def-sfb-fibre-coefficient-quotient) -/
abbrev CoefficientSummand (V : S) := Module.Dual k (F.obj V) ⊗[k] F.obj V

/-- The set-indexed direct sum of all coefficient summands.
Source: Milne §9(d), coefficient presentation of C(omega).
(blueprint: def-sfb-fibre-coefficient-quotient) -/
abbrev CoefficientSum := ⨁ V : S, CoefficientSummand F V

/-- Include a coefficient tensor in its direct-sum summand.
Source: Milne §9(d), coefficient presentation of C(omega).
(blueprint: def-sfb-fibre-coefficient-quotient) -/
noncomputable def coefficientInSum (V : S) :
    CoefficientSummand F V →ₗ[k] CoefficientSum F :=
  @DirectSum.lof k _ S (CoefficientSummand F) _ _ (Classical.decEq S) V

/-- The span of exactly the naturality relations, with no additional relations.
Source: Milne §9(d), coefficient presentation of C(omega).
(blueprint: def-sfb-fibre-coefficient-quotient) -/
def coefficientRelations : Submodule k (CoefficientSum F) :=
  Submodule.span k {z | ∃ (V W : S) (f : V ⟶ W)
    (v : F.obj V) (ψ : Module.Dual k (F.obj W)),
    z = coefficientInSum F W (ψ ⊗ₜ[k] (F.map f) v) -
      coefficientInSum F V ((ψ.comp (F.map f).hom) ⊗ₜ[k] v)}

/-- The actual direct-sum quotient B, prior to equipping it with a coalgebra structure.
Source: Milne §9(d), coefficient presentation of C(omega).
(blueprint: def-sfb-fibre-coefficient-quotient) -/
abbrev CoefficientQuotient := CoefficientSum F ⧸ coefficientRelations F

/-- The canonical linear map from a coefficient summand to the quotient.
Source: Milne §9(d), coefficient presentation of C(omega).
(blueprint: def-sfb-fibre-coefficient-quotient) -/
noncomputable def coefficientMap (V : S) :
    CoefficientSummand F V →ₗ[k] CoefficientQuotient F :=
  (coefficientRelations F).mkQ ∘ₗ coefficientInSum F V

/-- Brackets [phi tensor v]_V mean the class of this tensor in B.
Source: Milne §9(d), coefficient presentation of C(omega).
(blueprint: def-sfb-fibre-coefficient-quotient) -/
noncomputable def coefficient (V : S) (φ : Module.Dual k (F.obj V)) (v : F.obj V) :
    CoefficientQuotient F := coefficientMap F V (φ ⊗ₜ[k] v)

variable {A : Type v} [Category.{a} A]

/-- Use the counit of the chosen skeletal equivalence to take coefficients at any object.
Source: Milne §9(d), Theorem 9.37; transport along representative isomorphisms.
(blueprint: def-sfb-fibre-coefficient-quotient) -/
noncomputable def coefficientAt (G : A ⥤ ModuleCat.{w} k) (e : S ≌ A)
    (V : A) (φ : Module.Dual k (G.obj V)) (v : G.obj V) :
    CoefficientQuotient (e.functor ⋙ G) :=
  coefficient (e.functor ⋙ G) (e.inverse.obj V)
    (φ.comp (G.map (e.counitIso.app V).hom).hom) (G.map (e.counitIso.app V).inv v)

end CategoryTheory.FibreReconstruction
