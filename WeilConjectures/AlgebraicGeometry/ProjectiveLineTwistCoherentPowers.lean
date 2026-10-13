/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Twist
public import WeilConjectures.AlgebraicGeometry.Modules.Dual
public import WeilConjectures.AlgebraicGeometry.Ample

/-! # Coherent tensor powers of twists on the projective line

Source: Stacks Project, Constructions, Tags 01MS and 01MU.
(blueprint: lem-sc-p1-twist-coherent-powers).
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory
open AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Multiplication isomorphisms with the pointwise product formula give normalized,
coherent identifications of positive and negative tensor powers with the twists.

Source: Stacks Project, Constructions, Tags 01MS and 01MU; Step 2 of
lem-sc-p1-twist-multiplication.
(blueprint: lem-sc-p1-twist-coherent-powers).

Proof: Start both families in degree zero with the canonical unit isomorphism,
which sends 1 to 1. Define the positive successor by braiding O(1) past its
previous tensor power and then applying multiplication. On each coordinate
chart this sends the tensor power of the coordinate basis to its ordinary power.
The perfect multiplication pairing O(1) tensor O(-1) to O(0), followed by the
inverse unit isomorphism, identifies O(-1) with the dual of O(1): locally it
sends the inverse coordinate basis to the dual basis. Define the negative family
by iterating multiplication of this inverse twist. In each coordinate chart the
negative successor square evaluates a coordinate against its dual basis and
reduces x_i^(-(a+1)) x_i to x_i^(-a). Both sides therefore agree on the local
tensor basis. The positive square similarly expresses associativity and
commutativity of fraction multiplication. The two charts cover, so these local
identities are global morphism identities. At a=0 both families use exactly
the same unit isomorphism, giving the specified normalization. No scalar choices
remain, and negative exponents are handled by localization of the coordinate. -/
theorem projectiveLine_twist_coherent_powers (k : Type u) [Field k]
    (μ : ∀ n m : ℤ,
        Proj.twist (MvPolynomial.homogeneousSubmodule (Fin 2) k) n ⊗
          Proj.twist (MvPolynomial.homogeneousSubmodule (Fin 2) k) m ⟶
            Proj.twist (MvPolynomial.homogeneousSubmodule (Fin 2) k) (n + m))
    (hiso : ∀ n m : ℤ, IsIso (μ n m))
    (hmul : (∀ (n m : ℤ) (U : (Proj (MvPolynomial.homogeneousSubmodule (Fin 2) k)).Opens)
        (s : Γ(Proj.twist (MvPolynomial.homogeneousSubmodule (Fin 2) k) n, U))
        (t : Γ(Proj.twist (MvPolynomial.homogeneousSubmodule (Fin 2) k) m, U)) (x : U),
        (((μ n m).app U (tmulSection s t)).1 x :
            Localization.AtPrime x.1.asHomogeneousIdeal.toIdeal) =
          (s.1 x : Localization.AtPrime x.1.asHomogeneousIdeal.toIdeal) * (t.1 x))) :
    (∃ (ePos : ∀ a : ℕ,
          (Proj.twist (MvPolynomial.homogeneousSubmodule (Fin 2) k) 1).tensorPow a ≅
            Proj.twist (MvPolynomial.homogeneousSubmodule (Fin 2) k) (a : ℤ))
        (eNeg : ∀ a : ℕ,
          (dual (Proj.twist (MvPolynomial.homogeneousSubmodule (Fin 2) k) 1)).tensorPow a ≅
            Proj.twist (MvPolynomial.homogeneousSubmodule (Fin 2) k) (-(a : ℤ))),
        (ePos 0).hom =
            Proj.unitToTwist (𝒜 := MvPolynomial.homogeneousSubmodule (Fin 2) k)
                (SetLike.GradedOne.one_mem (A := MvPolynomial.homogeneousSubmodule (Fin 2) k)) ≫
              eqToHom (congrArg
                (Proj.twist (MvPolynomial.homogeneousSubmodule (Fin 2) k)) (by norm_num)) ∧
        ePos 0 = eNeg 0 ∧
        (∀ (a : ℕ) (i : Fin 2),
          (ρ_ _).inv ≫
              (Proj.twist (MvPolynomial.homogeneousSubmodule (Fin 2) k) 1).tensorPow a ◁
                Proj.unitToTwist
                  (𝒜 := MvPolynomial.homogeneousSubmodule (Fin 2) k)
                  (MvPolynomial.X_mem_homogeneousSubmodule_one k i) ≫
              (ePos a).hom ▷ _ ≫ μ (a : ℤ) 1 =
            (ρ_ _).inv ≫
              (Proj.twist (MvPolynomial.homogeneousSubmodule (Fin 2) k) 1).tensorPow a ◁
                Proj.unitToTwist
                  (𝒜 := MvPolynomial.homogeneousSubmodule (Fin 2) k)
                  (MvPolynomial.X_mem_homogeneousSubmodule_one k i) ≫
              (β_ _ _).hom ≫ (ePos (a + 1)).hom ≫ eqToHom (congrArg
                (Proj.twist (MvPolynomial.homogeneousSubmodule (Fin 2) k)) (by omega))) ∧
        (∀ (a : ℕ) (i : Fin 2),
          (ρ_ _).inv ≫
              (dual (Proj.twist (MvPolynomial.homogeneousSubmodule (Fin 2) k) 1)).tensorPow
                (a + 1) ◁ Proj.unitToTwist
                  (𝒜 := MvPolynomial.homogeneousSubmodule (Fin 2) k)
                  (MvPolynomial.X_mem_homogeneousSubmodule_one k i) ≫
              (eNeg (a + 1)).hom ▷ _ ≫ μ (-((a + 1 : ℕ) : ℤ)) 1 ≫
                eqToHom (congrArg
                  (Proj.twist (MvPolynomial.homogeneousSubmodule (Fin 2) k)) (by omega)) =
            (ρ_ _).inv ≫
              (dual (Proj.twist (MvPolynomial.homogeneousSubmodule (Fin 2) k) 1)).tensorPow
                (a + 1) ◁ Proj.unitToTwist
                  (𝒜 := MvPolynomial.homogeneousSubmodule (Fin 2) k)
                  (MvPolynomial.X_mem_homogeneousSubmodule_one k i) ≫
              (β_ _ _).hom ≫
              (α_ (Proj.twist (MvPolynomial.homogeneousSubmodule (Fin 2) k) 1)
                (dual (Proj.twist (MvPolynomial.homogeneousSubmodule (Fin 2) k) 1))
                ((dual (Proj.twist (MvPolynomial.homogeneousSubmodule (Fin 2) k) 1)).tensorPow
                  a)).inv ≫
              dualEvaluation (Proj.twist (MvPolynomial.homogeneousSubmodule (Fin 2) k) 1) ▷
                (dual (Proj.twist (MvPolynomial.homogeneousSubmodule (Fin 2) k) 1)).tensorPow a ≫
              (λ_ _).hom ≫ (eNeg a).hom)) := by sorry

end AlgebraicGeometry
