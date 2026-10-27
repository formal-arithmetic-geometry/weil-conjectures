module

public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Sheaf.Algebra.Homology.DerivedCoinductionAdjunction
public import Sheaf.Algebra.Homology.OrdinaryDerivedChangeOfRings
import Sheaf.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral
import Sheaf.Algebra.Homology.CartierQuotientDerivedDual
import Sheaf.Algebra.Homology.PerfectAlgebraCoinductionTensor
import Sheaf.Algebra.Homology.DerivedTensorSecondFactorFunctor
import Mathlib.CategoryTheory.Adjunction.Unique
import WeilConjectures.Algebra.Homology.KFlatModuleBaseChange

/-! # Derived coinduction cancels added evaluation variables

Source: Stacks Project, dualizing.tex, Tags 0BZH and 0BZJ, the Cartier quotient
calculation and induction on added variables
(blueprint: lem-trf-coinduction-polynomial-refinement).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace ModuleCat

/-- Adding ordered polynomial variables and evaluating them at `g` cancels derived
coinduction against derived scalar extension with the indicated shifts. The comparisons
are natural in the entire unbounded derived category, and may depend on `g` and its order.
No flatness, surjectivity of `ψ`, Noetherianity, or boundedness is assumed.
Source: Stacks Project, dualizing.tex, Tags 0BZH and 0BZJ
(blueprint: lem-trf-coinduction-polynomial-refinement).

Proof:
1. For one variable, write S = T[y], z = y - g. Polynomial division by the monic
polynomial z gives ker(eval g) = (z), and constants prove surjectivity. Comparing highest
coefficients proves multiplication by z injective, even over rings with zero divisors.
Thus S --z--> S --> T is a finite free resolution, so T[0] is perfect over S
(def-pc-perfect-ring-complex). If S is zero the same resolution and identifications hold.
2. By lem-trf-cartier-quotient-derived-dual, coinduction of S[0] is the dual of
(z) tensor T, shifted by -1. The generator z trivializes that dual as T. Apply
lem-trf-perfect-algebra-coinduction-tensor and the functoriality of
lem-pc-derived-tensor-second-factor-functor to obtain C_T^S(M) ≅ (M tensor_S^L T)[-1]
in D(T), naturally in M. Moving the shift across total tensor multiplies the summand
in first-factor degree a by (-1)^a, respecting differentials and T-actions.
3. The adjunction of lem-trf-derived-coinduction-adjunction and right-adjoint uniqueness
(lem-cat-right-adjoint-composition) identify coinduction along a composite with iterated
coinduction. On K-injectives coinduction commutes with shifts; shifted K-injectives are
K-injective by testing against oppositely shifted acyclic complexes. Evaluation at 1
identifies identity coinduction with the identity (def-trf-derived-coinduction).
4. Induct on m, successively evaluating the last variable. The base m = 0 uses identity
coinduction and identity scalar extension. The successor uses Steps 2 and 3. For a K-flat
representative F, extension stays K-flat by lem-pc-kflat-extension-of-scalars. The tensor
comparison of lem-pc-derived-tensor-second-factor-functor identifies iterated extension
with direct extension by (f tensor a) tensor p ↦ f tensor eval(a)p, with inverse
f tensor p ↦ (f tensor 1) tensor p. Balancing, differentials and functoriality hold directly;
resolution independence comes from the same tensor comparison. This gives the second
asserted natural isomorphism for every m.
5. Apply Step 4 to M = K tensor_R^L Q. Choose a K-flat R-representative F and extend
it to Q, again using lem-pc-kflat-extension-of-scalars. The same balanced maps identify
(K tensor_R^L Q) tensor_Q^L P with K tensor_R^L P, naturally in K, without flatness of P/R.
6. Compose coinduction along Q --> P --> A using Step 3, apply C_A^P to Step 5,
commute coinduction with shifts, and cancel [-m][m]. This yields the first natural
isomorphism in D(A). Ordered generators fix the trivializations and induction order;
no independence from these choices is asserted. -/
theorem coinduction_polynomial_refinement
    {R P A : Type u} [CommRing R] [CommRing P] [CommRing A]
    (ρ : R →+* P) (ψ : P →+* A) (m : ℕ) (g : Fin m → P) :
    Nonempty
      ((ordinaryDerivedExtendScalars ((MvPolynomial.C : P →+* MvPolynomial (Fin m) P).comp ρ)
          ⋙ derivedCoinduction (ψ.comp (MvPolynomial.eval g)))
          ⋙ shiftFunctor (DerivedCategory (ModuleCat.{u} A)) (m : ℤ) ≅
        ordinaryDerivedExtendScalars ρ ⋙ derivedCoinduction ψ) ∧
    Nonempty
      (derivedCoinduction (MvPolynomial.eval g) ≅
        ordinaryDerivedExtendScalars (MvPolynomial.eval g) ⋙
          shiftFunctor (DerivedCategory (ModuleCat.{u} P)) (-(m : ℤ))) := by
  sorry

end ModuleCat
