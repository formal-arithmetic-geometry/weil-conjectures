/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N4
-/
module

public import Sheaf.SixFunctors.ProEtale.DerivedCompletion
public import Mathlib.Algebra.Homology.DerivedCategory.Basic

import Sheaf.Paper.DerivedNakayamaResolution
import Sheaf.AlgebraicGeometry.ProEtaleProductsDerived
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
import Mathlib.CategoryTheory.Triangulated.Pretriangulated
import Mathlib.CategoryTheory.Limits.Shapes.Products

/-!
# Derived Nakayama from the first reduction

Source: blueprint main-20261015, sec-proetale-coefficients,
`sk-lem-pe-derived-nakayama/sk-lem-pe-derived-nakayama-first-reduction.md`
(blueprint: det-pe-derived-nakayama-first-reduction).

The canonical reduction functor at index n is reduction modulo pi^(n+1).
The four conjuncts express vanishing, closure under cones, closure under all integer
shifts, and detection of isomorphisms by the first reduction.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace AlgebraicGeometry.ProEtale

/-- Derived complete complexes vanish if their first reduction vanishes, are closed under
cones and shifts, and have isomorphisms detected by their first reduction.

Source: blueprint main-20261015, first-reduction lemma, Vanishing, Cones and Isomorphisms
paragraphs (blueprint: det-pe-derived-nakayama-first-reduction).

Proof plan:
1. Set R = O_(E,X) and pi = pi_E. The two-term coefficient resolution from
   det-pe-derived-nakayama-resolution identifies the actual n-th reduction of a representative
   M with D_n(M) = Cone(pi^n), differential (dx + pi^n y, -dy). The quotient transition is
   (x,y) |-> (x,pi y), and the augmentation is m |-> (m,0). These are the actual compatible
   quotient maps, not independent choices of identifications of the levels.
2. The signed permutation (b,a,b',a') |-> (b,b',a,-a') identifies D_n(Cone(f)) with
   Cone(D_n(f)). Substitution in the differentials verifies this and compatibility with
   inclusions, signed projections and transitions. The shift comparison is
   (x,y) |-> (x,(-1)^r y). Use the cone conventions of def-weil-abstract-derived-category.
3. For a strict tower N let P be its product, s = 1-T, and H(N) = Cone(s)[-1]. By
   det-pe-products-derived, P is also the derived product and preserves quasi-isomorphisms.
   The rotated cone triangle makes H(N) a derived limit (def-weil-derived-limit).
   The triangle-morphism isomorphism criterion lem-sf-triangle-morphism-iso shows that
   both D_n and H preserve quasi-isomorphisms. Thus F(M) = H((D_n(M))_n) descends through
   localization to an additive derived functor. Its natural comparison is the chain map
   c_M(m) = (((m,0))_n,0), the canonical map of sk-def-pe-derived-completion.
4. Products commute with the two cone summands by def-weil-category-product. The same
   signed permutation identifies H(Cone(f)) with Cone(H(f)): its differential in coordinates
   (v,u) is (dv,-du-sv). The shift comparison is (v,u) |-> (v,(-1)^r u). Combining this
   with step 2 makes F preserve cone triangles and shifts, carrying c_Cone(f) to the cone
   map of c_A,c_B and c_(M[r]) to c_M[r]; the coordinates affected by signs are zero.
5. If K_1 is zero, the successive coefficient triangles of
   det-pe-derived-nakayama-resolution give K_1 -> K_(n+1) -> K_n -> K_1[1]. Induction,
   comparing to the zero distinguished triangle by lem-sf-triangle-morphism-iso, gives
   K_n zero at every positive level.
6. By def-weil-category-product the product of zero objects is zero. The Roos triangle
   of def-weil-derived-limit therefore makes their derived limit zero, again using the
   triangle-morphism criterion. Completeness identifies K with this limit, so K is zero.
7. Represent any distinguished triangle by a localized cone triangle, as in
   def-weil-abstract-derived-category. Steps 2-4 give a distinguished triangle F(T) and
   a morphism (c_K,c_L,c_C): T -> F(T). Transport along the triangle isomorphism: naturality
   gives c_K = F(a)c_A a^(-1), and likewise for the other components, including the shifted
   last square. If K,L are complete, the first two components are invertible, so the third
   is invertible by lem-sf-triangle-morphism-iso. Hence C is complete. For any integer r,
   the shift comparison sigma satisfies sigma c_(K[r]) = c_K[r], so shifts are complete.
8. Complete f to a distinguished triangle (def-weil-triangulated-category). Its cone C
   is complete by step 7. Its first reduction is a distinguished cone triangle by step 2.
   If f_1 is invertible, lem-kun-distinguished-cone-zero makes C_1 zero; steps 5-6 make C
   zero. Apply the same zero-cone criterion to the original triangle to make f invertible.

There is no boundedness assumption, no restriction on X, and no invertibility hypothesis
on l on X. The dependency indexes positive coefficient powers by n+1, so index zero is K_1. -/
theorem derived_nakayama_first_reduction
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (X : Scheme.{u}) :
    (∀ K : DerivedCategory (AdicCompletion.Modules l E X),
      IsDerivedComplete l E X K →
      IsZero ((AdicCompletion.derivedReduction l E X 0).obj K) →
        (∀ n : ℕ, IsZero ((AdicCompletion.derivedReduction l E X n).obj K)) ∧ IsZero K) ∧
    (∀ T : Triangle (DerivedCategory (AdicCompletion.Modules l E X)),
      T ∈ distTriang (DerivedCategory (AdicCompletion.Modules l E X)) →
      IsDerivedComplete l E X T.obj₁ → IsDerivedComplete l E X T.obj₂ →
        IsDerivedComplete l E X T.obj₃) ∧
    (∀ K : DerivedCategory (AdicCompletion.Modules l E X),
      IsDerivedComplete l E X K → ∀ r : ℤ, IsDerivedComplete l E X (K⟦r⟧)) ∧
    (∀ (K L : DerivedCategory (AdicCompletion.Modules l E X)) (f : K ⟶ L),
      IsDerivedComplete l E X K → IsDerivedComplete l E X L →
      IsIso ((AdicCompletion.derivedReduction l E X 0).map f) → IsIso f) := by
  sorry

end AlgebraicGeometry.ProEtale
