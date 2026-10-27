module

public import Mathlib.LinearAlgebra.RootSystem.Chain

/-!
# Squared lengths of adjacent roots in a root string

Source: Milne, Algebraic Groups (2017), Appendix C.19–C.20, printed p. 611,
and Section g, printed pp. 621–622, table (180) and the rank-two root diagrams
(blueprint: lem-sfb-root-string-adjacent-length-ratio).

The adjacent-root identity is an agent-formulated consequence of these diagrams.
The bottom coefficient measures subtraction and the top coefficient measures addition.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u v w

namespace RootPairing

/-- Squared-length ratio for two adjacent roots in an independent root string.

Source: Milne, Algebraic Groups (2017), Appendix C.19–C.20, printed p. 611,
and Section g, printed pp. 621–622, table (180) and the rank-two diagrams
(blueprint: lem-sfb-root-string-adjacent-length-ratio).

Proof plan:
1. Write alpha = root i, beta = root j, gamma = root k = alpha + beta,
   A = b(alpha,alpha), B = b(beta,beta), D = b(gamma,gamma), p = chainBotCoeff i j,
   q = chainTopCoeff i j, and t = p-q in the integers. All roots are nonzero,
   because each evaluates to 2 on its coroot; hence A,B,D are positive.
   For any root a and vector x, put c = <x,a^vee>. Reflection invariance gives
   b(x,a) = b(x-c a,-a) = -b(x,a)+c b(a,a), so 2b(x,a) = c b(a,a).
2. By `lem-sfb-root-string-endpoint-difference`, <beta,alpha^vee> = t.
   Symmetry and bilinearity give 2b(alpha,beta) = t A and D = B+(t+1)A.
   By `lem-sfb-root-string-integer-interval` at z=1, q is at least 1.
   By `lem-sfb-root-string-length-bound`, p+q is at most 3. Thus (p,q) is
   (0,1), (0,2), (0,3), (1,1), (1,2), or (2,1).
3. For (0,1) and (1,2), t=-1, D=B and q=p+1, giving the identity.
4. For (0,2) and (0,3), t=-q and D=B-(q-1)A>0, so B>(q-1)A.
   The Cartan integer r=<alpha,beta^vee> satisfies rB=-qA. These inequalities
   imply -2<r<0, hence r=-1, B=qA and D=A. Therefore qD=(p+1)B.
5. For (1,1) and (2,1), t=p-1 and D=B+pA. The Cartan integer
   s=<alpha,gamma^vee> satisfies sD=(p+1)A. Positivity and p=1 or p=2
   give 0<s<2, hence s=1. Thus D=(p+1)A and B=A, proving qD=(p+1)B. -/
theorem adjacent_root_length_ratio
    {I : Type u} [Finite I]
    {V : Type v} [AddCommGroup V] [Module ℚ V]
    {W : Type w} [AddCommGroup W] [Module ℚ W]
    (P : RootPairing I ℚ V W) [P.IsCrystallographic] [P.IsReduced]
    (b : LinearMap.BilinForm ℚ V) (hsymm : b.IsSymm)
    (hpos : ∀ x : V, x ≠ 0 → 0 < b x x)
    (hinv : ∀ l : I, b.IsOrthogonal (P.reflection l))
    (i j k : I) (hij : LinearIndependent ℚ ![P.root i, P.root j])
    (hk : P.root k = P.root i + P.root j) :
    (P.chainTopCoeff i j : ℚ) * b (P.root k) (P.root k) =
      ((P.chainBotCoeff i j : ℚ) + 1) * b (P.root j) (P.root j) := by
  sorry

end RootPairing
