module

public import WeilConjectures.Algebra.Homology.ModuleHomComplex
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import Mathlib.Algebra.Exact.Basic

/-! # Exactness of total Hom into a bounded injective complex

Source: Stacks Project, Tag 0G4H, bounded-injective truncation comparison,
expanded using Tags 0A8H (total Hom) and 0135 (injective objects).
(blueprint: lem-trf-bounded-injective-total-hom-exact).

The induced maps are specified on every component of every homogeneous cochain.
The complexes in the first argument may be unbounded in both directions.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace CochainComplex

/-- Total Hom into a bounded termwise injective complex preserves degreewise short exactness.
Source: Stacks Project, Tag 0G4H, truncation comparison; Tags 0A8H and 0135.
(blueprint: lem-trf-bounded-injective-total-hom-exact).

Proof: (1) For a chain map f, define (f*z)_s = z_s f^s. This is A-linear.
Expanding the signed total Hom differential gives
D(f*z)_s = d_I z_s f^s - (-1)^r z_(s+1) f^(s+1) d_M
= (d_I z_s - (-1)^r z_(s+1) d_N) f^s = (f*Dz)_s,
using the chain-map identity. Hence the prescribed maps are chain maps, and
j*p* = 0 because pj = 0, by degreewise exactness.
(2) If p*z = 0, surjectivity of every p^s implies z_s = 0, so p* is injective.
(3) If j*z = 0, each z_s vanishes on im(j^s) = ker(p^s). Define y_s(w) = z_s(v)
for a lift p^s(v) = w. The kernel identity makes this independent of the lift;
lifting sums and scalar multiples proves A-linearity. Then p*y = z.
(4) Extend each u_s : U^s -> I^(s+r) across j^s using injectivity of I^(s+r).
Only a-r <= s <= b-r can have nonzero target, so choose these finitely many
extensions and use zero elsewhere. Their product gives v with j*v = u.
These are homogeneous cochains; extensions need not commute with differentials.
Thus the induced maps are short exact in every degree. No source support bound is used. -/
theorem boundedInjective_totalHom_exact
    {A : Type u} [CommRing A]
    (U V W I : CochainComplex (ModuleCat.{u} A) ℤ)
    (j : U ⟶ V) (p : V ⟶ W)
    (hseq : ∀ s : ℤ, Function.Injective (j.f s) ∧
      Function.Exact (j.f s) (p.f s) ∧ Function.Surjective (p.f s))
    (hinj : ∀ q : ℤ, Injective (I.X q))
    (a b : ℤ) (hab : a ≤ b)
    (hbound : ∀ q : ℤ, q < a ∨ b < q → IsZero (I.X q)) :
    ∃ (pstar : moduleHomComplex W I ⟶ moduleHomComplex V I)
      (jstar : moduleHomComplex V I ⟶ moduleHomComplex U I),
      (∀ (r : ℤ) (z : HomComplex.Cochain W I r) (s t : ℤ) (hst : s + r = t),
        ((pstar.f r) z).v s t hst = p.f s ≫ z.v s t hst) ∧
      (∀ (r : ℤ) (z : HomComplex.Cochain V I r) (s t : ℤ) (hst : s + r = t),
        ((jstar.f r) z).v s t hst = j.f s ≫ z.v s t hst) ∧
      (∀ r : ℤ, Function.Injective (pstar.f r) ∧
        Function.Exact (pstar.f r) (jstar.f r) ∧ Function.Surjective (jstar.f r)) := by
  sorry

end CochainComplex
