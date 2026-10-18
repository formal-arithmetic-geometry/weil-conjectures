/-
Copyright (c) 2026 The SHEAF contributors.
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleLeftComplete
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Sheaf.AlgebraicGeometry.ProEtaleMilnorEpimorphic

/-!
# Cohomology of the truncation tower

Source: Weil conjectures blueprint, main-20261015,
`sec-proetale-coefficients/sk-prop-pe-left-complete/
det-pe-left-complete-truncation-tower.md` (blueprint:
`det-pe-left-complete-truncation-tower`).

The tower is the canonical lower truncation tower `postnikovTower`; its cohomology
tower and degree-one derived inverse limit are the existing Milnor constructions.
-/

@[expose] public noncomputable section

set_option autoImplicit false

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe t u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.ProEt

/-- The cohomology of the canonical truncation tower is eventually constant, and its
degree-one derived inverse limit vanishes.
Source: Weil conjectures blueprint, main-20261015,
sec-proetale-coefficients/sk-prop-pe-left-complete/
det-pe-left-complete-truncation-tower.md (blueprint: det-pe-left-complete-truncation-tower).

Proof:
1. Put a = -n. By def-kun-truncations (Stacks Tag 0118), `K.truncGE a` is zero below
degree a, is coker d^(a-1) in degree a and K^i above it. Its cohomology vanishes below a;
in degree a the kernel of K^a / im d^(a-1) -> K^(a+1) is ker d^a / im d^(a-1), and above
a the kernel/image quotients are unchanged. These are the cohomology objects of
def-weil-abstract-derived-category, so u_n = H^q(K.πTruncGE a) is an isomorphism when
n >= -q, and its target is zero otherwise.
2. Write M_n = H^q(K.truncGE (-n)) and t_n = H^q(postnikovStep K n). The quotient
K -> tau_(>=-(n+1)) K followed by postnikovStep K n is K.πTruncGE (-n): the identity
above degree -n, the quotient in degree -n and zero below. Functoriality gives
t_n u_(n+1) = u_n. For n >= -q both u_n and u_(n+1) are isomorphisms, so
u_n^(-1) t_n u_(n+1) = 1; otherwise M_n = 0 and t_n = 0. Hence every t_n is an
epimorphism. Apply det-pe-milnor-epimorphic (`milnor_epimorphic`) to this tower to get
R^1 lim M_n = 0; clause 2 of det-pe-milnor-sequence identifies it with
`milnorTowerCokernel`.
3. Let N = max(0, -q). The u_n form a cone over the tower. For a cone (f_n : A -> M_n)
put f = u_N^(-1) f_N. For n < N, M_n = 0 and u_n f = f_n. For n >= N, the composite
transition t_(n,N) is an isomorphism with t_(n,N) f_n = f_N and t_(n,N) u_n = u_N, so
u_n f = f_n. Uniqueness follows from the component at N. Thus the cone is a limit cone,
and the induced map H^q(K) -> lim M_n, whose components are the u_n, is an
isomorphism. -/
theorem truncation_tower_cohomology
    (X : Scheme.{t})
    (R : Sheaf (topology X) RingCat.{max u (t + 1)})
    (K : CochainComplex (ringedSiteModules.{max u (t + 1)} R) ℤ)
    (q : ℤ) :
    (∀ n : ℕ, (n : ℤ) < -q →
      IsZero ((milnorCohomologyTower (postnikovTower K) q).obj (op n))) ∧
    (∀ n : ℕ, -q ≤ (n : ℤ) →
      IsIso (HomologicalComplex.homologyMap
        (K.πTruncGE (-(n : ℤ))) q)) ∧
    (∀ n : ℕ,
      HomologicalComplex.homologyMap
          (K.πTruncGE (-((n + 1 : ℕ) : ℤ))) q ≫
        HomologicalComplex.homologyMap (postnikovStep K n) q =
      HomologicalComplex.homologyMap (K.πTruncGE (-(n : ℤ))) q) ∧
    (∀ n : ℕ, (n : ℤ) < -q →
      HomologicalComplex.homologyMap (postnikovStep K n) q = 0) ∧
    (∀ n : ℕ, Epi (HomologicalComplex.homologyMap (postnikovStep K n) q)) ∧
    IsZero (milnorTowerCokernel (milnorCohomologyTower (postnikovTower K) q)) ∧
    ∃ f : (HomologicalComplex.homologyFunctor
        (ringedSiteModules.{max u (t + 1)} R) (ComplexShape.up ℤ) q).obj K ⟶
        limit (milnorCohomologyTower (postnikovTower K) q),
      (∀ n : ℕ,
        f ≫ limit.π (milnorCohomologyTower (postnikovTower K) q) (op n) =
          HomologicalComplex.homologyMap
            (K.πTruncGE (-(n : ℤ))) q) ∧ IsIso f := by
  sorry

end AlgebraicGeometry.Scheme.ProEt
