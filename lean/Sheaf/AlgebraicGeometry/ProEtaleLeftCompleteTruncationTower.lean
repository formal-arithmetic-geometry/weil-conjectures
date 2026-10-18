/-
Copyright (c) 2026 The SHEAF contributors.
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleLeftComplete
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Sheaf.AlgebraicGeometry.ProEtaleMilnorEpimorphic
import Mathlib.CategoryTheory.Limits.Constructions.EventuallyConstant

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
  have hz (n : ℕ) (hn : (n : ℤ) < -q) :
      IsZero ((milnorCohomologyTower (postnikovTower K) q).obj (op n)) := by
    exact (K.truncGE (-(n : ℤ))).isZero_of_isGE (-(n : ℤ)) q (by omega)
  have hi (n : ℕ) (hn : -q ≤ (n : ℤ)) :
      IsIso (HomologicalComplex.homologyMap (K.πTruncGE (-(n : ℤ))) q) := by
    exact (quasiIsoAt_iff_isIso_homologyMap _ _).mp
      (K.quasiIsoAt_πTruncGE (-(n : ℤ)) q (by omega))
  have hc (n : ℕ) :
      K.πTruncGE (-((n + 1 : ℕ) : ℤ)) ≫ postnikovStep K n =
        K.πTruncGE (-(n : ℤ)) := by
    dsimp [postnikovStep]
    rw [← Category.assoc, CochainComplex.πTruncGE_naturality]
    simp
  have hh (n : ℕ) :
      HomologicalComplex.homologyMap (K.πTruncGE (-((n + 1 : ℕ) : ℤ))) q ≫
        HomologicalComplex.homologyMap (postnikovStep K n) q =
          HomologicalComplex.homologyMap (K.πTruncGE (-(n : ℤ))) q := by
    rw [← HomologicalComplex.homologyMap_comp, hc]
  have he (n : ℕ) : Epi (HomologicalComplex.homologyMap (postnikovStep K n) q) := by
    by_cases hn : (n : ℤ) < -q
    · exact (hz n hn).epi _
    · have := hi n (by omega)
      have := hi (n + 1) (by push_cast; omega)
      have := IsIso.of_isIso_fac_left (hh n)
      infer_instance
  refine ⟨hz, hi, hh, ?_, he, ?_, ?_⟩
  · intro n hn
    exact (hz n hn).eq_of_tgt _ _
  · let := HasDerivedCategory.standard (ringedSiteModules.{max u (t + 1)} R)
    have ht (n : ℕ) :
        Epi ((milnorCohomologyTower (postnikovTower K) q).map
          (homOfLE (Nat.le_succ n)).op) := by
      simpa [milnorCohomologyTower, postnikovTower] using he n
    have := (AlgebraicGeometry.ProEtale.milnor_epimorphic.{u, t, max (u + 1) (t + 2)} X R
      (milnorCohomologyTower (postnikovTower K) q) ht).1
    exact isZero_cokernel_of_epi _
  · let M := milnorCohomologyTower (postnikovTower K) q
    let c : Cone M :=
      { pt := K.homology q
        π := NatTrans.ofOpSequence (fun n ↦
          HomologicalComplex.homologyMap (K.πTruncGE (-(n : ℤ))) q) (by
            intro n
            simpa [M, milnorCohomologyTower, postnikovTower] using (hh n).symm) }
    let N : ℕ := (-q).toNat
    have hN : -q ≤ (N : ℤ) := by dsimp [N]; omega
    have hconst : M.IsEventuallyConstantTo (op N) := by
      intro i f
      have hf : N ≤ i.unop := leOfHom f.unop
      have : IsIso (c.π.app i) := hi i.unop (by omega)
      have : IsIso (c.π.app (op N)) := hi N hN
      exact IsIso.of_isIso_fac_left (c.w f)
    have : IsIso (c.π.app (op N)) := hi N hN
    let hc := hconst.isLimitOfIsIso c
    refine ⟨(hc.conePointUniqueUpToIso (limit.isLimit M)).hom, ?_, inferInstance⟩
    intro n
    exact IsLimit.conePointUniqueUpToIso_hom_comp hc (limit.isLimit M) (op n)

end AlgebraicGeometry.Scheme.ProEt
