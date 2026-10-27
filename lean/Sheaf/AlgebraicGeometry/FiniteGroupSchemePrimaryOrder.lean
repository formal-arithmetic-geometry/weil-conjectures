module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.Defs
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.GroupTheory.Torsion
public import Mathlib.NumberTheory.Padics.PadicVal.Basic

import WeilConjectures.AlgebraicGeometry.GroupScheme.Finite
import Mathlib.GroupTheory.Sylow
import Mathlib.GroupTheory.OrderOfElement

/-!
# Prime-to-characteristic primary order of a finite commutative group scheme

Source: Milne, Algebraic Groups (2017), Proposition 11.3, printed p.210, and
Corollaries 11.30-11.31, printed pp.220-221; finite abelian group assembly.
(blueprint: lem-sfb-finite-group-scheme-primary-order)

The scheme order is `G.hom.finrankΓ`, including nilpotent multiplicities. Rational points
are morphisms from the tensor unit of the category of schemes over the base field.
Their group law is written multiplicatively: `x ^ m = 1` means `m x = 0`.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory
open scoped MonObj

namespace AlgebraicGeometry

/-- The primary subgroup of rational points has the prime-to-characteristic part of the
scheme-theoretic order as its cardinality, and the torsion counts stabilize at that value.

Source: Milne, Algebraic Groups (2017), Proposition 11.3, printed p.210, and
Corollaries 11.30-11.31, printed pp.220-221; the finite abelian group consequence is the
input in Milne, Abelian Varieties, I, proof of Proposition 10.20, printed p.52.
(blueprint: lem-sfb-finite-group-scheme-primary-order)

Proof:
1. Apply `lem-sfb-finite-commutative-group-local-constant-product`: write `G` as the product
   of its finite connected identity component `C` and a constant finite group scheme with
   group `H = G(k)`. If their orders are `d` and `q`, then `d,q ≥ 1` and `N = d*q`.
   This proves both positivity of `N` and finiteness of `H`.
2. In positive characteristic `p`, `lem-pc-flat-field` supplies flatness of `C`, and
   `lem-sc-connected-finite-order` gives `d = p^r`. Since the prime `ℓ` differs from `p`,
   the factor `d` contributes zero to the `ℓ`-valuation, so `v_ℓ(q) = v_ℓ(N)`.
   In characteristic zero, positivity of `N` lets `lem-sc-fg-order-prime-etale` apply;
   `lem-sc-finite-etale-points` then gives `q = N`, yielding the same valuation equality.
3. The elements killed by some power of `ℓ` form a subgroup `P`: the identity is killed,
   inverses are killed by the same power, and if powers `ℓ^a` and `ℓ^b` kill `x` and `y`,
   then `ℓ^(a+b)` kills their product, since `H` is commutative. By its definition every
   subgroup whose elements are killed by powers of `ℓ` is contained in `P`.
4. Thus `P` is a Sylow `ℓ`-subgroup. Apply `lem-sfb-sylow-subgroup-cardinality` to obtain
   `|P| = ℓ^v_ℓ(q) = ℓ^v_ℓ(N)`. This subgroup is Mathlib's `CommGroup.primaryComponent`.
5. By `lem-sfb-finite-additive-group-card-annihilator`, `|P| = ℓ^v_ℓ(N)` kills every
   element of `P`. For `n ≥ max(1, v_ℓ(N))`, multiplying the annihilation exponent by
   `ℓ^(n-v_ℓ(N))` shows that every element of `P` is killed by `ℓ^n`. Conversely any
   element killed by `ℓ^n` is in `P` by definition. Their cardinalities therefore agree.
   If the valuation is zero, `P` has cardinality one and the same argument applies.
-/
theorem finite_commutative_group_scheme_primary_order
    {k : Type u} [Field k] [IsAlgClosed k]
    (G : Over (Spec (.of k))) [GrpObj G] [IsCommMonObj G] [IsFinite G.hom]
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : ℓ ≠ ringChar k) :
    1 ≤ G.hom.finrankΓ ∧
      Finite (𝟙_ (Over (Spec (.of k))) ⟶ G) ∧
      Nat.card (CommGroup.primaryComponent (𝟙_ (Over (Spec (.of k))) ⟶ G) ℓ) =
        ℓ ^ padicValNat ℓ G.hom.finrankΓ ∧
      ∀ n : ℕ, max 1 (padicValNat ℓ G.hom.finrankΓ) ≤ n →
        Nat.card {x : 𝟙_ (Over (Spec (.of k))) ⟶ G // x ^ (ℓ ^ n) = 1} =
          ℓ ^ padicValNat ℓ G.hom.finrankΓ := by
  sorry

end AlgebraicGeometry
