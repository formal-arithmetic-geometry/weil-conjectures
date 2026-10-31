/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProfiniteFiniteConstantLocalModel
public import WeilConjectures.AlgebraicGeometry.FiniteProperLocalizing
public import WeilConjectures.AlgebraicGeometry.CondensedModuleDerivedPushpull
public import WeilConjectures.AlgebraicGeometry.CohomologicalDimension

/-!
# Open direct image with a relative cohomological-dimension Tor bound

Source: literature/blueprint/latest/blueprint/part-six-operations/
sec-constructibility-upper-shriek/sec-ctf-finite-geometric-restriction/
sk-cor-sf-direct-image-ctf/_section.md (blueprint: sk-cor-sf-direct-image-ctf).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry Scheme
open scoped CategoryTheory.Functor CategoryTheory.Obj
open scoped AlgebraicGeometry.ProEtale.CondensedRing

namespace AlgebraicGeometry.ProEtale

/-- The open direct image over the pro-etale site preserves finite-coefficient
constant-model constructibility and finite Tor amplitude, with the upper Tor endpoint
shifted by any bound for the relative ell-cohomological dimension.

Source: literature/blueprint/latest/blueprint/part-six-operations/sec-constructibility-upper-shriek/
sec-ctf-finite-geometric-restriction/sk-cor-sf-direct-image-ctf/_section.md,
node statement; Stacks Project, Tags 0F10, 0F12, and 0F4M
(blueprint: sk-cor-sf-direct-image-ctf).

Conventions: `k` is finite or algebraically closed with `ℓ ≠ char k`, schemes are
separated of finite type over `k` (blueprint sec-conventions, prose-01-09; part six,
prose-P1-01), and `A` is a finite commutative `ℓ`-primary ring.

Proof (the four steps of the node):
1. `X` and `U` are Noetherian, so `j` is quasi-compact. `Rj_*K` is bounded constructible by
   sk-cor-geo-open-finiteness. By sk-cor-pe-finite-tor-comparison, `K ≅ ν_U^* K_et` with
   `K_et ∈ D^b_ctf(U_et, A)`, and by lem-exc-comparison-tor-interval `K_et` has Tor
   amplitude in `[a,b]` exactly when `K` does. `cd_ℓ(j)` is finite by
   sk-prop-classical-inputs, so some `d ≥ cd_ℓ(j)` exists.
2. For an `A`-module `M`, the projection map
   `(Rj_* K_et) ⊗ᴸ M_X → Rj_*(K_et ⊗ᴸ M_U)` in `D(X_et, A)` is an isomorphism: for
   quasi-compact etale `V → X` and `V_U = V ×_X U`, the torsion cohomological dimension of
   `V` and `V_U` is finite (det-prop-sf-finiteness, det-base-field-cd-finite-field), so
   lem-kun-0f12 gives `RΓ(V, -)` of the projection map as an isomorphism; hence its cone
   has vanishing cohomology sheaves and is zero.
3. At a geometric point `x̄`, lem-sfb-etale-derived-tensor-stalk and step 2 identify
   `(Rj_* K_et)_x̄ ⊗ᴸ M` with a stalk of `Rj_*(K_et ⊗ᴸ M_U)`. The complex
   `K_et ⊗ᴸ M_U` has `ℓ`-power torsion cohomology sheaves in `[a,b]`; by sk-def-cd,
   `R^q j_*` vanishes on them for `q > d` (and for `q < 0`), so truncation triangles put
   `Rj_*(K_et ⊗ᴸ M_U)` in `[a,b+d]`. The stalk criterion lem-sf-etale-stalk-tor-test gives
   Tor amplitude `[a,b+d]` of `Rj_* K_et`.
4. sk-prop-pe-unbounded-classical gives `Rj_* K ≅ ν_X^* Rj_{et,*} K_et`, and
   lem-exc-comparison-tor-interval transfers Tor amplitude `[a,b+d]` to it, tested against
   every module sheaf on `X_proet` (sk-def-sfb-constructible). With step 1 this gives both
   conjuncts. The empty scheme, the zero ring, `j = id` and `a > b` need no separate case.
-/
theorem openDirectImage_preserves_constantModelConstructibleFiniteTor
    (ℓ : ℕ) [Fact ℓ.Prime]
    (k : Type u) [Field k]
    (_hbase : Finite k ∨ IsAlgClosed k)
    (_hchar : ringChar k ≠ ℓ)
    {U X : Scheme.{u}}
    [U.Over (Spec (.of k))] [X.Over (Spec (.of k))]
    [LocallyOfFiniteType (U ↘ Spec (.of k))]
    [QuasiCompact (U ↘ Spec (.of k))] [IsSeparated (U ↘ Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))] [IsSeparated (X ↘ Spec (.of k))]
    (j : U ⟶ X) [j.IsOver (Spec (.of k))] [IsOpenImmersion j]
    [QuasiCompact j]
    (A : Type u) [CommRing A] [Finite A]
    (_hA : ∃ n : ℕ, 1 ≤ n ∧ (ℓ ^ n : ℕ) • (1 : A) = 0)
    : (∀ K : ConstantModelConstructibleFiniteTor (finiteDiscreteCondensedCoefficient A) U,
        (constantModelBoundedConstructible (finiteDiscreteCondensedCoefficient A) X ⊓
          DerivedCategory.finiteTorAmplitude _)
          ((R(AlgebraicGeometry.ProEtale.CondensedRing.lowerStar
            (finiteDiscreteCondensedCoefficient A) j)).obj K.obj)) ∧
      ∀ (d : ℕ),
        relativeCohomologicalDimension ℓ (Fact.out : Nat.Prime ℓ) j ≤ (d : WithTop ℕ) →
        ∀ (a b : ℤ)
          (K : DerivedCategory
            (CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1})
              (condensedRingObj (finiteDiscreteCondensedCoefficient A) U))),
          (constantModelBoundedConstructible (finiteDiscreteCondensedCoefficient A) U K ∧
            DerivedCategory.torAmplitudeIn _ a b K) →
          constantModelBoundedConstructible (finiteDiscreteCondensedCoefficient A) X
              ((R(AlgebraicGeometry.ProEtale.CondensedRing.lowerStar
                (finiteDiscreteCondensedCoefficient A) j)).obj K) ∧
            DerivedCategory.torAmplitudeIn _ a (b + (d : ℤ))
              ((R(AlgebraicGeometry.ProEtale.CondensedRing.lowerStar
                (finiteDiscreteCondensedCoefficient A) j)).obj K) := by
  sorry

end AlgebraicGeometry.ProEtale
