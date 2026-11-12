/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerCalculus.CoefficientTowerShriekInterfaces

/-!
# The adjunction `Rf_! ⊣ f^!` on constructible towers

Let `E/ℚ_ℓ` be finite and `k` a field in which `ℓ` is invertible. For a smooth morphism
`f : X ⟶ Y` of separated `k`-schemes of finite type, blueprint `proposition-sp-tower-geometric`
asserts that the compactly supported direct image `Rf_{!,•}` on constructible towers
`Dctf(-, 𝒪_E/ℓ^•)` has a right adjoint `f^!_•`, computed level by level by the finite exceptional
inverse images: at level `n` its counit is the finite counit, so `(f^!_• C_•)_n ≃ f^!_{𝒪_E/ℓⁿ} C_n`.

The statement is made in the tower calculus of
`WeilConjectures.AlgebraicGeometry.SpTowerCalculus.CoefficientTowerShriekInterfaces`: the
constructible tower categories are `SpTowerCalculus.C`, and `Rf_{!,•}` restricted to them is
`SpTowerCalculus.restrictedSupport` (for the compactification `c` of `f`). The level `n`
assertion is phrased with representing pairs (blueprint `definition-representing-objects`): the
level `n` of `f^!_• K_•`, with the level `n` of the counit, represents `Hom(Rf_!(-), K_n)` on
`D^b_ctf(X, 𝒪_E/ℓ^{n+1})`. By uniqueness of representing pairs this identifies the level with the
finite exceptional inverse image and the level counit with the finite counit.

## Main statement

* `AlgebraicGeometry.ProEtale.SpTowerCalculus.exists_adjunction_restrictedSupport`: blueprint
  `proposition-sp-tower-geometric`.

The proof (the construction of the trace map of the projective line and the gluing of local
adjunctions in the topos of towers) is not formalised.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.ProEtale.SpTowerCalculus

open Scheme

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- Blueprint `proposition-sp-tower-geometric` (and its clause `proposition-sp-tower-geometric--1`):
**the adjunction `Rf_{!,•} ⊣ f^!_•` on constructible towers** (9.18). For `f : X ⟶ Y` smooth,
separated and of finite type over a field `k` in which `ℓ` is invertible, and a compactification
`c` of `f`, the compactly supported direct image on constructible towers has a right adjoint `G`
whose levels are the finite exceptional inverse images: for every constructible tower `K` on `Y`
and every level `n`, the pair consisting of `(G K)_n` and the level `n` of the counit
`Rf_{!,•} (G K) ⟶ K` represents `Hom(Rf_!(-), K_n)` on `D^b_ctf(X, 𝒪_E/ℓ^{n+1})`, that is
`β ↦ ε_n ∘ Rf_!(β)` is a bijection `Hom(M, (G K)_n) ≃ Hom(Rf_! M, K_n)`. -/
theorem exists_adjunction_restrictedSupport (k : Type u) [Field k] [NeZero (l : k)]
    (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
    (x : SpTowerShriek.OpenExchange l E b o) (hL : SpTowerShriek.Laws l E b o x)
    (q : Coordinates l E b) (h : Preservation l E k b o q) {X Y : Scheme.{u}}
    [X.Over (Spec (.of k))] [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [Y.Over (Spec (.of k))] [IsSeparated (Y ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))] [Smooth f]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] (c : Compactification f)
    (v : ∀ n : ℕ, Evaluation l E b o q c n) :
    ∃ (G : C l E b q Y ⥤ C l E b q X) (adj : restrictedSupport l E k b o q h f c ⊣ G),
      ∀ (K : C l E b q Y) (n : ℕ) (M : proEtaleDerivedCategory X (SpTowerShriek.R l E n)),
        spFiniteConstructibleTor X (SpTowerShriek.R l E n) M →
        Function.Bijective fun β : M ⟶
            (spDerivedCoefficientEvaluation l E X (q.abelian X) n).obj (G.obj K).obj ↦
          (reductionCompactSupport (SpTowerShriek.R l E n) c.i c.g).map β ≫
            (v n).comparison.inv.app (G.obj K).obj ≫
            (spDerivedCoefficientEvaluation l E Y (q.abelian Y) n).map (adj.counit.app K).hom := by
  sorry

end AlgebraicGeometry.ProEtale.SpTowerCalculus
