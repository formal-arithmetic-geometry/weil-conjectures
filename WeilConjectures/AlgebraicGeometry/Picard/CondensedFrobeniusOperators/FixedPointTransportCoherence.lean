/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Picard.TraceFormulaCoefficientConventions.TraceFormulaFrobeniusOperators
public import WeilConjectures.AlgebraicGeometry.ProEtale.Derived.ProEtaleDerivedPullbackCoherence
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtalePullbackStalkCoherence

/-!
# Coherence of fixed-point Frobenius stalk transport

Source: latest blueprint, `lem-trf-frobenius-degree-formula.proof.md`, Step 1,
iteration at one lift (blueprint: lem-trf-fixed-point-transport-coherence).
The stalk convention is point sections after derived pullback. The equality is an
identity of natural isomorphisms on strict Weil complexes, so it includes naturality
in every morphism of strict Weil complexes.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] WeilConjectures.integralOperationsSiteSmall
  WeilConjectures.integralReductionSiteEssentiallySmall

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj
open scoped AlgebraicGeometry.ProEtale.CondensedRing.CachedModInstances

namespace WeilConjectures.CondensedFrobeniusOperators

open AlgebraicGeometry.ProEtale.CondensedRing
open AlgebraicGeometry.ProEtale.CondensedRing.CohomologyTransport

/-- Clause (2) of the Frobenius-operator definition at an arbitrary fixed geometric
point, as a natural isomorphism in the underlying coefficient complex. This is the
same construction as `fixedPointReturn`, now before choosing a rational-point
presentation or a Weil structure. The three factors are the fixed-point equality,
the canonical derived pullback compositor, and the specified scheme/Galois comparison;
point sections then give the stalk coefficient complex.

Source: latest blueprint, `def-trf-frobenius-operators.md`, clause (2), and
`lem-trf-frobenius-degree-formula.proof.md`, Step 1
(blueprint: lem-trf-fixed-point-transport-coherence). -/
def fixedPointStalkTransport
    (F : WeilConjectures.FiniteFieldDatum.{u})
    (Y₀ : Over (Spec (CommRingCat.of F.k₀))) [IsSeparated Y₀.hom]
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
    (ell : ℕ) [Fact ell.Prime] (E : Type u) [Field E]
    [Algebra (Padic ell) E] [FiniteDimensional (Padic ell) E]
    (n : ℕ) (hn : 1 ≤ n)
    (z : Spec (.of F.k) ⟶ (F.geometricFiber Y₀).left)
    (m : ℕ) (hm : 1 ≤ m) (hz : z ≫ F.schemeFrobeniusIterate Y₀ m = z) :
    L (finiteCoefficient ell E n) z ⋙ Γ (finiteCoefficient ell E n) (Spec (.of F.k)) ≅
      L (finiteCoefficient ell E n)
          ((geometricFrobeniusGeometry F Y₀).h.pow m).hom ⋙
        (L (finiteCoefficient ell E n) z ⋙
          Γ (finiteCoefficient ell E n) (Spec (.of F.k))) :=
  let Λ := finiteCoefficient ell E n
  Functor.isoWhiskerRight
      ((eqToIso (congrArg (L Λ) hz)).symm ≪≫
        leftDerivedUpperStarComp Λ z (F.schemeFrobeniusIterate Y₀ m) ≪≫
        Functor.isoWhiskerRight
          (finiteSchemeGaloisComparisonFunctor F Y₀ ell E n hn m hm) (L Λ z))
      (Γ Λ (Spec (.of F.k))) ≪≫
    Functor.associator
      (L Λ ((geometricFrobeniusGeometry F Y₀).h.pow m).hom)
      (L Λ z) (Γ Λ (Spec (.of F.k)))

/-- The transport at `a+b` is transport at `a`, transport at `b` evaluated on the
`a`-fold pulled-back complex, and the canonical Galois pullback compositor. Equality
of natural isomorphisms after the strict-Weil forgetful functor states the equation
for every strict Weil complex and its naturality for every strict Weil morphism.
The second transport uses only the underlying pulled-back complex, as in the
construction of `fixedPointReturn`; it does not require choosing a new Weil map.

Source: latest blueprint, `lem-trf-frobenius-degree-formula.proof.md`, Step 1
(blueprint: lem-trf-fixed-point-transport-coherence).

Proof: write `P_m = L(Phi^m)^*`, `G_m = L(g^m)^*`, and `S = Fib_s Lz^*`.
The fixed-point transport is `tau_m = S(kappa_m) rho_m`. Pullback associativity at
`z, Phi^b, Phi^a`, using the three fixed-point equalities, gives
`rho_(a+b) = S(C_P) rho_b(P_a(-)) rho_a`. The normalized multiplicative comparison
says `kappa_(a+b) C_P = C_G kappa_b(G_a(-)) P_b(kappa_a)`.
Substitute the first equation in `tau_(a+b)`, then the second. Naturality of
`rho_b` at `kappa_a` moves `P_b(kappa_a)` across `rho_b`, leaving
`S(C_G) tau_b(G_a(-)) tau_a`. All factors are natural isomorphisms; precomposing
with the strict-Weil forgetful functor gives exactly the claimed natural identity.
The compositors are the normalized derived pullback comparisons, not chosen maps. -/
theorem fixedPointStalkTransport_add
    (F : WeilConjectures.FiniteFieldDatum.{u})
    (Y₀ : Over (Spec (CommRingCat.of F.k₀))) [IsSeparated Y₀.hom]
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
    (ell : ℕ) [Fact ell.Prime] (_hEll : ell ≠ F.p) (E : Type u) [Field E]
    [Algebra (Padic ell) E] [FiniteDimensional (Padic ell) E]
    (n : ℕ) (hn : 1 ≤ n)
    (z : Spec (.of F.k) ⟶ (F.geometricFiber Y₀).left)
    (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hza : z ≫ F.schemeFrobeniusIterate Y₀ a = z)
    (hzb : z ≫ F.schemeFrobeniusIterate Y₀ b = z)
    (hzab : z ≫ F.schemeFrobeniusIterate Y₀ (a + b) = z) :
    let Λ := finiteCoefficient ell E n
    let G := fun m ↦ ((geometricFrobeniusGeometry F Y₀).h.pow m).hom
    let S := L Λ z ⋙ Γ Λ (Spec (.of F.k))
    let W := FiniteStrictWeilComplex.forget (F := F) (Y₀ := Y₀)
      (ell := ell) (E := E) (n := n) (hn := hn)
    let τ := fun m hm hz ↦ fixedPointStalkTransport F Y₀ ell E n hn z m hm hz
    ∃ hG : G b ≫ G a = G (a + b),
      Functor.isoWhiskerLeft W (τ (a + b) (by omega) hzab) =
        Functor.isoWhiskerLeft W
          (τ a ha hza ≪≫
            Functor.isoWhiskerLeft (L Λ (G a)) (τ b hb hzb) ≪≫
            (Functor.associator (L Λ (G a)) (L Λ (G b)) S).symm ≪≫
            Functor.isoWhiskerRight
              ((leftDerivedUpperStarComp Λ (G b) (G a)).symm ≪≫
                eqToIso (congrArg (L Λ) hG)) S) := by
  sorry

end WeilConjectures.CondensedFrobeniusOperators
