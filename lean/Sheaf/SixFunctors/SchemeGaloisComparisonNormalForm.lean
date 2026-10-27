/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q126
-/
module

public import Sheaf.SixFunctors.SelectedSchemeGaloisComparison
public import Sheaf.AlgebraicGeometry.SchemeCharacteristic
public import Sheaf.AlgebraicGeometry.AbsoluteFrobeniusSite
public import Sheaf.AlgebraicGeometry.ProEtaleFiniteModules
public import Sheaf.Paper.IntegralFinitePullbackComposition
import Sheaf.AlgebraicGeometry.FrobeniusFactorization
import Sheaf.AlgebraicGeometry.FrobeniusTrivializationPullback
import Sheaf.AlgebraicGeometry.ProEtaleDerivedPullbackCoherence
import Sheaf.AlgebraicGeometry.ProEtaleConstantRingComposition
import Sheaf.AlgebraicGeometry.ProEtaleConstantRingMap

/-!
# Normal form of the specified scheme/Galois comparison

Source: main-20261015 blueprint, `prop-trf-scheme-galois-comparison.proof.md`, both
paragraphs and its displayed construction, as used in the final sentence of
`thm-trf-finite-coefficient-map.proof.md`
(blueprint: lem-trf-scheme-galois-comparison-normal-form).

The coefficient convention is the canonical constant-section convention of the recorded
comparison. Composition is written in categorical order. The equality is on the full
unbounded derived category, and the absolute-Frobenius exponent is the single exponent
`D.a * m`. The trivialization is selected from the recorded site theorem together with
its relative-Frobenius projection and module-adjunction-unit normalizations.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures.FiniteFieldDatum

/-- The specified multiplicative comparison at every positive iterate is the compositor
followed by the specified absolute-Frobenius trivialization at exponent `a * m`.
The existential characteristic proof records a conclusion, not an extra assumption.
Both factorizations are equalities of underlying scheme morphisms, so the Galois map
need not be linear over the algebraic closure.

Source: main-20261015, `prop-trf-scheme-galois-comparison.proof.md`, its displayed
construction and second paragraph; final coefficient-naturality sentence of
`thm-trf-finite-coefficient-map.proof.md`
(blueprint: lem-trf-scheme-galois-comparison-normal-form).

Proof, following the six steps of the DAG:
1. The finite-field datum has characteristic p. The structure maps from k_0 to all
   section rings therefore send p to zero, also for the empty scheme.
2. Frobenius factorization gives H_r = sigma^r Phi^r = Phi^r sigma^r. The geometric
   Galois map is inverse to sigma, so cancellation gives both displayed factorizations
   of Phi^r. The absolute iterates commute with all powers of the Galois map.
3. The canonical constant-section coefficient maps compose. The normalized derived
   pullback compositor satisfies associativity, so every reparenthesization below
   identifies with pullback along the same composite scheme morphism.
4. Put beta_r = tau_(ar) after the compositor for Phi^r = g^r H_r. Relative Frobenius
   and the section-unit equation determine tau. The normalization for r=1 says that
   beta_1 is the specified comparison.
5. Write T_r=L(Phi^r)^*, P_r=L(H_r)^*, G_r=L(g^r)^*, d_r:T_r -> P_r G_r, and
   t_r=tau_(ar):P_r -> id. The addition clause of FrobeniusTrivializationPullback gives
   t_(m+n),K = t_n,K after t_m,P_n K, under the canonical compositors. Its arbitrary-
   pullback clause with u=g^m gives t_n,G_m K after e_mn,K = G_m(t_n,K), where
   e_mn:G_m P_n -> P_n G_m is the canonical comparison for the commuting scheme maps.
   The hypotheses are exactly characteristic p, a scheme map g^m, and finite R;
   no linearity of g over k is used. Its relative-Frobenius and section-unit equations
   identify these maps with the specified site theorem's trivializations.
6. Under Step 3, expand d_(m+n) along T_(m+n) -> T_m T_n -> P_m G_m P_n G_n
   -> P_m P_n G_m G_n; the last arrow is P_m(e_mn)G_n. Naturality of t_m at G_m(d_n,K)
   moves the T_n expansion across t_m. In these coordinates, G_m(beta_n,K) after
   beta_m,T_n K is G_m(t_n,G_n K) after t_m,G_m P_n G_n K. Step 5 replaces its
   first factor by t_n,G_m G_n K after e_mn,G_n K. Naturality at that e gives
   e_mn,G_n K after t_m,G_m P_n G_n K = t_m,P_n G_m G_n K after P_m(e_mn,G_n K).
   Thus after the displayed interchange the remaining composite is t_n,G_m G_n K
   after t_m,P_n G_m G_n K, which is t_(m+n),G_(m+n) K by the addition law.
   Restoring compositors proves beta_(m+n),K = G_m(beta_n,K) after beta_m,T_n K.
   Induct on r>=1: Step 4 gives beta_1=kappa; the formula with (m,n)=(r,1), and
   multiplicativity of the specified comparison, give beta_(r+1)=kappa^(r+1).
   Evaluate at K to obtain the equality with the single exponent am trivialization.
   The initial eqToHom only transports along the first scheme-map factorization. -/
theorem schemeGaloisComparison_normal_form
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (X₀ : Over (Spec (CommRingCat.of D.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    (R : Type u) [CommRing R] [Finite R]
    (hR : ∃ n : ℕ, IsUnit (n : D.k) ∧ ∀ r : R, n • r = 0)
    (m : ℕ) (hm : 1 ≤ m) :
    ∃ hX : (D.geometricFiber X₀).left.IsCharacteristic D.p,
      ∃ w : D.schemeFrobeniusIterate X₀ m =
          (D.geometricFiber X₀).left.iterateFrobenius D.prime (hX.2 ⊤) (D.a * m) ≫
            HPow.hPow (α := End (D.geometricFiber X₀).left)
              (D.geometricGaloisFrobenius X₀) m,
        D.schemeFrobeniusIterate X₀ m =
          HPow.hPow (α := End (D.geometricFiber X₀).left)
              (D.geometricGaloisFrobenius X₀) m ≫
            (D.geometricFiber X₀).left.iterateFrobenius D.prime (hX.2 ⊤) (D.a * m) ∧
        ∀ K : proEtaleDerivedCategory (D.geometricFiber X₀).left R,
          (D.canonicalSchemeGaloisComparison X₀ R hR m hm).hom.app K =
            (eqToHom (congrArg (proEtaleConstantRingDerivedPullback R) w)).app K ≫
              (proEtaleConstantRingPullbackComposition
                ((D.geometricFiber X₀).left.iterateFrobenius D.prime
                  (hX.2 ⊤) (D.a * m))
                (HPow.hPow (α := End (D.geometricFiber X₀).left)
                  (D.geometricGaloisFrobenius X₀) m) R).inv.app K ≫
              (proEtaleFrobeniusDerivedIso R
                ((absoluteFrobenius_proEtale_trivialization
                  D.p D.prime R).choose_spec.2.choose_spec.2.choose
                    (D.geometricFiber X₀).left hX (D.a * m))).hom.app
                ((proEtaleConstantRingDerivedPullback R
                  (HPow.hPow (α := End (D.geometricFiber X₀).left)
                    (D.geometricGaloisFrobenius X₀) m)).obj K) := by
  sorry

end WeilConjectures.FiniteFieldDatum
