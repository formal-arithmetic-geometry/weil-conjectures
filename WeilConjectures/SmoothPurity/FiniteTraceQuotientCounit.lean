/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteSmoothAdjunctionData
import WeilConjectures.SmoothPurity.RepresentingTraceClassification

/-! # Quotient compatibility for the actual finite smooth trace

The finite purity square and its exceptional coefficient mate preserve the actual
trace counit, rather than just the isomorphism class of the dualizing object.
Source: current blueprint smooth purity, coefficient reduction and trace construction.
(blueprint: lem-pur-finite-trace-quotient-counit)
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry

namespace AlgebraicGeometry.Etale.FiniteSmoothPurity

/-- The actual finite smooth trace gives the representing Hom bijections, on every
ordinary source test, for a bounded constructible finite-Tor target K.

Proof: the finite smooth-level theorem makes the specified gamma invertible at K.
Its counit transpose is exactly trace by definition. Apply the generic representing
trace theorem to that isomorphism and the actual exceptional adjunction. The finite
orientation and its trace are supplied inputs throughout.
Source: sk-thm-purity-transport, Step 1, and def-pur-smooth-trace.
(blueprint: lem-pur-finite-trace-quotient-counit) -/
theorem finiteTrace_pairing
    {A : Type (u + 1)} [CommRing A] [Finite A]
    {N : ℕ} {hN : 0 < N} {hA : (N : A) = 0}
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (f : X ⟶ Y) [HasCompactification f] [QuasiCompact f] [IsSeparated f] (d : ℕ)
    (s : SmoothLevel A N hN hA f d) (K : DerivedCategoryModule A Y)
    (hK : DerivedCategory.boundedConstructibleFiniteTor A Y K)
    (Q : DerivedCategoryModule A X) :
    Function.Bijective (fun a : Q ⟶ (puritySource A f (line A N hA X d)).obj K ↦
      (rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).map a ≫
        trace A f (line A N hA X d) s.alpha K) := by
  have := s.ordinary_isIso K hK
  exact ProEtale.CondensedRing.representingTrace_of_iso _
    (rightDerivedUpperShriekAdjunction A f)
    (asIso (gamma A f (line A N hA X d) s.alpha K)) Q

/-- The source reduction and the exceptional coefficient-counit comparison transport
precisely the finite smooth trace. All maps are the actual quotient and counit maps.

Proof: apply compact support to the coefficient-purity square of r. Postcompose
with the lower counit. The exceptional coefficient-counit equation of r rewrites
its left side; the definition of proTrace identifies its right side. This requires
only K in the stated constructible finite-Tor domain, and applies also to equal
coefficient levels and to the empty scheme. In particular no uniqueness of an
unnormalized representing trace is used.
Source: sk-lem-sp-reduction, compatibility of the finite orientation and actual
exceptional counits; def-pur-smooth-trace, displayed counit composite.
(blueprint: lem-pur-finite-trace-quotient-counit) -/
theorem finiteTrace_quotient_counit
    {A B : Type (u + 1)} [CommRing A] [Finite A] [CommRing B] [Finite B]
    {phi : A →+* B} {N M : ℕ} {hN : 0 < N} {hM : 0 < M}
    {hA : (N : A) = 0} {hB : (M : B) = 0}
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (f : X ⟶ Y) [HasCompactification f] [QuasiCompact f] [IsSeparated f] (d : ℕ)
    {a : SmoothLevel A N hN hA f d} {b : SmoothLevel B M hM hB f d}
    (r : ReductionData phi f d a b) (K : proCategory A Y) (hK : IsCtf A Y K) :
    (proCompact B f).map
        ((proScalar phi X).map (proGamma A f (line A N hA X d) a.alpha K)) ≫
      proCompactCoefficientInverse phi f ((exceptional A f).obj K) ≫
        (proScalar phi Y).map (proCounit A f K) =
    (proCompact B f).map (proLambda f d r.twist K) ≫
      proTrace B f (line B M hB X d) b.alpha ((proScalar phi Y).obj K) := by
  rw [← (r.pro_counit K hK).2, ← Category.assoc, ← Functor.map_comp,
    (r.pro_purity K hK).2, Functor.map_comp, Category.assoc]
  rfl

end AlgebraicGeometry.Etale.FiniteSmoothPurity
