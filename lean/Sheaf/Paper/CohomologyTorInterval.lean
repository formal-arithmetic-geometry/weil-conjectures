/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q07
-/
module

public import Sheaf.Topology.ProfiniteCondensedRing
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Sheaf.Paper.ConstantModelTorAmplitude
import Sheaf.CategoryTheory.RingedSiteModules
import Sheaf.CategoryTheory.TruncationDescends
import WeilConjectures.CategoryTheory.TruncationTriangle
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom

/-!
# A Tor interval from the Tor intervals of cohomology modules

Source: blueprint main-20261015, sec-proetale-coefficients,
sk-def-localizing-closure/sk-def-localizing-closure-ctf-equals-bc.proof.md,
Complexes paragraph, generalized to a common cohomology Tor interval `[c,d]`
(blueprint: lem-sfb-cohomology-tor-interval).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- A complex with cohomology in `[a,b]`, each cohomology module in degree zero having
Tor amplitude in `[c,d]`, has Tor amplitude in `[a+c,b+d]`. No constructibility is assumed.

Source: blueprint main-20261015, localizing closure, Complexes paragraph
(blueprint: lem-sfb-cohomology-tor-interval).

Proof:
1. In the abelian category of modules over `Λ_X`, represent `K` by a cochain complex `C`.
   Put `T_q = Q(τ_≤q C)`. The cohomology formulas of lem-weil-pbc-truncation-descends
   give `T_(a-1) ≅ 0` and `T_b ≅ K`: the lower truncation is acyclic, and the upper
   truncation inclusion is a quasi-isomorphism.
2. Set `M_q = H^q(K)` in degree zero. The Layer-B relative derived tensor of
   sk-def-sfb-derived-tensor-hom is computed using a K-flat resolution `P` of each test
   module `N`. The degree-r term of `M_q[-q] ⊗ P` is `M_q ⊗ P^(r-q)`. Its differential
   differs from that of `(M_q ⊗ P)[-q]` only by signs, so its degree-r cohomology is
   the degree-(r-q) cohomology of `M_q ⊗ P`. This holds also for negative q. Thus the
   Tor interval of `M_q[-q]` is `[q+c,q+d]`.
3. For `a ≤ q ≤ b`, this interval lies in the common interval `I = [a+c,b+d]`.
   Widening an interval preserves the tensor-test vanishing condition. Zero has amplitude
   in `I`, since relative tensor is additive and tensoring zero gives zero. Isomorphism
   invariance in det-def-sfb-constructible-tor-amplitude gives the base case `T_(a-1)`.
4. Induct on the natural number `m` from 0 to `b-a+1`. For `q = a+m`, the distinguished
   triangle `T_(q-1) → T_q → H^q(K)[-q] → T_(q-1)[1]` of
   lem-weil-pbc-truncation-triangle has first and third terms of amplitude in `I`.
   The extension clause of det-def-sfb-constructible-tor-amplitude gives the middle term
   the same amplitude. At `m = b-a+1` this proves the assertion for `T_b`.
5. Transport along `T_b ≅ K` using isomorphism invariance. Only the cohomological window
   and the common Tor interval were used; no constructibility or geometric finiteness
   hypothesis occurs. -/
theorem torAmplitudeIn_of_cohomology_interval
    (X : Scheme.{u}) (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    (K : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ.X X)))
    (a b c d : ℤ) (hab : a ≤ b) (hcd : c ≤ d)
    (hK : ∀ q : ℤ, q ∉ Set.Icc a b →
      IsZero ((DerivedCategory.homologyFunctor _ q).obj K))
    (hH : ∀ q : ℤ, q ∈ Set.Icc a b →
      DerivedCategory.torAmplitudeIn _ c d
        ((DerivedCategory.singleFunctor _ 0).obj
          ((DerivedCategory.homologyFunctor _ q).obj K))) :
    DerivedCategory.torAmplitudeIn _ (a + c) (b + d) K := by
  sorry

end AlgebraicGeometry.ProEtale
