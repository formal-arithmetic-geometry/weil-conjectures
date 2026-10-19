/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q93
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import WeilConjectures.RingTheory.IsRegularSystemOfParameters
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.Topology.Irreducible
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import WeilConjectures.Topology.PresheafModuleStalkFunctor

import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.RingTheory.Ideal.GoingDown
import WeilConjectures.Mathlib.RingTheory.RegularLocalRing.Defs
import Sheaf.AlgebraicGeometry.EtaleSmoothZeroDimensionalFibres
import Sheaf.RingTheory.RegularRingSmoothAscent
import Sheaf.RingTheory.RegularLocalUFDBoundaryFactorization
import Sheaf.AlgebraicGeometry.IsRegularScheme

/-!
# Étale local coordinates for regular boundary components

Source: Illusie–Laszlo–Orgogozo, Exposé VIII, Remark 4.2.2(i), printed p. 118,
and Lemma 4.2.9, printed p. 121
(blueprint: lem-trf-etale-component-coordinate-identification).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Regular reduced boundary components match the parameter hyperplanes after shrinking.
Equalities of ideal sheaves specify equality as closed subschemes, including all intersections.
The last clause concerns the original `W`, independently of the shrinking.

Source: Illusie–Laszlo–Orgogozo, Exposé VIII, Remark 4.2.2(i), printed p. 118,
and Lemma 4.2.9, printed p. 121
(blueprint: lem-trf-etale-component-coordinate-identification).

Proof:
1. Discard the finitely many components missing `v w`. The remaining reduced component ideals
are exactly the minimal primes over the boundary ideal in the target local ring
(def-weil-irreducible-components, def-weil-closed-immersion, def-pc-reduced-scheme,
def-weil-pbc-localization-at-prime).
2. Étale base change is smooth. Regularity ascends along the resulting smooth affine maps,
so the local quotients by the pulled-back component ideals are regular local domains
(lem-weil-pbc-etale-scheme-base-change, lem-weil-pbc-etale-smooth-zero-dimensional-fibres,
def-sbc-smooth-morphisms, lem-weil-pbc-regular-ring-smooth-ascent, lem-sc-regular-local-domain).
3. Flat going-down applied to the zero primes gives contraction back to the original component
primes, so distinct components give distinct primes upstairs (def-weil-etale-morphism,
def-weil-flat-morphism, lem-sc-flat-going-down).
4. The parameter elements are prime by regular-local unique factorization. Their cotangent
classes form a basis, so the principal primes are pairwise incomparable and are exactly the
minimal primes over the parameter product, including the empty-product case
(lem-trf-regular-local-ufd-boundary-factorization,
lem-weil-pbc-regular-local-cotangent-dimension, def-weil-pbc-regular-system-of-parameters).
5. Pulling back the finite union of component supports shows that each parameter prime contains
one of the component primes; primality and incomparability give equality.
6. Conversely each component prime contains a parameter prime; contraction and minimality force
it to be the matching component prime. This gives the bijection, also for `r = 0`.
7. The étale source is locally Noetherian. Finite generators and finitely many localization
denominators spread all local ideal equalities to a common open neighbourhood
(pqf-lem-locnoeth-lft, pqf-def-locnoeth, def-weil-closed-immersion,
def-weil-pbc-localization-at-prime).
8. Scheme-theoretic intersections have the sums of the component ideals. Pullback commutes with
these sums, giving the assigned coordinate equations or the unit ideal for a missing component
(def-pc-fibre-product, def-weil-closed-immersion).
9. For every generic point of a component of the full pullback, use an affine flat map from a
domain. Flat going-down forces the minimal prime upstairs to contract to zero, so its image is
the generic point of the original component (lem-weil-pbc-etale-scheme-base-change,
def-pc-integral-scheme, lem-weil-pbc-flat-morphism-affine-criterion, lem-sc-flat-going-down).
-/
theorem etaleComponentCoordinateIdentification
    {X D W : Scheme.{u}} [IsLocallyNoetherian X]
    (i : D ⟶ X) [IsClosedImmersion i] [IsReduced D]
    {m : ℕ} (Da : Fin m → Scheme.{u}) (c : ∀ a, Da a ⟶ D)
    [∀ a, IsClosedImmersion (c a)] [∀ a, IsReduced (Da a)]
    (hregular : ∀ (a : Fin m) (y : Da a),
      ∃ U : (Da a).affineOpens, y ∈ U.1 ∧ IsRegularRing Γ(Da a, U))
    (hcomponents : ∀ a, Set.range (c a) ∈ irreducibleComponents D)
    (hcomplete : ∀ Z : Set D, Z ∈ irreducibleComponents D →
      ∃! a : Fin m, Set.range (c a) = Z)
    (v : W ⟶ X) [Etale v] (w : W)
    {d r : ℕ} [IsRegularLocalRing (W.presheaf.stalk w)]
    (hdim : ringKrullDim (W.presheaf.stalk w) = (d : WithBot ℕ∞))
    (t : Fin d → W.presheaf.stalk w)
    (ht : IsLocalRing.IsRegularSystemOfParameters (List.ofFn t))
    (rle : r ≤ d) (V : W.Opens) (hwV : w ∈ V)
    (s : Fin d → Γ(W, V))
    (hs : ∀ j, W.presheaf.germ V w hwV (s j) = t j)
    (hboundary : i.ker.comap (V.ι ≫ v) =
      Scheme.IdealSheafData.ofIdealTop
        (Ideal.span {V.topIso.inv (∏ j : Fin r, s (Fin.castLE rle j))})) :
    (∃ (U : W.Opens) (hUV : U ≤ V), w ∈ U ∧
      ∃ e : {a : Fin m // v w ∈ Set.range (c a ≫ i)} ≃ Fin r,
        (∀ a : {a : Fin m // v w ∈ Set.range (c a ≫ i)},
          (c a.1 ≫ i).ker.comap (U.ι ≫ v) =
            Scheme.IdealSheafData.ofIdealTop
              (Ideal.span {U.topIso.inv
                (W.presheaf.map (homOfLE hUV).op (s (Fin.castLE rle (e a))))})) ∧
        (∀ a : Fin m, v w ∉ Set.range (c a ≫ i) →
          (c a ≫ i).ker.comap (U.ι ≫ v) = ⊤) ∧
        (∀ q : Finset {a : Fin m // v w ∈ Set.range (c a ≫ i)},
          (⨆ a : q, (c a.1.1 ≫ i).ker).comap (U.ι ≫ v) =
            Scheme.IdealSheafData.ofIdealTop
              (Ideal.span (Set.range fun a : q ↦ U.topIso.inv
                (W.presheaf.map (homOfLE hUV).op (s (Fin.castLE rle (e a.1))))))) ∧
        (∀ q : Finset (Fin m), (∃ a ∈ q, v w ∉ Set.range (c a ≫ i)) →
          (⨆ a : q, (c a.1 ≫ i).ker).comap (U.ι ≫ v) = ⊤)) ∧
    (∀ (a : Fin m) (Z : Set ↥(pullback (c a ≫ i) v)),
      Z ∈ irreducibleComponents ↥(pullback (c a ≫ i) v) →
      ∀ z : ↥(pullback (c a ≫ i) v), IsGenericPoint z Z →
        IsGenericPoint (pullback.fst (c a ≫ i) v z) Set.univ) := by
  sorry

end AlgebraicGeometry
