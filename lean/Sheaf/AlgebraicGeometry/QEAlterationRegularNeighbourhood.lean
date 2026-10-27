/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q83
-/
module

public import Sheaf.RingTheory.ExcellentRing
public import Sheaf.AlgebraicGeometry.IsRegularScheme
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.RingTheory.FinitePresentation
import Mathlib.Topology.Constructible
import Mathlib.Topology.Spectral.Basic
import WeilConjectures.Topology.ProconstructibleClosureSpecialization

/-!
# Alteration neighbourhoods regular above a prescribed closed fibre

Source: Kurano--Shimomoto, Ideal-adic completion of quasi-excellent rings (after Gabber),
Lemma 4.4 and Definition 3.2, printed pp. 3, 5--6
(blueprint: lem-per-qe-alteration-regular-neighbourhood).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- Around a prime with excellent localization there is an alteration covering whose charts
have regular ambient local rings above a prescribed quasi-excellent closed fibre.

Dominance is dense image. For a dominant morphism of integral schemes the image of the
source generic point is the target generic point. Thus finiteness of the canonical stalk map
at that point is precisely finiteness of the induced extension of function fields. The
closed fibre is specified by the extension of `J` to `Localization.Away b`.

Source: Kurano--Shimomoto, Ideal-adic completion of quasi-excellent rings (after Gabber),
Lemma 4.4 and Definition 3.2, printed pp. 3, 5--6
(blueprint: lem-per-qe-alteration-regular-neighbourhood).

Proof:
1. Excellence of `Localization.AtPrime q` implies quasi-excellence
   [def-exc-excellent-ring]. Apply [lem-per-qe-weak-uniformization-cover] to its spectrum,
   obtaining regular integral charts and an integral proper-surjective generically finite
   witness, with an indexed open cover and compatible maps.
2. Spread the entire diagram to `Spec B[1/a]` for some `a` outside `q`, using
   [lem-per-local-alteration-diagram-spreading]. Retain integrality, Noetherianity,
   finite type, dominance, generic finiteness and the covering witness.
3. A point of a spread chart lying over a prime contained in `q` survives localization
   to `B_q`. On an affine chart with coordinate ring `C` and prime `p`, every element
   of `B` outside `q` is already a unit in `C_p`. Localizing first by those elements
   and then at `p` therefore leaves the ambient local ring unchanged. It is regular
   because the corresponding chart over `B_q` is regular.
4. The quotient `B/J` is J-2 by [def-exc-excellent-ring]. Apply
   [lem-per-j2-closed-fibre-regular-locus] to each chart over `Spec B`: its nonregular
   locus above `V(J)` is closed. This is constructible
   [def-weil-constructible-subset]. Finite type over a Noetherian ring is finite
   presentation [lem-weil-pbc-finite-type-noetherian-finite-presentation], so Chevalley
   [lem-weil-pbc-chevalley-constructible-image] makes its image constructible.
5. The affine target is spectral [lem-weil-pbc-qcqs-scheme-spectral]. If `q` belonged
   to the closure of such an image, [lem-weil-pbc-spectral-proconstructible-closure-specialization]
   would give a point of the image generalizing `q`. A nonregular point over it would
   contradict step 3. Hence `q` avoids all these finitely many image closures.
6. Choose a basic neighbourhood `D(b)` of `q` avoiding their union and contained in
   `D(a)`; one may take `b = a*c` after choosing `D(c)` inside the desired open.
   Restrict the whole diagram, using the permanence clause of
   [lem-per-local-alteration-diagram-spreading]. Open restriction preserves local
   rings, and the bad loci are now empty, proving the required regularity.
-/
theorem exists_qe_alteration_regular_neighbourhood
    (B : Type u) [CommRing B] [IsNoetherianRing B] [IsDomain B]
    (q : Ideal B) [q.IsPrime] (J : Ideal B)
    (hq : IsExcellent (Localization.AtPrime q)) (hJ : IsQuasiExcellent (B ⧸ J)) :
    ∃ b : B, b ∉ q ∧
      ∃ (n : ℕ) (X : Fin n → Scheme.{u})
        (φ : ∀ i : Fin n, X i ⟶ Spec (.of (Localization.Away b))),
        (∀ i : Fin n, ∃ (_ : IsIntegral (X i)),
          IsNoetherian (X i) ∧ IsDominant (φ i) ∧
          RingHom.Finite ((φ i).stalkMap (genericPoint (X i))).hom ∧
          LocallyOfFiniteType (φ i) ∧ QuasiCompact (φ i) ∧
          ∀ x : X i,
            Ideal.map (algebraMap B (Localization.Away b)) J ≤ (φ i x).asIdeal →
              IsRegularLocalRing ((X i).presheaf.stalk x)) ∧
        ∃ (V : Scheme.{u}) (_ : IsIntegral V)
          (p : V ⟶ Spec (.of (Localization.Away b))),
          IsNoetherian V ∧ IsProper p ∧ Surjective p ∧
          RingHom.Finite (p.stalkMap (genericPoint V)).hom ∧
          ∃ (U : Fin n → V.Opens) (g : ∀ i : Fin n, (U i).toScheme ⟶ X i),
            (⨆ i : Fin n, U i) = ⊤ ∧ ∀ i : Fin n, g i ≫ φ i = (U i).ι ≫ p := by
  sorry

end AlgebraicGeometry
