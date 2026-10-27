/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q34
-/
module

public import Sheaf.AlgebraicGeometry.AdicFormalGeometry
public import Mathlib.AlgebraicGeometry.Noetherian
public import Sheaf.AlgebraicGeometry.CoherentFiniteType
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
import WeilConjectures.RingTheory.AdicCompletionNoetherian
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.Noetherian.Basic
import WeilConjectures.RingTheory.FiniteTypeGRing
import Sheaf.AlgebraicGeometry.GRingAffineCover
import Sheaf.AlgebraicGeometry.JTwoAffineCover
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian

/-! # Quasi-excellence on all formal affine opens of a completion

Source: Temkin, Non-embedded desingularization, sections 2.4.1 and 2.4.3,
Theorem 2.1.8; Illusie--Laszlo--Orgogozo, Travaux de Gabber, Expose I,
Theoreme 9.2 (blueprint: lem-per-quasi-excellent-formal-affines).

The formal affine opens below are arbitrary open ringed subspaces isomorphic to complete
Noetherian formal spectra. They need not lie in an original completed affine chart.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry

/-- Completing a Noetherian scheme with quasi-excellent affine coordinate rings along a
coherent ideal gives a Noetherian adic formal scheme, and every formal affine open has
Noetherian quasi-excellent coordinate ring.
Source: Temkin, sections 2.4.1 and 2.4.3, Theorem 2.1.8;
Illusie--Laszlo--Orgogozo, Expose I, Theoreme 9.2
(blueprint: lem-per-quasi-excellent-formal-affines).

Proof plan:
1. Choose a finite Noetherian affine cover of X. Its ideals are finitely generated.
   Completion is Noetherian by lem-weil-pbc-adic-completion-noetherian, and complete
   for the extended ideal with the original quotient by lem-weil-pbc-adic-completion-mod-ideal.
   Glue these formal spectra using lem-per-formal-completion-reduction-dictionary.
   This finite cover proves Noetherian adicness and identifies the closed fibre Z = V(I).
2. On each chart the ring A/I is Noetherian by lem-weil-pbc-surjective-image-noetherian
   and a G-ring by lem-weil-pbc-finite-type-over-g-ring. Every finite type A/I-algebra
   is finite type over A, so the J-2 clause of def-exc-excellent-ring descends to A/I.
3. The quotient charts cover Z. Use pqf-def-locnoeth to obtain local Noetherianity,
   then lem-trf-g-ring-affine-cover and lem-trf-j2-affine-cover to show that every
   affine open of Z has quasi-excellent coordinate ring. Intersections need not be affine.
4. For an arbitrary formal affine U = Spf R, the reduction dictionary supplies an ideal
   J defining the same topology and identifies Spec(R/J) with the open subscheme of Z
   on U. Step 3 makes R/J quasi-excellent. The ring R is Noetherian and J-complete,
   so lem-per-gabber-adic-quasi-excellence makes R quasi-excellent. This applies also
   to opens lying in none of the original charts. No regular morphism is assumed. -/
theorem quasiExcellent_formalCompletion
    {X : Scheme.{u}} [IsNoetherian X]
    (_hX : ∀ V : X.affineOpens, IsQuasiExcellent Γ(X, V))
    (I : X.IdealSheafData)
    (_hI : RingedSpace.IsCoherent X.toRingedSpace I.toModules) :
    IsNoetherianAdicFormalScheme (adicFormalCompletion I) ∧
      ∀ (U : Opens (adicFormalCompletion I)) (R : CommRingCat.{u}) (K : Ideal R),
        IsNoetherianRing R → IsAdicComplete K R →
        Nonempty ((adicFormalCompletion I).restrict U.isOpenEmbedding ≅ adicFormalSpec R K) →
        IsNoetherianRing R ∧ IsQuasiExcellent R := by
  sorry

/-- The completion of a Noetherian quasi-excellent ring along any ideal is quasi-excellent,
and so are the coordinate rings of all formal affine opens of its formal spectrum.
Source: Temkin, Theorem 2.1.8 and section 2.4.3;
Illusie--Laszlo--Orgogozo, Expose I, Theoreme 9.2
(blueprint: lem-per-quasi-excellent-formal-affines).

Proof plan (the affine specialization, Step 5 of the node):
1. Put X = Spec A and take the quasi-coherent ideal sheaf associated with I. The
   one-chart cover makes X Noetherian. The ideal is finitely generated, so its
   associated sheaf is finite type; pqf-lem-coherent-ft-locnoeth makes it coherent.
2. Apply lem-trf-g-ring-affine-cover and lem-trf-j2-affine-cover to the one-chart
   cover to verify quasi-excellence on every affine open of X.
3. Apply quasiExcellent_formalCompletion. The reduction dictionary identifies this
   formal completion with Spf of AdicCompletion I A for the extended ideal.
4. The completed ring is Noetherian and complete for that ideal by
   lem-weil-pbc-adic-completion-noetherian and lem-weil-pbc-adic-completion-mod-ideal.
   Its entire formal spectrum is therefore a formal affine open. This gives the first
   conclusion; all the other formal affine opens give the second. If I = A, the
   completed ring is zero and its formal spectrum empty; I = 0 recovers A, and nilpotent
   ideals give stationary quotient towers. No characteristic restriction is used. -/
theorem quasiExcellent_adicCompletion_formalAffines
    (A : Type u) [CommRing A] [IsNoetherianRing A]
    (_hA : IsQuasiExcellent A) (I : Ideal A) :
    IsQuasiExcellent (AdicCompletion I A) ∧
      ∀ (U : Opens (adicFormalSpec (CommRingCat.of (AdicCompletion I A))
          (I.map (algebraMap A (AdicCompletion I A)))))
        (R : CommRingCat.{u}) (K : Ideal R),
        IsNoetherianRing R → IsAdicComplete K R →
        Nonempty ((adicFormalSpec (CommRingCat.of (AdicCompletion I A))
          (I.map (algebraMap A (AdicCompletion I A)))).restrict U.isOpenEmbedding ≅
            adicFormalSpec R K) →
        IsQuasiExcellent R := by
  sorry

end AlgebraicGeometry
