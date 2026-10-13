module
public import Sheaf.AlgebraicGeometry.Morphisms.CompletedMatchingRingMap
public import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.Ideal.Quotient.Operations
@[expose] public section
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.CompletionGluingData

/-- The completed comparison is onto after passage to the residue quotient.
Source: Stacks Project, Tags 0BLH and 05ER.
(blueprint: lem-sbc-completed-matching-ring-map-residue-quotient-surjective)

The formal gluing comparison identifies the scalar extension of matching sections
with the completed finite algebra. Reducing this comparison modulo the image of the
maximal ideal gives the asserted surjectivity. This is the residue-quotient part of
the canonical H0 comparison; the remaining algebraic extraction of a lift is proved
in `residue_lift_of_quotient_surjective`.
-/
theorem completedRingMap_residue_quotient_surjective
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    {U : (Spec (.of A)).Opens}
    (hU : ∀ x : Spec (.of A), x ∈ U ↔ x ≠ IsLocalRing.closedPoint A)
    {Y : Scheme.{u}} {q : Y ⟶ U.toScheme} [IsFinite q]
    {E : Scheme.{u}} {s : E ⟶ Spec
      (.of (AdicCompletion (IsLocalRing.maximalIdeal A) A))} [IsFinite s]
    (D : CompletionGluingData A U q E s) :
    let P : CommRingCat := pushout D.baseMap (CommRingCat.ofHom
      (algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A)))
    Function.Surjective (fun a : P =>
      Ideal.Quotient.mk
        ((IsLocalRing.maximalIdeal (AdicCompletion (IsLocalRing.maximalIdeal A) A)).map
          (((ΓSpecIso (.of (AdicCompletion (IsLocalRing.maximalIdeal A) A))).inv ≫
            s.appTop).hom)) (D.completedRingMap a)) := by sorry

end AlgebraicGeometry.Scheme.CompletionGluingData
