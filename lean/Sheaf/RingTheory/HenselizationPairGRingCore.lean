module

public import Sheaf.RingTheory.GRingMaximalIdealCriterion
public import Sheaf.RingTheory.PairHenselizationNoetherianCompletion

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace RingTheory

/-- The Noetherian and maximal-local regularity part of the G-ring theorem for a
henselization of a pair.  It packages the completion comparison, finite separable
fibres, and geometric-regularity argument of Stacks Project Tag 0AH3; the final
application of the maximal-ideal criterion is kept in the parent theorem.
Source: Stacks Project, More on Algebra, Tag 0AH3, proof paragraphs 1--4
(blueprint: lem-weil-pbc-henselization-pair-g-ring-core).
-/
theorem henselization_pair_noetherian_and_maximal_regular
    (A : Type u) [CommRing A] (I : Ideal A)
    (c : Cocone (ObjectProperty.ι
      (fun C : Under (CommRingCat.of A) ↦
        AlgebraicGeometry.Etale (AlgebraicGeometry.Spec.map C.hom) ∧
          Function.Bijective (Ideal.quotientMap (I.map C.hom.hom) C.hom.hom
            (Ideal.le_comap_map)))))
    (hc : Nonempty (IsColimit c) ∧
      HenselianRing c.pt.right (I.map c.pt.hom.hom) ∧
      Function.Bijective (Ideal.quotientMap (I.map c.pt.hom.hom) c.pt.hom.hom
        (Ideal.le_comap_map)))
    (hA : IsGRing A) :
    IsNoetherianRing c.pt.right ∧
      ∀ (m : Ideal c.pt.right) [m.IsMaximal],
        RingHom.IsRegular
          (algebraMap (Localization.AtPrime m)
            (AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime m))
              (Localization.AtPrime m))) := by
  sorry

end RingTheory
