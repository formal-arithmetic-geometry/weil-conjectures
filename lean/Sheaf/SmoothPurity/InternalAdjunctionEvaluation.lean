module

public import WeilConjectures.SixFunctors.Etale.Derived.TensorHom
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import Sheaf.AlgebraicGeometry.EtaleDerivedTensorSymmetry
import Sheaf.Algebra.Homology.RhomGlobalSectionsOfUniverses
import Sheaf.Algebra.Homology.RingedInternalHomShiftOfUniverses
import Sheaf.AlgebraicGeometry.CompactifiableOverField
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint
import Sheaf.AlgebraicGeometry.ProperProjectionFormula
import Sheaf.CategoryTheory.KInjectiveTotalDerived
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekProjection

/-! # Evaluation formula for the canonical internal compact-support adjunction

Source: literature/blueprint/master/blueprint/sec-smooth-purity/sk-prop-sf-cbc/
lem-asd-internal-adjunction-evaluation.md (blueprint: lem-asd-internal-adjunction-evaluation).

## Main statements

* `internalAdjunctionEvaluation` states the tensor--Hom transpose formula for the
  canonical compact-support internal adjunction.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Opposite
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

/-- The tensor--Hom transpose of the canonical compact-support internal adjunction is
obtained by the compact-support projection map, evaluation, and the exceptional counit.
Source: literature/blueprint/master/blueprint/sec-smooth-purity/sk-prop-sf-cbc/
lem-asd-internal-adjunction-evaluation.md (blueprint: lem-asd-internal-adjunction-evaluation).

Proof: compose the ordinary inverse-image adjunction, the tensor--Hom adjunction,
the canonical projection isomorphism, and the exceptional adjunction. Naturality of
these Hom-bijections identifies the resulting representative with the canonical
internal-adjunction isomorphism `derivedHomRightDerivedLowerShriekIsoOfFinite` (the
recorded declaration of prop-asd-internal-adjunction: the conjugate of the projection map
along these adjunctions, invertible by `isIso_projectionMap_of_finite`); evaluating at
`h` gives the displayed composite. The projection map is the canonical one, and the
exceptional last arrow is its adjunction counit. Precomposing both sides with the
canonical symmetry `Q ⊗ Rf_!M ≅ Rf_!M ⊗ Q` renders the node's tensor order; on the
right this is the node's `Π_{f,Q,M}` followed by `Rf_!(p)`, the two inner symmetries of
the reordered projection map cancelling against the reordering of `p`.
-/
theorem internalAdjunctionEvaluation
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X S : Scheme.{u}} (f : X ⟶ S) [HasCompactification f]
    [IsLocallyNoetherian X] [CompactSpace X]
    [IsLocallyNoetherian S] [CompactSpace S]
    (M : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat A)))
    (K Q : DerivedCategory (Sheaf S.smallEtaleTopology (ModuleCat A)))
    (h : Q ⟶
      (R((f)_*[ModuleCat A])).obj
        (((RHom(X)[ModuleCat A]).obj (op M)).obj
          ((R(f)^![ModuleCat A]).obj K))) :
    ((derivedTensorSymmetry (ModuleCat A) S).hom.app Q).app
        ((R(f)_![ModuleCat A]).obj M) ≫
      ((derivedTensorHomAdjunction (ModuleCat A) ((R(f)_![ModuleCat A]).obj M)).homEquiv
        Q K).symm
      (h ≫ (((derivedHomRightDerivedLowerShriekIsoOfFinite A f).app (op M)).app K).hom) =
      ((derivedTensorSymmetry (ModuleCat A) S).hom.app Q).app
        ((R(f)_![ModuleCat A]).obj M) ≫
        ((projectionMap (ModuleCat A) f).app M).app Q ≫
        (R(f)_![ModuleCat A]).map
          (((derivedTensorHomAdjunction (ModuleCat A) M).homEquiv
              (L((f)^*[ModuleCat A]).obj Q)
              ((R(f)^![ModuleCat A]).obj K)).symm
            (((derivedUpperStarLowerStarAdjunction (ModuleCat A) f).homEquiv
                Q (((RHom(X)[ModuleCat A]).obj (op M)).obj
                  ((R(f)^![ModuleCat A]).obj K))).symm h)) ≫
        (rightDerivedUpperShriekAdjunction (ModuleCat A) f).counit.app K := by
  sorry

end AlgebraicGeometry.Etale
