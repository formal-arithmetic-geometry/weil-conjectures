/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
import WeilConjectures.AlgebraicGeometry.ReductionUniversalHomeomorphism

/-!
# Open direct image and reduction

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/
sk-prop-a1-kummer/thm-fin-open-degree-zero.proof.md, Proof, first paragraph,
reduction comparison before Noetherian induction (blueprint: lem-fin-reduction-open-direct-image)
-/

@[expose] public section

universe u

open CategoryTheory
open AlgebraicGeometry
open AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Etale

/-- For an open immersion, direct image of constant-coefficient étale module sheaves
is unchanged after replacing the ambient and open schemes by their reductions.

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/
sk-prop-a1-kummer/thm-fin-open-degree-zero.proof.md, Proof, first paragraph,
reduction comparison before Noetherian induction (blueprint: lem-fin-reduction-open-direct-image).

Proof: the reduction square commutes because the nilradical restricts to an open
subscheme. The reduction of `U` is a universal homeomorphism, so its étale inverse
and direct images are quasi-inverse and the unit is a module-linear isomorphism.
Compose its direct image along `j` with the canonical composition isomorphisms for
`lowerStar`; this gives the displayed natural isomorphism, and naturality follows
from naturality of the unit and of those composition isomorphisms.
-/
theorem finReductionOpenDirectImage (Λ : Type (u + 1)) [CommRing Λ]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    Nonempty
      (lowerStar (ModuleCat.{u + 1} Λ) j ≅
        upperStar (ModuleCat.{u + 1} Λ) (U.nilradical.subschemeι) ⋙
          lowerStar (ModuleCat.{u + 1} Λ) ((U.nilradical.subschemeι ≫ j).liftNilradical) ⋙
            lowerStar (ModuleCat.{u + 1} Λ) (X.nilradical.subschemeι)) := by
  have : Surjective U.nilradical.subschemeι :=
    (reduction_isReduced_isClosedImmersion_isSurjective_isUniversalHomeomorphism U).2.2.1
  have : (upperStar (ModuleCat.{u + 1} Λ) U.nilradical.subschemeι).IsEquivalence :=
    isEquivalence_upperStar _ _
  let e := asIso (upperStarLowerStarAdjunction
    (ModuleCat.{u + 1} Λ) U.nilradical.subschemeι).unit
  refine ⟨(Functor.leftUnitor _).symm ≪≫ Functor.isoWhiskerRight e _ ≪≫
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ ?_⟩
  exact lowerStarComp (ModuleCat.{u + 1} Λ) U.nilradical.subschemeι j ≪≫
    (lowerStarComp (ModuleCat.{u + 1} Λ)
      ((U.nilradical.subschemeι ≫ j).liftNilradical) X.nilradical.subschemeι
      (U.nilradical.subschemeι ≫ j) (Hom.liftNilradical_subschemeι _).symm).symm

end AlgebraicGeometry.Etale
