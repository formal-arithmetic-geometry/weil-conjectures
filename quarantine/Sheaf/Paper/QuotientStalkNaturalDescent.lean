/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U3
-/
module

public import Sheaf.Paper.TraceBoundedQuotientStalkRealization

/-!
# Descent of a strict quotient-stalk isomorphism

Source: Stacks Tags 05V1, 06YS, 06YT, and the parent derived roof argument.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

/-- A natural strict tower isomorphism descends across the prescribed quotient-stalk
realization to every morphism in the full integral constructible category.
This lemma asserts only existence and the representative comparison equation;
it assumes no automorphism action and asserts no composition or identity law.

Source: blueprint Euler-product proof, Local powers (b), parent steps 5--7;
Stacks Project, sites-cohomology.tex, Tags 06YS and 06YT
(blueprint: lem-trf-quotient-stalk-natural-descent).

Proof: choose one flat-term K-flat representative for each constructible object.
Conjugate the localized diagonal Roos map of R by the two given realization
isomorphisms. For a chain map the square follows from naturality of the
realizations and R, and functoriality of the Roos construction. Every derived
arrow between the chosen representatives is a roof in the homotopy category.
Resolve the roof apex by a flat-term K-flat complex. It still represents a
constructible object because its derived class is isomorphic to the source.
For the quasi-isomorphism denominator the chain-map square can be inverted,
since the realizations identify its localized Roos maps with an isomorphism.
Compose this inverted square with the numerator square. This proves naturality
for the derived arrow itself. The identity arrow with any second representative
gives independence of the representative and the required equation for every P
and q. Thus the conjugate component maps form the asserted natural isomorphism.
Homotopies are respected: their diagonal cocone homotopy has components
(-product(h),product(h)); the mixed terms cancel by transition naturality. -/
theorem trfQuotientStalkNaturalDescent
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    (T : Scheme.{u}) [∀ x : T, Invertible (l : T.residueField x)]
    (e : ∀ v : Spec (.of D.k) ⟶ T,
      trfQuotientSectionTower l E v ≅ trfQuotientStalkTower l E v)
    (he : ∀ (v : Spec (.of D.k) ⟶ T) (M : sfIntegralConstructibleCategory l E T)
      (P : (integralOperationsGoodComplex l E T).FullSubcategory)
      (q : DerivedCategory.Q.obj P.obj ≅ M.obj),
      IsIso (trfQuotientStalkRealizationArrow l E D v (e v) M.obj P q))
    (hnat : ∀ (v : Spec (.of D.k) ⟶ T)
      (M M' : DerivedCategory (integralTowerModules l E T))
      (_hM : sfIntegralConstructible l E T M) (_hM' : sfIntegralConstructible l E T M')
      (P P' : (integralOperationsGoodComplex l E T).FullSubcategory)
      (q : DerivedCategory.Q.obj P.obj ≅ M) (q' : DerivedCategory.Q.obj P'.obj ≅ M')
      (w : P.obj ⟶ P'.obj) (h : M ⟶ M'),
      DerivedCategory.Q.map w ≫ q'.hom = q.hom ≫ h →
      (trfCompletedPointFibre l E D v).map h ≫
          trfQuotientStalkRealizationArrow l E D v (e v) M' P' q' =
        trfQuotientStalkRealizationArrow l E D v (e v) M P q ≫
          (trfIntegralModuleQ l E).map
            (integralOperationsRoosMap ((trfQuotientStalkTower l E v).map w)))
    (v w : Spec (.of D.k) ⟶ T)
    (R : trfQuotientStalkTower l E v ≅ trfQuotientStalkTower l E w) :
    ∃ r : (sfIntegralConstructible l E T).ι ⋙ trfCompletedPointFibre l E D v ≅
        (sfIntegralConstructible l E T).ι ⋙ trfCompletedPointFibre l E D w,
      ∀ (M : sfIntegralConstructibleCategory l E T)
        (P : (integralOperationsGoodComplex l E T).FullSubcategory)
        (q : DerivedCategory.Q.obj P.obj ≅ M.obj),
        r.hom.app M ≫ trfQuotientStalkRealizationArrow l E D w (e w) M.obj P q =
          trfQuotientStalkRealizationArrow l E D v (e v) M.obj P q ≫
            (trfIntegralModuleQ l E).map
              (integralOperationsRoosMap (R.hom.app P.obj)) := by sorry

end WeilConjectures
