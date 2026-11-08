/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Submission.WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriekIndependence
public import Submission.WeilConjectures.WeilSheaf.CondensedModelBaseChange
public import Submission.WeilConjectures.WeilSheaf.SmoothPurityReflectedSquareComponents
public import Submission.WeilConjectures.TraceFormula.Specialization.NearbyDualityGenericBaseSliceInputs

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-! # Compact-support base change between different fields

Restrict the ambient weakly étale compactification exchange through the fully faithful
bounded constructible inclusions. The resulting square uses the actual chosen compactifications.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k₁ k₂ : Type u} [Field k₁] [Field k₂]
  [Fact (ringChar k₁).Prime] [Fact (ringChar k₁ ≠ ℓ)]
  [Fact (ringChar k₂).Prime] [Fact (ringChar k₂ ≠ ℓ)]
  {X Y : Over (Spec (.of k₁))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  {X' Y' : Over (Spec (.of k₂))}
  [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom] [IsSeparated X'.hom]
  [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom]
  (f : X ⟶ Y) (f' : X' ⟶ Y')
  {πX : X'.left ⟶ X.left} {πY : Y'.left ⟶ Y.left}



section Compactification

variable (c : Compactification f.left) (c' : Compactification f'.left)
  {πZ : c'.Z ⟶ c.Z} (hi : IsPullback c'.i πX πZ c.i)
  (hg : IsPullback πZ c'.g c.g πY) [WeaklyEtale πZ] [WeaklyEtale πY]

/-- The ambient compactification exchange in left-derived coordinates. -/
noncomputable def purityFieldCompactificationAmbientExchange :
    Rf_!(c)⟦Profinite.padicAlgClRingObj ℓ⟧ ⋙ L((πY)^*⟦Profinite.padicAlgClRingObj ℓ⟧) ≅
      L((πX)^*⟦Profinite.padicAlgClRingObj ℓ⟧) ⋙ Rf_!(c')⟦Profinite.padicAlgClRingObj ℓ⟧ := by
  have : WeaklyEtale πX := MorphismProperty.of_isPullback hi ‹WeaklyEtale πZ›
  exact Functor.isoWhiskerLeft _ (leftDerivedUpperStarIsoMapDerivedCategory _ πY) ≪≫
    rightDerivedLowerShriekOfCompactificationBaseChangeIso _ c c' hi hg ≪≫
    Functor.isoWhiskerRight (leftDerivedUpperStarIsoMapDerivedCategory _ πX).symm _

/-- Restriction of compactification base change to the bounded constructible categories. -/
noncomputable def purityFieldCompactificationExchange :
    boundedConstructibleLowerShriekOfCompactification ℓ c ⋙
        boundedConstructibleUpperStarOfMap ℓ πY ≅
      boundedConstructibleUpperStarOfMap ℓ πX ⋙
        boundedConstructibleLowerShriekOfCompactification ℓ c' :=
  ObjectProperty.preimageIso_liftSquareWithComparisons
    (boundedConstructibleLowerShriekOfCompactificationCompatibility ℓ c)
    (boundedConstructibleLowerShriekOfCompactificationCompatibility ℓ c')
    (fun K ↦ boundedConstructible_leftDerivedUpperStar_obj_of_scheme _ πX K.obj K.property)
    (fun K ↦ boundedConstructible_leftDerivedUpperStar_obj_of_scheme _ πY K.obj K.property)
    (purityFieldCompactificationAmbientExchange ℓ f f' c c' hi hg)

/-- The same cross-field exchange for the lower-shriek functors chosen by Nagata. -/
noncomputable def purityFieldLowerShriekExchange :
    boundedConstructibleLowerShriek ℓ f ⋙ boundedConstructibleUpperStarOfMap ℓ πY ≅
      boundedConstructibleUpperStarOfMap ℓ πX ⋙ boundedConstructibleLowerShriek ℓ f' :=
  Functor.isoWhiskerRight
      (boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl ℓ
        (compactificationOverField f) c) _ ≪≫
    purityFieldCompactificationExchange ℓ f f' c c' hi hg ≪≫
    Functor.isoWhiskerLeft _
      (boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl ℓ
        c' (compactificationOverField f'))

end Compactification

end AlgebraicGeometry.ProEtale.CondensedRing
