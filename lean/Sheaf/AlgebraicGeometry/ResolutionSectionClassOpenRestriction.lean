/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U3
-/
module

public import Sheaf.AlgebraicGeometry.FlatBaseChangeMapSectionsDefs

/-! # Open restriction of the normalized resolution class

Source: Stacks Project, Tags 01E4 and 01FB.
-/

@[expose] public section
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits Opposite
noncomputable section
namespace AlgebraicGeometry.Scheme.Modules
attribute [local instance] enoughInjectives

/-- Restrict derived module sections between two opens of the same scheme.
The coefficient identification is restriction composition, with the inclusion equation.
Source: Stacks Project, Tag 01FB.
(blueprint: new-resolution-section-class-open-restriction) -/
def cohomologyOpenRestriction {Y : Scheme.{u}} (G : Y.Modules)
    (U L : Y.Opens) (e : L ≤ U) (p : ℕ) :
    (forget₂ _ AddCommGrpCat.{u}).obj
      ((RingedSpace.moduleCohomology U.toScheme.toRingedSpace p).obj
        ((restrictFunctor U.ι).obj G)) ⟶
    (forget₂ _ AddCommGrpCat.{u}).obj
      ((RingedSpace.moduleCohomology L.toScheme.toRingedSpace p).obj
        ((restrictFunctor L.ι).obj G)) :=
  let j := Y.homOfLE e
  let c := (restrictFunctorComp j U.ι).symm.app G ≪≫
    (restrictFunctorCongr (Y.homOfLE_ι e)).app G
  moduleCohomologyFMap j
    ((restrictAdjunction j).unit.app ((restrictFunctor U.ι).obj G) ≫
      (pushforward j).map c.hom) p

/-- The normalized resolution class commutes with restriction between arbitrary opens.
No affineness, quasi-coherence, base change or scalar extension is assumed.
Source: Stacks Project, Tag 01E4, Lemma 20.7.3; Tag 01FB, Remark 20.14.2.
(blueprint: new-resolution-section-class-open-restriction)

Proof: Expand both resolutionSectionClass maps. The augmentations of R and R'
identify them with the same derived section comparison for the fixed resolution I.
Restriction on cohomology is computed by restricting I termwise and applying the
section-complex comparison (restrictedResolution_cohomology). Compose restrictions
along the two open inclusions; moduleCohomologyFMap composition and target naturality
identify that map with cohomologyOpenRestriction. The component equations of R and
R' identify the resulting section-complex map with I(U) to I(f inverse W).
The equation e transports I(U) to I(f inverse V). Naturality of exact evaluation's
homology comparison moves this restriction past the two homology isomorphisms.
Naturality of sectionCohomologyTheta then gives restriction on the homology sheaf.
Finally the naturality square of I.isoRightDerivedObj inverse moves the restriction
past the final comparison, yielding the displayed equality. Equality proofs have
no effect because the category of opens is thin. This works for empty or equal
opens, zero coefficients and p = 0 with the same section complexes. -/
theorem resolutionSectionClass_open_restriction
    {X S : Scheme.{u}} (f : X ⟶ S) (F : X.Modules) (I : InjectiveResolution F)
    (p : ℕ) (V W : S.Opens) (eWV : W ≤ V)
    (U : X.Opens) (e : U = f ⁻¹ᵁ V) (R : RestrictedResolutionSections I U)
    (R' : RestrictedResolutionSections I (f ⁻¹ᵁ W)) :
    let eU : f ⁻¹ᵁ W ≤ U := by rw [e]; exact f.preimage_mono eWV
    let K := ((pushforward f).mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex
    let Q := ((pushforward f).rightDerived p).obj F
    let c := resolutionSectionClass R.resolution K V
      (R.sections ≪≫ eqToIso (congrArg (fun T ↦
        ((RingedSpace.openModuleSections X.toRingedSpace T).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj I.cocomplex) e)) p ≫
      Hom.app (I.isoRightDerivedObj (pushforward f) p).inv V
    let c' := resolutionSectionClass R'.resolution K W R'.sections p ≫
      Hom.app (I.isoRightDerivedObj (pushforward f) p).inv W
    ∀ y : (RingedSpace.moduleCohomology U.toScheme.toRingedSpace p).obj
        ((restrictFunctor U.ι).obj F),
      c' (cohomologyOpenRestriction F U (f ⁻¹ᵁ W) eU p y) =
        Q.presheaf.map (homOfLE eWV).op (c y) := by sorry

end AlgebraicGeometry.Scheme.Modules
