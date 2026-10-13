/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G4
-/
module

public import Sheaf.AlgebraicGeometry.FlatBaseChangeMapSectionsDefs

/-! # The flat pullback unit on raw section cohomology

Source: Stacks Project, Cohomology, Tags 02N7 and 01E4.
-/

@[expose] public section
universe uBC
set_option autoImplicit false
set_option Elab.async true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits Opposite
noncomputable section
namespace AlgebraicGeometry.Scheme.Modules

/-- The homology mate on a fixed pair of resolution complexes acts on raw section classes.
Source: Stacks Project, Cohomology, Tags 02N7 and 01E4.
(blueprint: lem-weil-pbc-flat-pullback-resolution-raw-mate-sections).

Proof: Apply the degreewise adjunction unit to a cycle of the source section complex.
Naturality for the cycle inclusion identifies the resulting section with the unit on
its cycle sheaf. Exactness of flat tensor pullback identifies both the cycle sheaf
and the homology quotient with those of the pulled back complex. Naturality of the
unit for the quotient therefore identifies the resulting raw homology class with
the mate of the inverse exact homology comparison. The cycle formula for the
sheafification comparison theta sends this class to its class in the homology sheaf.
Now compose with the termwise adjoint c of q. Theta is natural for c, as follows
from naturality of the sheafification counit and the exact homology comparison.
The complex adjunction identity eta followed by pushforward of c equals q.
Hence the composite class is precisely H(q) followed by theta on the target.
This proves the displayed raw-complex identity. There are no resolution-section
isomorphisms or derived-image isomorphisms in this statement. -/
theorem flatBaseChangeResolution_rawMate_sections {X S S' : Scheme.{uBC}}
    (f : X ⟶ S) (g : S' ⟶ S) [Flat g] {F : X.Modules}
    (I : InjectiveResolution F)
    (J : InjectiveResolution ((tensorPullback (pullback.snd g f)).obj F))
    (t : I.cocomplex ⟶ ((pushforward (pullback.snd g f)).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj J.cocomplex) (p : ℕ) (V : S.Opens) :
    let K := ((pushforward f).mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex
    let L := ((pushforward (pullback.fst g f)).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj J.cocomplex
    let U := SheafOfModules.forget S.ringCatSheaf
    let U' := SheafOfModules.forget S'.ringCatSheaf
    let E := PresheafOfModules.toPresheaf S.ringCatSheaf.obj ⋙
      (CategoryTheory.evaluation S.Opensᵒᵖ AddCommGrpCat.{uBC}).obj (op V)
    let E' := PresheafOfModules.toPresheaf S'.ringCatSheaf.obj ⋙
      (CategoryTheory.evaluation S'.Opensᵒᵖ AddCommGrpCat.{uBC}).obj (op (g ⁻¹ᵁ V))
    let adj := Classical.choose (exists_tensorPullbackAdjunction g)
    ((((U.mapHomologicalComplex (ComplexShape.up ℕ)).obj K).sc p).mapHomologyIso E).hom ≫
        E.map (sectionCohomologyTheta K p) ≫
        Hom.app (adj.homEquiv _ _
          (((K.sc p).mapHomologyIso (tensorPullback g)).inv ≫
            HomologicalComplex.homologyMap (flatBaseChangeResolutionC f g I J t) p)) V =
      HomologicalComplex.homologyMap
        (((RingedSpace.openModuleSections S.toRingedSpace V).mapHomologicalComplex
          (ComplexShape.up ℕ)).map (flatBaseChangeResolutionQ f g I J t)) p ≫
        ((((U'.mapHomologicalComplex (ComplexShape.up ℕ)).obj L).sc p)
          |>.mapHomologyIso E').hom ≫ E'.map (sectionCohomologyTheta L p) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
