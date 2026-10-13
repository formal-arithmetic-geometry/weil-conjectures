/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N2
-/
module

public import Sheaf.AlgebraicGeometry.FlatBaseChangeMapSectionsDefs

/-! # Flat-unit compatibility on raw section cohomology

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

/-- Flat pullback's unit carries raw section classes to the mate of the inverse homology
comparison. This is the unit case, before composition with a map into a target complex.
Source: Stacks Project, Cohomology, Tags 02N7 and 01E4.
(blueprint: lem-weil-pbc-flat-unit-raw-sections).

Proof: Represent a section-complex homology class on V by a cycle. Apply the degreewise
adjunction unit; naturality for the differential makes its image a cycle on g inverse V.
Naturality for the cycle inclusion identifies this with the unit on the cycle sheaf.
Flatness makes tensor pullback exact, so its cycle and homology comparison isomorphisms
identify the image cycle and quotient with those of the pulled-back complex. Naturality
of the unit for the homology quotient gives the inverse comparison's adjoint on the class.
The sheafification comparison theta sends a cycle to its class in the homology sheaf:
this follows from the sheafification counit and its exact homology comparison.
Apply exact evaluation to this cycle identity. The two composites agree after the
surjective cycle-to-homology map of the section complex, so they agree as morphisms.
The same argument applies in degree zero and on the empty open; no invertibility of theta
and no acyclicity of sections is used. -/
theorem flatUnit_raw_sections {S S' : Scheme.{uBC}} (g : S' ⟶ S) [Flat g]
    (K : CochainComplex S.Modules ℕ) (p : ℕ) (V : S.Opens) :
    let A := (tensorPullback g).mapHomologicalComplex (ComplexShape.up ℕ)
    let U := SheafOfModules.forget S.ringCatSheaf
    let U' := SheafOfModules.forget S'.ringCatSheaf
    let E := PresheafOfModules.toPresheaf S.ringCatSheaf.obj ⋙
      (CategoryTheory.evaluation S.Opensᵒᵖ AddCommGrpCat.{uBC}).obj (op V)
    let E' := PresheafOfModules.toPresheaf S'.ringCatSheaf.obj ⋙
      (CategoryTheory.evaluation S'.Opensᵒᵖ AddCommGrpCat.{uBC}).obj (op (g ⁻¹ᵁ V))
    let adj := Classical.choose (exists_tensorPullbackAdjunction g)
    ((((U.mapHomologicalComplex (ComplexShape.up ℕ)).obj K).sc p).mapHomologyIso E).hom ≫
        E.map (sectionCohomologyTheta K p) ≫
        Hom.app (adj.homEquiv _ _ ((K.sc p).mapHomologyIso (tensorPullback g)).inv) V =
      HomologicalComplex.homologyMap
        (((RingedSpace.openModuleSections S.toRingedSpace V).mapHomologicalComplex
          (ComplexShape.up ℕ)).map ((adj.mapHomologicalComplex
            (ComplexShape.up ℕ)).unit.app K)) p ≫
        ((((U'.mapHomologicalComplex (ComplexShape.up ℕ)).obj (A.obj K)).sc p)
          |>.mapHomologyIso E').hom ≫ E'.map (sectionCohomologyTheta (A.obj K) p) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
