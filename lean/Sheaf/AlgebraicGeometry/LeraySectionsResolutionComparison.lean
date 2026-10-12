/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G1
-/
module

public import Sheaf.Paper.PQFCohomology
import Sheaf.AlgebraicGeometry.RingedSpaceDerivedDirectImage

/-! # Resolution comparison for sections of a direct image

Source: Stacks Project, Cohomology, Tags 01F4 (2), 01F2, and 01EX
(blueprint: lem-pc-leray-sections-resolution-comparison).
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
namespace AlgebraicGeometry

/-- Compare the derived composite with sections upstairs, retaining its cycle formula.
No edge map or acyclicity witness occurs in this statement.

Source: Stacks Project, Cohomology, Tags 01F4 (2), 01F2, and 01EX.
(blueprint: lem-pc-leray-sections-resolution-comparison)

Proof: Restriction along Opens.map_top identifies sections of the direct image on Y
with sections on X, naturally in the module sheaf. After forgetting scalars this is
an isomorphism, with inverse restriction along the inverse equality. Apply it in each
degree of a complex. Restriction commutes with differentials and comparison cochain
maps. Taking homology gives natural isomorphisms on the chosen injective resolutions;
conjugate by isoRightDerivedObj to obtain e. Naturality follows from the comparison
maps extending coefficient morphisms and isoRightDerivedObj naturality. For any other
injective resolution the comparison extending the identity shows the same formula.
Sections preserves the kernel defining the cycle sheaf, so each transported global
cycle has a unique lift z. Any c with the displayed inclusion equation sends z to the
transported global cycle: the inclusion into the term is monic. The homology map of
the termwise restriction sends the original cycle class to the class of c(z).
Conjugating by the resolution isomorphisms proves the last equation. In degree zero
and for zero complexes the same kernel argument applies; empty schemes introduce no
exception. The isomorphism e is determined by this formula since the cycle quotient
is epic, so the statement determines the comparison rather than an arbitrary witness.
-/
theorem leray_sections_resolution_comparison {X Y : Scheme.{u}} (f : X ⟶ Y) :
    let D := RingedSpace.moduleDirectImage f.toLRSHom.toShHom
    let G := RingedSpace.globalSectionsFunctor Y.toRingedSpace
    ∃ e : ∀ q : ℕ,
      (RingedSpace.moduleCohomology X.toRingedSpace q ⋙ forget₂ _ AddCommGrpCat) ≅
        ((D ⋙ G).rightDerived q ⋙ forget₂ _ AddCommGrpCat),
    ∀ (q : ℕ) (F : SheafOfModules.{u} (moduleRings X.toRingedSpace))
      (I : InjectiveResolution F)
      (s : (RingedSpace.globalSectionsComplex I).cycles q),
      let K := (D.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex
      let T := ((D ⋙ G).mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex
      ∃ z : G.obj (K.cycles q),
        (I.cocomplex.X q).val.presheaf.map
            (eqToHom (congrArg op (Opens.map_top f.base).symm))
            ((RingedSpace.globalSectionsComplex I).iCycles q s) = G.map (K.iCycles q) z ∧
        ∀ (c : G.obj (K.cycles q) ⟶ T.cycles q),
          c ≫ T.iCycles q = G.map (K.iCycles q) →
          (e q).hom.app F
              ((I.isoRightDerivedObj (RingedSpace.globalSectionsFunctor X.toRingedSpace) q).inv
                ((RingedSpace.globalSectionsComplex I).homologyπ q s)) =
            (I.isoRightDerivedObj (D ⋙ G) q).inv (T.homologyπ q (c z)) := by sorry

end AlgebraicGeometry
