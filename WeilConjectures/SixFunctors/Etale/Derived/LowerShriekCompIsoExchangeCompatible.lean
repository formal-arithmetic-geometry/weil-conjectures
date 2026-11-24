/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangePaste
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.RelativeMap
public import WeilConjectures.CategoryTheory.Adjunction.ProjectionTensorMap

/-!
# The composition isomorphism of `R_!` and the vertical pasting of `Ex_!`

The composition isomorphism `R(f ≫ g)_! ≅ Rf_! ⋙ Rg_!` built from the chosen compactifications
(`AlgebraicGeometry.Etale.rightDerivedLowerShriekCompIso`) is the inverse of
`AlgebraicGeometry.Etale.unboundedEtaleLowerShriekCompIso`
(`AlgebraicGeometry.Etale.rightDerivedLowerShriekCompIso_eq_symm`). Hence the compactly supported
base change maps of two stacked cartesian squares and of their pasting are compatible with these
composition isomorphisms (`AlgebraicGeometry.Etale.exchangeCompCompatible_of_paste_vert`), also
after transport along equalities `f ≫ g = h`
(`AlgebraicGeometry.Etale.exchangeCompCompatible_of_eq`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

open Scheme

variable {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ]

section Comp

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) [HasCompactification f]
  [HasCompactification g] [HasCompactification (f ≫ g)] [QuasiCompact f] [QuasiCompact (f ≫ g)]

/-- The composition isomorphism `R(f ≫ g)_! ≅ Rf_! ⋙ Rg_!` of
`AlgebraicGeometry.Etale.rightDerivedLowerShriekCompIso` is the inverse of
`AlgebraicGeometry.Etale.unboundedEtaleLowerShriekCompIso`. -/
theorem rightDerivedLowerShriekCompIso_eq_symm :
    rightDerivedLowerShriekCompIso Λ f g = (unboundedEtaleLowerShriekCompIso Λ f g).symm := by
  refine Iso.ext ?_
  dsimp only [rightDerivedLowerShriekCompIso, unboundedEtaleLowerShriekCompIso, Iso.trans,
    Iso.symm]
  simp only [Category.assoc]
  rfl

end Comp

section Paste

variable {X X' Y Y' Z Z' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'} {g : Y ⟶ Z} {g' : Y' ⟶ Z'}
  {vX : X' ⟶ X} {vY : Y' ⟶ Y} {vZ : Z' ⟶ Z}

/-- **Vertical pasting as `ExchangeCompCompatible`**: the compactly supported base change maps
of two stacked cartesian squares and of their pasting are compatible with the composition
isomorphisms `AlgebraicGeometry.Etale.rightDerivedLowerShriekCompIso`
(`AlgebraicGeometry.Etale.rightDerivedLowerShriekBaseChangeMap_paste_vert`). -/
theorem exchangeCompCompatible_of_paste_vert
    [QuasiCompact f] [QuasiCompact (f ≫ g)] [QuasiCompact f'] [QuasiCompact g']
    [QuasiCompact (f' ≫ g')]
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    [HasCompactification f'] [HasCompactification g'] [HasCompactification (f' ≫ g')]
    (sqf : IsPullback vX f' f vY) (sqg : IsPullback vY g' g vZ)
    (sqgf : IsPullback vX (f' ≫ g') (f ≫ g) vZ) :
    Adjunction.ExchangeCompCompatible (rightDerivedLowerShriekBaseChangeMap Λ sqf)
      (rightDerivedLowerShriekBaseChangeMap Λ sqg) (rightDerivedLowerShriekBaseChangeMap Λ sqgf)
      (rightDerivedLowerShriekCompIso Λ f g) (rightDerivedLowerShriekCompIso Λ f' g') where
  comp M := by
    rw [rightDerivedLowerShriekCompIso_eq_symm, rightDerivedLowerShriekCompIso_eq_symm]
    simp only [Iso.symm_hom]
    have h := rightDerivedLowerShriekBaseChangeMap_paste_vert (Λ := Λ) sqf sqg sqgf M
    rw [← cancel_mono ((unboundedEtaleLowerShriekCompIso Λ f' g').hom.app
      ((L((vX)^*[ModuleCat.{u + 1} Λ])).obj M))]
    simp only [Category.assoc, Iso.inv_hom_id_app]
    rw [← h, ← Functor.map_comp_assoc, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id,
      Category.id_comp]
    -- the identity is stated at `R.obj (LvX^* M)`, the map at `(LvX^* ⋙ R).obj M`
    erw [Category.comp_id]

/-- Transport of `ExchangeCompCompatible` along equalities `f ≫ g = h`, `f' ≫ g' = h'`: the
composition isomorphisms become `AlgebraicGeometry.Etale.rightDerivedLowerShriekCompIsoOfEq`. -/
theorem exchangeCompCompatible_of_eq {h : X ⟶ Z} {h' : X' ⟶ Z'}
    (w : f ≫ g = h) (w' : f' ≫ g' = h')
    [HasCompactification f] [HasCompactification g] [HasCompactification h]
    [HasCompactification f'] [HasCompactification g'] [HasCompactification h']
    [QuasiCompact h] [QuasiCompact h'] [QuasiCompact f'] [QuasiCompact g']
    (sqf : IsPullback vX f' f vY) (sqg : IsPullback vY g' g vZ)
    (sqh : IsPullback vX h' h vZ) (sqgf : IsPullback vX (f' ≫ g') (f ≫ g) vZ)
    (H : letI : HasCompactification (f ≫ g) := HasCompactification.of_eq w.symm
      letI : HasCompactification (f' ≫ g') := HasCompactification.of_eq w'.symm
      letI : QuasiCompact (f ≫ g) := by rw [w]; infer_instance
      letI : QuasiCompact (f' ≫ g') := by rw [w']; infer_instance
      Adjunction.ExchangeCompCompatible (rightDerivedLowerShriekBaseChangeMap Λ sqf)
        (rightDerivedLowerShriekBaseChangeMap Λ sqg)
        (rightDerivedLowerShriekBaseChangeMap Λ sqgf)
        (rightDerivedLowerShriekCompIso Λ f g) (rightDerivedLowerShriekCompIso Λ f' g')) :
    Adjunction.ExchangeCompCompatible (rightDerivedLowerShriekBaseChangeMap Λ sqf)
      (rightDerivedLowerShriekBaseChangeMap Λ sqg) (rightDerivedLowerShriekBaseChangeMap Λ sqh)
      (rightDerivedLowerShriekCompIsoOfEq Λ f g h w)
      (rightDerivedLowerShriekCompIsoOfEq Λ f' g' h' w') := by
  subst w w'
  refine ⟨fun M ↦ ?_⟩
  have hM := H.comp M
  simp only [rightDerivedLowerShriekCompIsoOfEq, Iso.trans_hom, eqToIso_refl, Iso.refl_hom,
    Category.id_comp]
  exact hM

end Paste

end AlgebraicGeometry.Etale
