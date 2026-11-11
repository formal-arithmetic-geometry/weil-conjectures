/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangePaste
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.RelativeMap
public import WeilConjectures.CategoryTheory.Adjunction.ProjectionTensorMap
import all WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedEtaleCompactSupportComparisonsSupplement

/-!
# The composition isomorphism of `R_!` and the vertical pasting of `Ex_!`

The composition isomorphism `R(f ≫ g)_! ≅ Rf_! ⋙ Rg_!` built from the chosen compactifications
(`AlgebraicGeometry.Etale.rightDerivedLowerShriekCompIso`) is the inverse of
`AlgebraicGeometry.Etale.unboundedEtaleLowerShriekCompIso`, without noetherian hypotheses
(`AlgebraicGeometry.Etale.rightDerivedLowerShriekCompIso_eq_unboundedEtaleLowerShriekCompIso_symm`).
Hence the compactly supported base change maps of two stacked cartesian squares and of their
pasting are compatible with these composition isomorphisms
(`AlgebraicGeometry.Etale.exchangeCompCompatible_rightDerivedLowerShriekCompIso`).

The identity and tower laws of the comparisons of compactifications hold for any schemes: they
are those of the private compact-support formalism of
`WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedEtaleCompactSupportComparisonsSupplement`,
whose public statements carry unused noetherian hypotheses.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

open Scheme

variable {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ]

attribute [local instance] unbounded_has_base_change unbounded_has_proper_exchange

/-- The comparison of a compactification with itself is the identity. -/
private lemma rightDerivedLowerShriekOfCompactificationIso_self {X Y : Scheme.{u}} {f : X ⟶ Y}
    [QuasiCompact f] (c : Compactification f) :
    rightDerivedLowerShriekOfCompactificationIso Λ c c = Iso.refl _ := by
  rw [← unbounded_shriek_iso]
  exact (unboundedFormalism Λ).shriekIso_refl c

/-- The tower description of `AlgebraicGeometry.Etale.unboundedEtaleLowerShriekCompIso`. -/
private lemma unboundedEtaleLowerShriekCompIso_tower' {X Y Z : Scheme.{u}} (f : X ⟶ Y)
    (g : Y ⟶ Z) [QuasiCompact f] [QuasiCompact g] [HasCompactification f] [HasCompactification g]
    [HasCompactification (f ≫ g)] [QuasiCompact (f ≫ g)] (d : Compactification g)
    (e : Compactification (f ≫ d.i)) :
    (unboundedEtaleLowerShriekCompIso Λ f g).hom =
      NatTrans.hcomp (rightDerivedLowerShriekIso Λ e.restrict).inv
        (rightDerivedLowerShriekIso Λ d).inv ≫
      (rightDerivedLowerShriekOfCompactificationCompIso Λ d e).hom ≫
      (rightDerivedLowerShriekIso Λ (d.comp e)).hom := by
  let T := Compactification.Triangle.ofRestrict d e
  have h := (unboundedFormalism Λ).lowerShriekCompIso_hom_eq T
  rw [← (unboundedFormalism Λ).shriekIso_symm
    T.cf (HasCompactification.compactification f),
    ← (unboundedFormalism Λ).shriekIso_symm
      T.cg (HasCompactification.compactification g)] at h
  rw [unbounded_chosen_comp] at h
  dsimp only [T] at h
  rw [unbounded_comp_iso] at h
  simp only [unbounded_shriek_iso, Iso.symm_hom, Compactification.Triangle.ofRestrict] at h
  convert! h using 1

/-- The composition isomorphism `R(f ≫ g)_! ≅ Rf_! ⋙ Rg_!` of
`AlgebraicGeometry.Etale.rightDerivedLowerShriekCompIso` is the inverse of
`AlgebraicGeometry.Etale.unboundedEtaleLowerShriekCompIso`. -/
theorem rightDerivedLowerShriekCompIso_eq_unboundedEtaleLowerShriekCompIso_symm {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) [QuasiCompact f] [QuasiCompact g] [HasCompactification f]
    [HasCompactification g]
    [HasCompactification (f ≫ g)] [QuasiCompact (f ≫ g)] :
    rightDerivedLowerShriekCompIso Λ f g = (unboundedEtaleLowerShriekCompIso Λ f g).symm := by
  have h := unboundedEtaleLowerShriekCompIso_tower' (Λ := Λ) f g
    (HasCompactification.compactification g)
    ((HasCompactification.compactification (f ≫ g)).ofComp
      (HasCompactification.compactification g))
  have hrefl : rightDerivedLowerShriekIso Λ (HasCompactification.compactification g) =
      Iso.refl _ :=
    rightDerivedLowerShriekOfCompactificationIso_self _
  refine Iso.ext ?_
  rw [Iso.symm_hom, Iso.hom_eq_inv, h, hrefl]
  ext K
  simp only [rightDerivedLowerShriekCompIso, Iso.trans_inv, Iso.symm_inv,
    Functor.isoWhiskerRight_inv, NatTrans.comp_app, NatTrans.hcomp_app, Functor.whiskerRight_app,
    Iso.refl_inv, NatTrans.id_app, Category.assoc]
  -- the identity is stated at `R(g)_!`, the composite at `Rg_!(c)`
  erw [Category.id_comp]

variable {X X' Y Y' Z Z' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'} {g : Y ⟶ Z} {g' : Y' ⟶ Z'}
  {vX : X' ⟶ X} {vY : Y' ⟶ Y} {vZ : Z' ⟶ Z}

/-- **Vertical pasting of `Ex_!` as `ExchangeCompCompatible`**: the compactly supported base
change maps of two stacked cartesian squares and of their pasting are compatible with the
composition isomorphisms `AlgebraicGeometry.Etale.rightDerivedLowerShriekCompIso`
(`AlgebraicGeometry.Etale.rightDerivedLowerShriekBaseChangeMap_paste_vert`). -/
theorem exchangeCompCompatible_rightDerivedLowerShriekCompIso
    [QuasiCompact f] [QuasiCompact g] [QuasiCompact f'] [QuasiCompact g'] [QuasiCompact (f ≫ g)]
    [QuasiCompact (f' ≫ g')]
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    [HasCompactification f'] [HasCompactification g'] [HasCompactification (f' ≫ g')]
    (sqf : IsPullback vX f' f vY) (sqg : IsPullback vY g' g vZ)
    (sqgf : IsPullback vX (f' ≫ g') (f ≫ g) vZ) :
    Adjunction.ExchangeCompCompatible (rightDerivedLowerShriekBaseChangeMap Λ sqf)
      (rightDerivedLowerShriekBaseChangeMap Λ sqg) (rightDerivedLowerShriekBaseChangeMap Λ sqgf)
      (rightDerivedLowerShriekCompIso Λ f g) (rightDerivedLowerShriekCompIso Λ f' g') where
  comp M := by
    rw [rightDerivedLowerShriekCompIso_eq_unboundedEtaleLowerShriekCompIso_symm,
      rightDerivedLowerShriekCompIso_eq_unboundedEtaleLowerShriekCompIso_symm]
    simp only [Iso.symm_hom]
    have h := rightDerivedLowerShriekBaseChangeMap_paste_vert (Λ := Λ) sqf sqg sqgf M
    rw [← cancel_mono ((unboundedEtaleLowerShriekCompIso Λ f' g').hom.app
      ((L((vX)^*[ModuleCat.{u + 1} Λ])).obj M))]
    simp only [Category.assoc, Iso.inv_hom_id_app]
    rw [← h, ← Functor.map_comp_assoc, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id,
      Category.id_comp]
    -- the identity is stated at `R.obj (LvX^* M)`, the map at `(LvX^* ⋙ R).obj M`
    erw [Category.comp_id]

end AlgebraicGeometry.Etale
