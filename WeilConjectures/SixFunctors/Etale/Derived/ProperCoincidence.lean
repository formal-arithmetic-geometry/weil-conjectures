/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionRefinement
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekToLowerStar
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarCompCoherence

/-!
# Proper coincidence: `Rf_! ≅ Rf_*` canonically

For a compactification `c = (X ⟶[i] Z ⟶[g] Y)` of `f`, the *forget-supports* map
`ψ_c : Rf_!(c) = Rg_* D(i_!) ⟶ Rg_* Ri_* ⟶ Rf_*`. For a refinement of compactifications the
comparison of lower shrieks intertwines the forget-supports maps.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

variable {X Y : Scheme.{u}} {f : X ⟶ Y} {c d : Compactification f} (r : c.Refinement d)

/-- Associativity of the composition maps of derived pushforwards along a refinement. -/
lemma rightDerivedLowerStarCompHom_refinement_assoc
    (M : DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    (rightDerivedLowerStarCompHom A r.hom d.g c.g r.hom_g.symm).app (R((c.i)_*[A]).obj M) ≫
        (rightDerivedLowerStarCompHom A c.i c.g f c.comm).app M =
      R((d.g)_*[A]).map ((rightDerivedLowerStarCompHom A c.i r.hom d.i r.i_hom.symm).app M) ≫
        (rightDerivedLowerStarCompHom A d.i d.g f d.comm).app M := by
  have h := leftDerivedUpperStarComp_assoc' A c.i r.hom d.g d.i c.g f r.i_hom.symm
    r.hom_g.symm d.comm
  have e₁ := conjugateEquiv_whiskerRight (derivedUpperStarLowerStarAdjunction A c.g)
    ((derivedUpperStarLowerStarAdjunction A d.g).comp (derivedUpperStarLowerStarAdjunction A r.hom))
    (derivedUpperStarLowerStarAdjunction A c.i) (leftDerivedUpperStarComp A r.hom d.g c.g
      r.hom_g.symm).hom
  sorry

end Etale

end AlgebraicGeometry
