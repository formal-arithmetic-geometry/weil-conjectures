/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Morphisms.UniversalHomeomorphism
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Basic
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-!

# The reduction of a scheme over a base

For a scheme `X` over `S`, the reduced closed subscheme `X_red ⟶ X` cut out by the nilradical,
as a scheme over `S` (`CategoryTheory.Over.reduced`, `CategoryTheory.Over.reducedι`). The inclusion
is a finite universal homeomorphism, and a morphism from a reduced scheme factors through it
(`CategoryTheory.Over.reducedLift`).

-/

@[expose] public section

universe u

open AlgebraicGeometry

namespace CategoryTheory.Over

variable {S : Scheme.{u}} (G : Over S)

/-- The reduced subscheme `G_red` of a scheme `G` over `S`, as a scheme over `S`. -/
noncomputable abbrev reduced : Over S :=
  Over.mk (G.left.nilradical.subschemeι ≫ G.hom)

/-- The closed immersion `G_red ⟶ G` of the reduced subscheme, as a morphism over `S`. -/
noncomputable def reducedι : G.reduced ⟶ G :=
  Over.homMk G.left.nilradical.subschemeι

instance : IsClosedImmersion G.reducedι.left :=
  inferInstanceAs (IsClosedImmersion G.left.nilradical.subschemeι)

instance : Mono G.reducedι :=
  Over.mono_of_mono_left _

instance : IsReduced G.reduced.left :=
  inferInstanceAs (IsReduced G.left.nilradical.subscheme)

instance : IsFinite G.reducedι.left :=
  inferInstanceAs (IsFinite G.left.nilradical.subschemeι)

instance : Surjective G.reducedι.left := ⟨by
  change Function.Surjective G.left.nilradical.subschemeι
  rw [← Set.range_eq_univ, Scheme.IdealSheafData.range_subschemeι, Scheme.support_nilradical]
  rfl⟩

instance : IsUniversalHomeomorphism G.reducedι.left where

instance [LocallyOfFiniteType G.hom] : LocallyOfFiniteType G.reduced.hom :=
  inferInstanceAs (LocallyOfFiniteType (G.left.nilradical.subschemeι ≫ G.hom))

instance [QuasiCompact G.hom] : QuasiCompact G.reduced.hom :=
  inferInstanceAs (QuasiCompact (G.left.nilradical.subschemeι ≫ G.hom))

instance [IsSeparated G.hom] : IsSeparated G.reduced.hom :=
  inferInstanceAs (IsSeparated (G.left.nilradical.subschemeι ≫ G.hom))

/-- A morphism `X ⟶ G` over `S` from a reduced scheme factors (uniquely, as `G_red ⟶ G` is a
monomorphism) through the reduced subscheme `G_red`. -/
noncomputable def reducedLift {X : Over S} [IsReduced X.left] (f : X ⟶ G) : X ⟶ G.reduced :=
  Over.homMk (IsClosedImmersion.lift G.left.nilradical.subschemeι f.left (by
      rw [Scheme.IdealSheafData.ker_subschemeι,
        Scheme.IdealSheafData.le_ker_iff_range_subset_support]
      simp))
    ((IsClosedImmersion.lift_fac_assoc _ _ _ _).trans (Over.w f))

@[reassoc (attr := simp)]
theorem reducedLift_reducedι {X : Over S} [IsReduced X.left] (f : X ⟶ G) :
    G.reducedLift f ≫ G.reducedι = f := by
  apply Over.OverMorphism.ext
  exact IsClosedImmersion.lift_fac _ _ _

end CategoryTheory.Over
