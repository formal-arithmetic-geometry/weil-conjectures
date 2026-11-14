/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Coherent
public import WeilConjectures.AlgebraicGeometry.PseudoCoherentComplex
public import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.AlgebraicGeometry.CoherentAffineFreeResolution

/-! # Coherent modules are pseudo-coherent on Noetherian schemes

Stacks Project, Tag 08E8.
-/

@[expose] public section

universe u w

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- A coherent module on a Noetherian scheme, regarded as a complex concentrated in degree
zero, is pseudo-coherent (Stacks, Tag 08E8). -/
theorem isPseudoCoherent_singleFunctor_obj_of_isCoherent (Y : Scheme.{u}) [IsNoetherian Y]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [∀ U : Y.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings Y.toRingedSpace).over U))]
    (F : SheafOfModules.{u} (moduleRings Y.toRingedSpace))
    (hF : RingedSpace.IsCoherent Y.toRingedSpace F) :
    Y.IsPseudoCoherent
      ((DerivedCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).obj F) := by
  intro y
  obtain ⟨U, A, _, _, hy, _, M, _, _, _, e, _, E, hE, hfree, q, hq⟩ :=
    AlgebraicGeometry.coherent_affine_free_resolution Y F hF y
  refine ⟨U, hy, E, hE, hfree, ?_⟩
  have : QuasiIso q := hq
  exact ⟨((SheafOfModules.overFunctor.{u}
    (moduleRings Y.toRingedSpace) U).mapDerivedCategorySingleFunctor 0).app F ≪≫
      (asIso (DerivedCategory.Q.map q)).symm⟩

end AlgebraicGeometry.Scheme
