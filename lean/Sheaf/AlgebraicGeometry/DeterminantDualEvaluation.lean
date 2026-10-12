/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P3
-/
module

public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Sheaf.AlgebraicGeometry.Modules.ExteriorSheaf
public import Sheaf.Paper.DerivedHomMayerVietoris
public import WeilConjectures.AlgebraicGeometry.Modules.LocallyFreeRank
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
import Mathlib.LinearAlgebra.ExteriorPower.Pairing
import Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree

/-! # Ordinary determinant evaluation

Source: Stacks Project, Tag 0BRT, final determinant inversion.
(blueprint: lem-sc-determinant-dual-evaluation).
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry

/-- The top exterior powers of a finite locally free sheaf and its internal dual
are tensor inverses in the ordinary category of sheaves of modules.
Source: Stacks Project, Tag 0BRT, final determinant inversion.
(blueprint: lem-sc-determinant-dual-evaluation).

Proof: trivialize M as the free sheaf of rank d on an open cover. Internal Hom
into the structure sheaf restricts to the dual free module. The determinant pairing
of exterior powers takes the wedge of the dual basis and the wedge of the basis to
1. These top exterior powers are free of rank one, so the pairing is an isomorphism
locally. Under a change of basis the two generators scale by inverse determinants;
hence the pairing is independent of the trivialization. The sectionwise determinant
pairings commute with restrictions and descend through sheafification and the
sheaf tensor product. The local inverses agree on overlaps by uniqueness of the
inverse and glue to a global inverse. For d=0 the empty wedges give the structure
sheaf and the pairing is multiplication. On the empty scheme all maps involved
are the unique isomorphisms. -/
theorem determinant_dual_evaluation (X : Scheme.{u})
    (M : X.Modules) (d : ℕ) (hfree : M.IsFiniteLocallyFreeOfRank d) :
    letI := SheafOfModules.monoidalCategory X.sheaf
    let L : SheafOfModules.{u} (moduleRings X.toRingedSpace) :=
      Scheme.Modules.exteriorSheaf
        (SheafOfModules.homObj (R := X.sheaf) M
          (SheafOfModules.unit X.ringCatSheaf)) d
    let F : SheafOfModules.{u} (moduleRings X.toRingedSpace) :=
      Scheme.Modules.exteriorSheaf M d
    Nonempty (L ⊗ F ≅ 𝟙_ (SheafOfModules.{u} (moduleRings X.toRingedSpace))) := by sorry

end AlgebraicGeometry
