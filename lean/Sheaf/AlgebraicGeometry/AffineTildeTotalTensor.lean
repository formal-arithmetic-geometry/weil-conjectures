/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S2
-/
module

public import Sheaf.AlgebraicGeometry.DerivedCategory
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Sheaf.Algebra.Homology.KFlat
import Sheaf.AlgebraicGeometry.Modules.AffineTildeTensor

/-! # Tilde and the unbounded total tensor complex

Source: Stacks Project, Tag 08DX, proof of the affine computation.
(blueprint: lem-pc-affine-tilde-total-tensor).
-/

@[expose] public section

universe u w

open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry

noncomputable local instance affineTotalTensor (A : Type u) [CommRing A] :
    MonoidalCategory (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace)) :=
  SheafOfModules.monoidalCategory (Spec (.of A)).sheaf

set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Tilde commutes naturally with the total tensor complex, for two arbitrary unbounded
module complexes. Source: Stacks Project, Tag 08DX, proof of part (2), and Tag 01I8.
(blueprint: lem-pc-affine-tilde-total-tensor).

Proof: the affine tilde tensor comparison of Tag 01I8 identifies, in each bidegree,
`tilde(P.X p) tensor tilde(N.X q)` with `tilde(P.X p tensor N.X q)`. Its uniqueness
on pure global tensors implies naturality in both factors. Consequently it respects
both differentials, including the sign on the second differential. The tilde functor
is a left adjoint to global sections, and therefore preserves every coproduct indexed
by the pairs (p,q) with p+q=n, even when the complexes are unbounded. Apply these
coproduct comparisons degreewise to obtain mutually inverse chain maps. Checking on
each summand gives naturality with respect to maps of both input complexes. Applying
Q to this natural total-complex isomorphism gives the stated localized comparison. -/
theorem affineTilde_totalTensor_natIso (A : Type u) [CommRing A]
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))] :
    Nonempty
      ((@Functor.mapHomologicalComplex _ _ _ _ _ _ _
        (@id (ModuleCat.{u} A ⥤
          SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))
          (tilde.functor (.of A))) ⟨fun _ _ ↦ tilde.map_zero⟩ (.up ℤ)) ⋙
        (curriedTensor
          (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))).map₂CochainComplex ⋙
        (Functor.whiskeringLeft (CochainComplex (ModuleCat.{u} A) ℤ)
          (CochainComplex
            (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace)) ℤ)
          (CochainComplex
            (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace)) ℤ)).obj
          (@Functor.mapHomologicalComplex _ _ _ _ _ _ _
        (@id (ModuleCat.{u} A ⥤
          SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))
          (tilde.functor (.of A))) ⟨fun _ _ ↦ tilde.map_zero⟩ (.up ℤ)) ⋙
          (Functor.whiskeringRight (CochainComplex (ModuleCat.{u} A) ℤ)
            (CochainComplex
              (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace)) ℤ)
            (schemeDerivedCategory (Spec (.of A)))).obj DerivedCategory.Q ≅
        (curriedTensor (ModuleCat.{u} A)).map₂CochainComplex ⋙
          (Functor.whiskeringRight (CochainComplex (ModuleCat.{u} A) ℤ)
            (CochainComplex (ModuleCat.{u} A) ℤ)
            (schemeDerivedCategory (Spec (.of A)))).obj
            ((@Functor.mapHomologicalComplex _ _ _ _ _ _ _
        (@id (ModuleCat.{u} A ⥤
          SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))
          (tilde.functor (.of A))) ⟨fun _ _ ↦ tilde.map_zero⟩ (.up ℤ)) ⋙ DerivedCategory.Q)) := by
  sorry

end AlgebraicGeometry
