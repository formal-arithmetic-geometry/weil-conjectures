/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group X2
-/
module

public import Sheaf.AlgebraicGeometry.PerfectComplex
public import Sheaf.Paper.KoszulComplex
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.Algebra.Homology.Embedding.CochainComplex

/-! # Geometric properties of the explicit affine Koszul complex
Source: Stacks Project, Tags 0A9A and 0663.
(blueprint: lem-pc-affine-koszul-geometric-properties).
-/

@[expose] public section
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

/-- The actual sheafified finite Koszul complex is perfect and acyclic
where one of its defining functions is invertible.
Source: Stacks Project, Tag 0A9A, affine paragraph, and Tag 0663.
(blueprint: lem-pc-affine-koszul-geometric-properties).

Proof: In cochain degree -q the complex is the sheaf associated to the q-th exterior
power of the free module on Fin r; these are finite free and vanish for q > r.
On every principal affine neighbourhood, restriction identifies these sheaves with
finite free modules over the restricted structure sheaf. Thus the displayed complex
is locally strictly perfect, with bounds -r and 0. For a point not containing f i,
multiplication by f i is a unit in
its local ring. Exterior multiplication by the i-th basis vector is a homotopy
between multiplication by f i and zero (Tag 0663); after localization this contracts
the complex. All its homology stalks therefore vanish at that point.
For r = 0 the support assertion has no hypotheses satisfied, and the complex is the
structure sheaf in degree zero. The zero ring has no points and causes no exception. -/
theorem affine_koszul_geometric_properties
    (A : Type u) [CommRing A] (r : ℕ) (f : Fin r → A)
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))]
    [∀ V : (Spec (.of A)).Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings (Spec (.of A)).toRingedSpace).over V))] :
    let Q := DerivedCategory.Q.obj
      ((@Functor.mapHomologicalComplex ℤ (ModuleCat.{u} A)
        (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))
        _ _ _ _ (tilde.functor (.of A))
        ⟨fun _ _ ↦ tilde.map_zero⟩ (ComplexShape.up ℤ)).obj
        ((ExteriorAlgebra.koszulComplex A r f).extend ComplexShape.embeddingDownNat))
    Scheme.IsPerfect (Spec (.of A)) Q ∧
      ∀ (n : ℤ) (x : PrimeSpectrum A), (∃ i, f i ∉ x.asIdeal) →
        Subsingleton (↑(TopCat.Presheaf.stalk ((DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace)) n).obj
            Q).val.presheaf x)) := by sorry

end AlgebraicGeometry
