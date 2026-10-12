/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P1
-/
module

public import Sheaf.AlgebraicGeometry.DerivedTensorStructure
public import Sheaf.Algebra.Homology.DerivedInternalHom
import Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorClosed
import Sheaf.Algebra.Homology.HomTensorTotal
import Sheaf.Algebra.Homology.KFlat
import Sheaf.Algebra.Homology.KFlatResolution
import Sheaf.Algebra.Homology.KInjectiveHomComplex
import Sheaf.Algebra.Homology.QuasiIsoHomComplexMap
import Sheaf.Algebra.Homology.RhomGlobalSections
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutions

/-! # Derived internal-Hom adjunction on a scheme

Source: Stacks Project, Cohomology, Tags 08DJ and 0FPB
(blueprint: lem-sc-derived-internal-hom-adjunction).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.MonoidalCategory Opposite TopologicalSpace

namespace AlgebraicGeometry

/-- The derived tensor-internal-Hom bijection and tensor symmetry, natural in all variables.
The second bijection is obtained from the first by precomposing with the inverse symmetry.
The tensor is the shared K-flat derived tensor, and RHom is the shared K-injective model.
Source: Stacks Project, Cohomology, Tags 08DJ and 0FPB
(blueprint: lem-sc-derived-internal-hom-adjunction).

Proof:
1. Choose K-flat representatives P of K and L' of L using lem-pc-kflat-resolution and
   the K-injective representative I of M from def-pur-derived-internal-hom and
   prop-pur-kinjective-resolutions-exist. Use the closed sheaf tensor of
   lem-pc-sheaf-modules-tensor-closed.
2. By lem-pur-rhom-well-defined, Hom(L,I) and Hom(L',I) are quasi-isomorphic.
   By lem-pur-hom-kflat-into-kinjective the latter and Hom(P,Hom(L',I)) are K-injective.
   The complex isomorphism of lem-sc-derived-hom-tensor-total identifies this last complex
   with Hom(Tot(P tensor L'),I), representing RHom(K tensor^L L,M).
   Taking H^0 of global sections and using lem-pur-rhom-global-sections gives the bijection.
3. The comparisons in lem-pur-rhom-well-defined, lem-pur-hom-kflat-into-kinjective,
   lem-sc-derived-hom-tensor-total and lem-pur-rhom-global-sections are canonical and
   natural, proving independence of representatives and the displayed naturality equation.
4. The sheaf tensor symmetry with sign (-1)^(pq) gives an isomorphism of total complexes
   Tot(P tensor L') and Tot(L' tensor P). Both compute the shared derived tensors.
   A quasi-isomorphism tensored with a K-flat complex remains a quasi-isomorphism: its
   cone is the tensor with the acyclic cone, acyclic by def-pc-kflat-complex.
   Common K-flat resolutions from lem-pc-kflat-resolution therefore make the symmetry
   independent of choices and natural. Precomposition gives the final natural bijection. -/
theorem scheme_derivedInternalHom_adjunction (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))] :
    ∃ (e : ∀ K L M : schemeDerivedCategory X,
        (K ⟶ (derivedInternalHom (Opens.grothendieckTopology X.toRingedSpace)
          X.toRingedSpace.sheaf).obj (op L, M)) ≃ (K ⊗ L ⟶ M))
      (s : ∀ K L : schemeDerivedCategory X, K ⊗ L ≅ L ⊗ K)
      (e' : ∀ K L M : schemeDerivedCategory X,
        (K ⟶ (derivedInternalHom (Opens.grothendieckTopology X.toRingedSpace)
          X.toRingedSpace.sheaf).obj (op L, M)) ≃ (L ⊗ K ⟶ M)),
      (∀ (K K' L L' M M' : schemeDerivedCategory X)
        (a : K' ⟶ K) (b : L' ⟶ L) (c : M ⟶ M')
        (f : K ⟶ (derivedInternalHom (Opens.grothendieckTopology X.toRingedSpace)
          X.toRingedSpace.sheaf).obj (op L, M)),
        e K' L' M' (a ≫ f ≫
          (derivedInternalHom (Opens.grothendieckTopology X.toRingedSpace)
            X.toRingedSpace.sheaf).map (b.op, c)) =
          (a ⊗ₘ b) ≫ e K L M f ≫ c) ∧
      (∀ (K K' L L' : schemeDerivedCategory X) (a : K ⟶ K') (b : L ⟶ L'),
        (a ⊗ₘ b) ≫ (s K' L').hom = (s K L).hom ≫ (b ⊗ₘ a)) ∧
      (∀ (K L M : schemeDerivedCategory X)
        (f : K ⟶ (derivedInternalHom (Opens.grothendieckTopology X.toRingedSpace)
          X.toRingedSpace.sheaf).obj (op L, M)),
        e' K L M f = (s K L).inv ≫ e K L M f) ∧
      (∀ (K K' L L' M M' : schemeDerivedCategory X)
        (a : K' ⟶ K) (b : L' ⟶ L) (c : M ⟶ M')
        (f : K ⟶ (derivedInternalHom (Opens.grothendieckTopology X.toRingedSpace)
          X.toRingedSpace.sheaf).obj (op L, M)),
        e' K' L' M' (a ≫ f ≫
          (derivedInternalHom (Opens.grothendieckTopology X.toRingedSpace)
            X.toRingedSpace.sheaf).map (b.op, c)) =
          (b ⊗ₘ a) ≫ e' K L M f ≫ c) := by
  sorry

end AlgebraicGeometry
