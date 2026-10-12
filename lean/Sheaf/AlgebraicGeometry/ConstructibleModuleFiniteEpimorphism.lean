/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S1
-/
module

public import Sheaf.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasColimitsOfShape
public import Mathlib.Algebra.Category.ModuleCat.Adjunctions

/-!
# Finite affine free covers of constructible module sheaves

Source: Stacks Project, Etale Cohomology, Tag 095N, proof of the finite surjection.
(blueprint: lem-weil-pbc-constructible-module-finite-epimorphism).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- A constructible module sheaf on a qcqs scheme receives an epimorphism from a
finite coproduct of free sheaves on affine etale objects.

Source: Stacks Project, Etale Cohomology, Tag 095N,
`lemma-category-constructible-modules`, proof after the first displayed surjection.
(blueprint: lem-weil-pbc-constructible-module-finite-epimorphism).

Proof: Each section on an etale object gives a morphism from its sheafified free
module by free Yoneda and sheafification. At each geometric point, finite stalks
allow finitely many sections representing all stalk elements; shrink their pointed
neighbourhoods to affine ones. The induced map from the finite coproduct is
surjective at this stalk. Each finite affine free coproduct is constructible:
identify each summand with etale extension by zero of the constant rank-one
sheaf, apply Tag 03S8, and use closure under finite sums. Its map to F therefore
has constructible cokernel by Tag 03RZ. The support of this cokernel is
constructible by Tag 09YS, and stalk exactness identifies it with failure of
surjectivity. Enlarging the finite family decreases the support. Independence of
stalk vanishing from the geometric point over a fixed point shows that every
point is avoided by one such support. The constructible topology of the qcqs
scheme is compact, hence finitely many supports have empty intersection.
Concatenate their families: its cokernel support is empty, hence its cokernel
has zero geometric stalks. Conservativity makes the cokernel zero, so the map
is epi. The empty scheme and zero sheaf permit the empty family. -/
theorem exists_affine_free_etale_epimorphism
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (hF : IsConstructibleEtaleModuleSheaf F) :
    let P : X.Etale → Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ) := fun W =>
      (presheafToSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
        (uliftYoneda.{u + 1}.obj W ⋙ ModuleCat.free Λ)
    ∃ (n : ℕ) (U : Fin n → X.Etale), (∀ i, IsAffine (U i).left) ∧
      ∃ g : (∐ fun i : Fin n => P (U i)) ⟶ F, Epi g := by sorry

end AlgebraicGeometry.Scheme
