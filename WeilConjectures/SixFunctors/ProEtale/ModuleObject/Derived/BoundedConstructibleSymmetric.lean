/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Monoidal.DerivedSymmetric
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleBraided

/-!

# The braiding of bounded constructible complexes is symmetric

The Koszul braiding `ProEtale.CondensedRing.boundedConstructibleBraiding` of `Dᵇc(X)⟦Λ⟧` is the
restriction of the braiding `DerivedCategory.braidedCategory'` of the derived tensor product of
module objects. Since the braiding of the relative tensor product of module objects is symmetric
(`CategoryTheory.Mod.braidingHom_braidingHom`), so is the derived braiding
(`DerivedCategory.braiding_hom_braiding_hom`), and so is its restriction
(`ProEtale.CondensedRing.boundedConstructibleBraiding_hom_braiding_hom`).

-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {k : Type u} [Field k] (X : Over (Spec (.of k))) {ℓ : ℕ} [IsEllAdicFinitenessCoefficient ℓ Λ]
  [Fact (ringChar k ≠ ℓ)]

attribute [local instance] boundedConstructibleBraiding in
/-- The Koszul braiding of `Dᵇc(X)⟦Λ⟧` is symmetric. -/
lemma boundedConstructibleBraiding_hom_braiding_hom (K L : Dᵇc(X.left)⟦Λ⟧) :
    (β_ K L).hom ≫ (β_ L K).hom = 𝟙 _ :=
  ObjectProperty.hom_ext _
    (DerivedCategory.braiding_hom_braiding_hom _ (fun M N ↦ Mod.braidingHom_braidingHom M N)
      K.obj L.obj)

end AlgebraicGeometry.ProEtale.CondensedRing
