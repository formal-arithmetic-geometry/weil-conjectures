/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategoryBraided
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible

/-!

# The braiding of the derived tensor product on bounded constructible complexes

The derived category `D(Mod_{Λ_X})` of module objects over a commutative condensed ring `Λ`
carries the braiding `DerivedCategory.braidedCategory'` of the derived tensor product: the
symmetry of `Mod_{Λ_X}`, with the Koszul sign rule on complexes, descended along K-flat
resolutions. The bounded constructible complexes `Dᵇc(X)⟦Λ⟧` form a full monoidal subcategory
(`ProEtale.CondensedRing.isMonoidal_boundedConstructible`), and the braiding restricts to it
(`ObjectProperty.fullBraidedSubcategory`).

Since other braidings of derived categories are assumed as instances elsewhere,
`DerivedCategory.braidedCategory'` is not an instance, and neither is its restriction
`ProEtale.CondensedRing.boundedConstructibleBraiding`; it is meant to be used as a local
instance.

## Main definitions

- `ProEtale.CondensedRing.boundedConstructibleBraiding`: the Koszul braiding of `Dᵇc(X)⟦Λ⟧`.

-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {k : Type u} [Field k] (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom]
  [QuasiCompact X.hom] [IsSeparated X.hom]

set_option synthInstance.maxHeartbeats 400000 in
-- the generic search goes through the instances on `Mod (Sheaf (ProEt.topology X) Ab) _`
/-- The monoidal structure of `Dᵇc(X)⟦Λ⟧`, the full monoidal subcategory of `D(Mod_{Λ_X})`
(`isMonoidal_boundedConstructible`). Finding it from the generic instances exceeds the default
heartbeat limit, so it is recorded once here. -/
noncomputable instance monoidalCategory_boundedConstructible
    {ℓ : ℕ} [IsEllAdicFinitenessCoefficient ℓ Λ] [Fact (ringChar k ≠ ℓ)] :
    MonoidalCategory (Dᵇc(X.left)⟦Λ⟧) :=
  inferInstance

attribute [local instance] DerivedCategory.braidedCategory' in
/-- The Koszul braiding of the derived tensor product on `Dᵇc(X)⟦Λ⟧`: the restriction
(`ObjectProperty.fullBraidedSubcategory`) of the braiding `DerivedCategory.braidedCategory'` of
`D(Mod_{Λ_X})`. It is not an instance, see the module docstring. -/
@[instance_reducible]
noncomputable def boundedConstructibleBraiding
    {ℓ : ℕ} [IsEllAdicFinitenessCoefficient ℓ Λ] [Fact (ringChar k ≠ ℓ)] :
    BraidedCategory (Dᵇc(X.left)⟦Λ⟧) :=
  ObjectProperty.fullBraidedSubcategory _

end AlgebraicGeometry.ProEtale.CondensedRing
