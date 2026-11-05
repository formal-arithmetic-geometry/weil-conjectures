/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Modules.ClearDenominators
public import WeilConjectures.AlgebraicGeometry.Modules.RestrictionTensorComparison

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry.Scheme.Modules

/-- The restriction tensor comparison characterized by its inverse on pure tensor sections.
This characterization determines the inverse uniquely by the sheaf tensor universal property,
and hence determines the isomorphism. Thus the choice here is of a uniquely specified map,
not of arbitrary data from a mere existence statement.
Source: Stacks Project, Modules, Tag 01CD.
(blueprint: def-sc-tensor-power-open-restriction-comparisons). -/
noncomputable def openRestrictionTensorIso {X Y : Scheme.{u}} (j : Y ⟶ X)
    [IsOpenImmersion j] (F G : X.Modules) :
    (F ⊗ G).restrict j ≅ F.restrict j ⊗ G.restrict j :=
  Classical.choose (exists_restriction_tensor_comparison j F G)

/-- Restriction of tensor powers, constructed recursively from the unit and tensor comparisons.
Source: Stacks Project, Modules, Tag 01CD, iterated over tensor powers.
(blueprint: def-sc-tensor-power-open-restriction-comparisons). -/
noncomputable def openRestrictionTensorPowIso {X Y : Scheme.{u}} (j : Y ⟶ X)
    [IsOpenImmersion j] (L : X.Modules) :
    (n : ℕ) → (L.tensorPow n).restrict j ≅ (L.restrict j).tensorPow n
  | 0 => restrictUnitIso j
  | n + 1 => openRestrictionTensorIso j L (L.tensorPow n) ≪≫
      (Iso.refl (L.restrict j) ⊗ᵢ openRestrictionTensorPowIso j L n)

/-- The numerator comparison as an isomorphism of module sheaves, so its components are
compatible with every restriction map. Source: Stacks Project, Modules, Tag 01CD.
(blueprint: def-sc-tensor-power-open-restriction-comparisons). -/
noncomputable def openRestrictionNumeratorIso {X Y : Scheme.{u}} (j : Y ⟶ X)
    [IsOpenImmersion j] (F L : X.Modules) (n : ℕ) :
    (F ⊗ L.tensorPow n).restrict j ≅ F.restrict j ⊗ (L.restrict j).tensorPow n :=
  openRestrictionTensorIso j F (L.tensorPow n) ≪≫
    (Iso.refl (F.restrict j) ⊗ᵢ openRestrictionTensorPowIso j L n)

end AlgebraicGeometry.Scheme.Modules
