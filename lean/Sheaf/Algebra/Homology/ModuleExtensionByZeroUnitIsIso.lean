module

public import Sheaf.Algebra.Homology.OpenRestrictionAdjunctionExact
import Sheaf.Algebra.Homology.ModuleExtensionByZeroUnitMono
import Sheaf.Algebra.Homology.ModuleExtensionByZeroUnitEpi
import Sheaf.CategoryTheory.ExtensionByZeroPresheaf

/-! # Invertibility of the open extension unit

Source: Stacks Project, Sheaves Lemma 00A7 (4).
(blueprint: lem-sc-module-extension-by-zero-unit-isiso).
-/

@[expose] public section
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
universe u
noncomputable section
namespace AlgebraicGeometry
set_option linter.style.haveILetI false
/-- The unit of the chosen extension-by-zero/restriction adjunction is an isomorphism.
Source: Stacks Project, Sheaves Lemma 00A7 (4), label lemma-j-shriek-modules;
Modules on Sites Lemma 03DI, label lemma-extension-by-zero.
(blueprint: lem-sc-module-extension-by-zero-unit-isiso).

Proof: First use the canonical adjunction obtained by direct-sum injections followed by
module sheafification. On opens contained in W the extension presheaf has one summand,
canonically the original section module. These identifications commute with restriction.
Sheafification on W therefore gives back the original sheaf, and the canonical unit is
an isomorphism. Compare this adjunction with the chosen one by uniqueness of left adjoints:
the comparison is a natural automorphism of extension by zero, and the units differ by
its restriction. Thus the chosen unit is also an isomorphism. The argument works for
W empty (the category of module sheaves is then trivial) and W equal to X. -/
theorem moduleExtensionByZero_unit_isIso (X : RingedSpace.{u}) (W : Opens X)
    (G : SheafOfModules.{u} ((moduleRings X).over W)) :
    IsIso ((Classical.choice (open_restriction_adjunction_exact X W).2.2.2.2).unit.app G)
    := by
  let f := (Classical.choice (open_restriction_adjunction_exact X W).2.2.2.2).unit.app G
  haveI : Mono f := moduleExtensionByZero_unit_mono X W G
  haveI : Epi f := moduleExtensionByZero_unit_epi X W G
  exact isIso_of_mono_of_epi f

end AlgebraicGeometry
