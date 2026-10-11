import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Sheaf.Topology.RingedSpaceModuleCohomology

/-! # Cohomology of a module sheaf agrees with that of its underlying abelian sheaf

Source: Stacks Project, sites-cohomology.tex, Lemma Tag 03FD
(blueprint: lem-sc-module-abelian-zariski-cohomology).
-/

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace

noncomputable section

namespace AlgebraicGeometry

/-- The right-derived cohomology of an `O_X`-module sheaf agrees with the
cohomology of its underlying abelian sheaf, naturally in the module sheaf.
Source: Stacks Project, sites-cohomology.tex, Lemma Tag 03FD.
Proof: forgetful exactness and an injective module resolution give an injective
resolution after forgetting; the acyclic-resolution comparison identifies both
cohomologies, naturally in the sheaf (blueprint: lem-sc-module-abelian-zariski-cohomology). -/
theorem module_cohomology_iso_underlying_abelian
    (X : Scheme.{u})
    (F : SheafOfModules.{u} (moduleRings X.toRingedSpace))
    (q : ℕ)
    [hE : EnoughInjectives (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})] :
    Nonempty
      ((forget₂ (ModuleCat.{u}
          ((moduleRings X.toRingedSpace).obj.obj (Opposite.op ⊤))) AddCommGrpCat).obj
          ((RingedSpace.moduleCohomology X.toRingedSpace q).obj F) ≅
        @CategoryTheory.Sheaf.H' _ _ _ _
          (CategoryTheory.hasExt_of_enoughInjectives _)
          ((SheafOfModules.toSheaf (moduleRings X.toRingedSpace)).obj F)
          q ⊤) := by
  sorry

end AlgebraicGeometry
