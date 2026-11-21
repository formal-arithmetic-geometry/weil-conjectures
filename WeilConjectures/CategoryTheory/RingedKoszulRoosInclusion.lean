/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.Algebra.Homology.ExactProductsRoosComparison
public import WeilConjectures.CategoryTheory.RingedKoszulSystem
import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMap
import WeilConjectures.Algebra.Homology.TelescopeHomRoosArrow
import WeilConjectures.CategoryTheory.RingedKoszulFiniteHomTower

/-! # Ordinary Koszul limits and the explicit Roos fibre

Source: Stacks Project, sites-cohomology.tex, Tag 0A0A; derived.tex, Tag 0949.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
variable (O : Sheaf J CommRingCat.{u}) (r : ℕ)
variable (b : Fin r → (O.obj ⋙ forget CommRingCat).sections)

/-- The zero-second-coordinate map from the ordinary limit of the strict Koszul tensor
 tower to its explicit Roos fibre is a quasi-isomorphism on K-injective coefficients.

Source: Stacks Project, sites-cohomology.tex, Tag 0A0A; derived.tex, Tag 0949. -/
theorem quasiIso_ringedKoszul_roosComparison (I : ringedSiteComplex O)
    [I.IsKInjective] :
    QuasiIso (ExactProductsRoos.comparison.app (ringedKoszulTensorTowerComplex O r b I)) := by
  obtain ⟨f, hf₁, hf₂, hf⟩ :=
    CochainComplex.quasiIso_telescopeColimit O (ringedKoszulDiagram O r b)
  let : QuasiIso f := hf
  have hHom : QuasiIso (((homComplexFunctor (R := O)).map f.op).app I) := by
    simpa only [Functor.map_id, Category.comp_id] using
      (quasiIso_homComplex_map (𝟙 I) f)
  obtain ⟨e⟩ := exists_ringedKoszul_finiteHomTower_iso O r b I
  obtain ⟨a⟩ := telescopeHom_roos_arrow_iso O (ringedKoszulDiagram O r b) I
    (ringedKoszulTensorTowerComplex O r b I) e f hf₁ hf₂
  exact (quasiIso_iff_of_arrow_mk_iso _ _ a).mp hHom

end CategoryTheory
