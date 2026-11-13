/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.AlgebraicGeometry.Sites.Proetale
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Fpqc

/-! # The structure sheaf on the small pro-etale site

## References

* Stacks Project, Tags 03O3 and 098K.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- Global sections, restricted to weakly etale schemes over `S`, with pullback of functions
(Stacks, Tags 03O3 and 098K). -/
def proEtaleStructurePresheaf (S : Scheme.{u}) : S.ProEtᵒᵖ ⥤ CommRingCat.{u} :=
  (ProEt.forget S ⋙ Over.forget S).op ⋙ Scheme.Γ

/-- Global sections form a sheaf for pro-etale coverings (Stacks, Tag 03O3). -/
theorem proEtaleStructurePresheaf_isSheaf (S : Scheme.{u}) :
    Presheaf.IsSheaf (ProEt.topology S) (proEtaleStructurePresheaf S) := by
  exact Functor.op_comp_isSheaf_of_isSheaf _ _ proetaleTopology _
    (isSheaf_Γ proetaleTopology)

/-- The pro-etale structure sheaf, with sections `Γ(U, O_U)` and the usual restriction maps
(Stacks, Tags 03O3 and 098K). -/
def proEtaleStructureSheaf (S : Scheme.{u}) : Sheaf (ProEt.topology S) CommRingCat.{u} :=
  ⟨proEtaleStructurePresheaf S, proEtaleStructurePresheaf_isSheaf S⟩

end AlgebraicGeometry.Scheme
