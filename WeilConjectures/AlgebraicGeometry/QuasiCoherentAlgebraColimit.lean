/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.QuasiCoherentAlgebra
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Filtered.Basic
import WeilConjectures.AlgebraicGeometry.QuasiCoherentModuleColimitAffineSections
import WeilConjectures.CategoryTheory.SheafAlgebrasDirectedColimit

/-! # Directed colimits of quasi-coherent algebra sheaves

## References

* [Stacks Project, Tag 01ID](https://stacks.math.columbia.edu/tag/01ID)
* [Stacks Project, Tag 009E](https://stacks.math.columbia.edu/tag/009E)
* [Stacks Project, Tag 0087](https://stacks.math.columbia.edu/tag/0087)
* [Stacks Project, Tag 01AH](https://stacks.math.columbia.edu/tag/01AH)
* [Stacks Project, Tag 01AJ](https://stacks.math.columbia.edu/tag/01AJ)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open AlgebraicGeometry

namespace AlgebraicGeometry.Scheme

/-- Directed colimits of quasi-coherent algebra sheaves exist in all algebra sheaves,
are quasi-coherent, are the sheafification of the presheaf colimit with its coprojections,
have colimit rings of sections on affine opens, and commute with restriction to opens.
Being a colimit in all algebra sheaves with quasi-coherent vertex also gives the colimit
in their full subcategory of quasi-coherent algebras. Restriction uses the open site
`Over V`, whose objects are precisely the opens contained in `V`. -/
theorem quasiCoherentAlgebra_colimit
    (X : Scheme.{u}) (I : Type u) [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (F : I ⥤ X.CommAlgebraSheaf)
    (hF : ∀ i : I, X.IsQuasiCoherentAlgebra (F.obj i)) :
    ∃ (c : Cocone F),
      Nonempty (IsColimit c) ∧ X.IsQuasiCoherentAlgebra c.pt ∧
      (∃ (p : Cocone (F ⋙ Under.forget X.sheaf ⋙
          sheafToPresheaf (Opens.grothendieckTopology X) CommRingCat)),
        Nonempty (IsColimit p) ∧
        ∃ (e : (presheafToSheaf (Opens.grothendieckTopology X) CommRingCat).obj p.pt ≅
            c.pt.right),
          ∀ i : I, p.ι.app i ≫ toSheafify (Opens.grothendieckTopology X) p.pt ≫
            e.hom.hom = (c.ι.app i).right.hom) ∧
      (∀ (U : X.Opens), IsAffineOpen U →
        Nonempty (IsColimit
          (((evaluation X.Opensᵒᵖ CommRingCat).obj (op U)).mapCocone
            ((sheafToPresheaf (Opens.grothendieckTopology X) CommRingCat).mapCocone
              ((Under.forget X.sheaf).mapCocone c))))) ∧
      (∀ (V : X.Opens), Nonempty (IsColimit
        ((Under.post ((Opens.grothendieckTopology X).overPullback CommRingCat V)).mapCocone
          c))) := by
  classical
  let P := F ⋙ Under.forget X.sheaf ⋙
    sheafToPresheaf (Opens.grothendieckTopology X) CommRingCat
  let p := colimit.cocone P
  have hp (U : X.Opens) : Nonempty (IsColimit
      (((evaluation X.Opensᵒᵖ CommRingCat).obj (op U)).mapCocone p)) :=
    ⟨isColimitOfPreserves _ (colimit.isColimit P)⟩
  obtain ⟨σP, σ, ι, _, _, hι, hc, hm⟩ :=
    sheafAlgebras_directed_colimit X X.sheaf I F p hp
  let c : Cocone F := Cocone.mk (Under.mk σ) ι
  let M := commAlgebraSheafModuleFunctor X.sheaf
  obtain ⟨hq, hs⟩ := Modules.quasiCoherentModuleColimitAffineSections X I
    (F ⋙ M) (M.mapCocone c) hm.some hF
  refine ⟨c, hc, hq, ?_, ?_, ?_⟩
  · refine ⟨p, ⟨colimit.isColimit P⟩, Iso.refl _, ?_⟩
    intro i
    simpa using (hι i).symm
  · intro U hU
    obtain ⟨hsurj, hzero⟩ := hs U hU
    let r := ((evaluation X.Opensᵒᵖ CommRingCat).obj (op U)).mapCocone
      ((sheafToPresheaf (Opens.grothendieckTopology X) CommRingCat).mapCocone
        ((Under.forget X.sheaf).mapCocone c))
    let D := P ⋙ (evaluation X.Opensᵒᵖ CommRingCat).obj (op U)
    let κ := (colimit.isColimit D).desc r
    have hκ (i : I) (x : D.obj i) : κ (colimit.ι D i x) = r.ι.app i x :=
      ConcreteCategory.congr_hom ((colimit.isColimit D).fac r i) x
    have hsurjective : Function.Surjective κ := by
      intro s
      obtain ⟨i, x, hx⟩ := hsurj s
      exact ⟨colimit.ι D i x, (hκ i x).trans hx⟩
    have hinjective : Function.Injective κ := by
      apply (injective_iff_map_eq_zero κ.hom).mpr
      intro z hz
      obtain ⟨i, x, rfl⟩ := Concrete.colimit_exists_rep D z
      have hx : ((c.ι.app i).right.hom.app (op U)) x = 0 :=
        (hκ i x).symm.trans hz
      obtain ⟨j, hij, hj⟩ := (hzero i x).mp hx
      calc
        colimit.ι D i x = colimit.ι D j (D.map (homOfLE hij) x) :=
          (ConcreteCategory.congr_hom (colimit.w D (homOfLE hij)) x).symm
        _ = 0 := by rw [show D.map (homOfLE hij) x = 0 from hj]; exact map_zero _
    have : IsIso κ := (ConcreteCategory.isIso_iff_bijective κ).mpr
      ⟨hinjective, hsurjective⟩
    exact ⟨(colimit.isColimit D).ofPointIso⟩
  · intro V
    have : ((Opens.grothendieckTopology X).overPullback CommRingCat.{u} V).IsLeftAdjoint :=
      ((Over.forgetAdjStar V).sheafPushforwardContinuous
        ((Opens.grothendieckTopology X).over V)
        (Opens.grothendieckTopology X) (E := CommRingCat.{u})).isLeftAdjoint
    exact ⟨isColimitOfPreserves _ hc.some⟩

end AlgebraicGeometry.Scheme
