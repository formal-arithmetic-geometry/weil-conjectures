/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.CategoryTheory.Sites.Adjunction
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.CategoryTheory.Sites.GlobalSections

/-! # Constant set comparisons for left exact left adjoints. -/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory

/-- The canonical set-sheaf comparison for a left exact inverse-image.
Source: Stacks Project, `sites.tex`, Tags 0H7J and 00YV
(auxiliary; not a blueprint node). -/
theorem canonicalConstantSetComparison
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    (JC : GrothendieckTopology C) (JD : GrothendieckTopology D)
    (L : Sheaf JC (Type u) ⥤ Sheaf JD (Type u))
    (V : Sheaf JD (Type u) ⥤ Sheaf JC (Type u)) (adj : L ⊣ V)
    (hL : PreservesFiniteLimits L) :
    Nonempty (constantSheaf JC (Type u) ⋙ L ≅ constantSheaf JD (Type u)) := by
  classical
  have : PreservesFiniteLimits L := hL
  let pointComparison :
      L.obj ((constantSheaf JC (Type u)).obj PUnit.{u + 1}) ≅
        (constantSheaf JD (Type u)).obj PUnit.{u + 1} :=
    ((Types.isTerminalPUnit.isTerminalObj (Functor.const Cᵒᵖ) _).isTerminalObj
      (presheafToSheaf JC (Type u)) _).isTerminalObj L _ |>.uniqueUpToIso
        (Types.isTerminalPUnit.isTerminalObj (Functor.const Dᵒᵖ) _ |>.isTerminalObj
          (presheafToSheaf JD (Type u)) _)
  let globalComparison : V ⋙ Sheaf.Γ JC (Type u) ≅ Sheaf.Γ JD (Type u) := by
    exact Functor.isoWhiskerLeft V (Sheaf.ΓNatIsoCoyoneda JC PUnit.{u + 1}) ≪≫
      (adj.compCoyonedaIso.app (Opposite.op
        ((constantSheaf JC (Type u)).obj PUnit.{u + 1}))).symm ≪≫
      coyoneda.mapIso pointComparison.symm.op ≪≫
      (Sheaf.ΓNatIsoCoyoneda JD PUnit.{u + 1}).symm
  let kappaType : constantSheaf JC (Type u) ⋙ L ≅ constantSheaf JD (Type u) :=
    (((constantSheafΓAdj JC (Type u)).comp adj).ofNatIsoRight globalComparison).leftAdjointUniq
      (constantSheafΓAdj JD (Type u))
  exact ⟨kappaType⟩

/-- Conjugate a comparison natural in all sets by the constant-sheaf/forget
comparison. Source: Stacks, Sites, Tag 00YV
(auxiliary; not a blueprint node). -/
noncomputable def constantRingSetComparison
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    (JC : GrothendieckTopology C) (JD : GrothendieckTopology D)
    [HasWeakSheafify JC CommRingCat.{u}] [HasWeakSheafify JD CommRingCat.{u}]
    (L : Sheaf JC (Type u) ⥤ Sheaf JD (Type u))
    (kappa : constantSheaf JC (Type u) ⋙ L ≅ constantSheaf JD (Type u)) :
    (constantSheaf JC CommRingCat.{u} ⋙ sheafForget JC ⋙ L) ≅
      constantSheaf JD CommRingCat.{u} ⋙ sheafForget JD := by
    refine NatIso.ofComponents (fun A ↦ ?_) ?_
    · exact (L.mapIso ((constantCommuteCompose JC (forget CommRingCat)).app A) ≪≫
        (kappa.app A) ≪≫
        (((constantCommuteCompose JD (forget CommRingCat)).app A).symm))
    · intro A B f
      have hJ := (constantCommuteCompose JC (forget CommRingCat)).hom.naturality f
      have hD := (constantCommuteCompose JD (forget CommRingCat)).inv.naturality f
      have hJ' : (sheafForget JC).map ((constantSheaf JC CommRingCat).map f) ≫
          (constantCommuteCompose JC (forget CommRingCat)).hom.app B =
          (constantCommuteCompose JC (forget CommRingCat)).hom.app A ≫
            (constantSheaf JC (Type u)).map (forget CommRingCat |>.map f) := by
        simpa only [Functor.comp_map] using hJ
      have hD' : (constantSheaf JD (Type u)).map (forget CommRingCat |>.map f) ≫
          (constantCommuteCompose JD (forget CommRingCat)).inv.app B =
          (constantCommuteCompose JD (forget CommRingCat)).inv.app A ≫
            (sheafForget JD).map ((constantSheaf JD CommRingCat).map f) := by
        simpa only [Functor.comp_map] using hD
      have hk := kappa.hom.naturality ((forget CommRingCat).map f)
      have hk' : L.map ((constantSheaf JC (Type u)).map ((forget CommRingCat).map f)) ≫
          kappa.hom.app B = kappa.hom.app A ≫
            (constantSheaf JD (Type u)).map ((forget CommRingCat).map f) := by
        simpa only [Functor.comp_map] using hk
      dsimp
      rw [← Category.assoc, ← L.map_comp, hJ', L.map_comp]
      change L.map ((constantCommuteCompose JC (forget CommRingCat)).hom.app A) ≫
        L.map ((constantSheaf JC (Type u)).map ((forget CommRingCat).map f)) ≫
          kappa.hom.app B ≫ (constantCommuteCompose JD (forget CommRingCat)).inv.app B = _
      calc
        _ = L.map ((constantCommuteCompose JC (forget CommRingCat)).hom.app A) ≫
            (L.map ((constantSheaf JC (Type u)).map ((forget CommRingCat).map f)) ≫
              kappa.hom.app B) ≫
            (constantCommuteCompose JD (forget CommRingCat)).inv.app B := by
              simp only [Category.assoc]
        _ = L.map ((constantCommuteCompose JC (forget CommRingCat)).hom.app A) ≫
            (kappa.hom.app A ≫
              (constantSheaf JD (Type u)).map ((forget CommRingCat).map f)) ≫
            (constantCommuteCompose JD (forget CommRingCat)).inv.app B := by rw [hk']
        _ = L.map ((constantCommuteCompose JC (forget CommRingCat)).hom.app A) ≫
            kappa.hom.app A ≫
            ((constantSheaf JD (Type u)).map ((forget CommRingCat).map f) ≫
              (constantCommuteCompose JD (forget CommRingCat)).inv.app B) := by
              simp only [Category.assoc]
        _ = L.map ((constantCommuteCompose JC (forget CommRingCat)).hom.app A) ≫
            kappa.hom.app A ≫
            ((constantCommuteCompose JD (forget CommRingCat)).inv.app A ≫
              (sheafForget JD).map ((constantSheaf JD CommRingCat).map f)) := by rw [hD']
        _ = _ := by simp only [Category.assoc]

end CategoryTheory
