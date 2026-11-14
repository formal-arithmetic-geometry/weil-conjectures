/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Scheme
public import WeilConjectures.CategoryTheory.SiteCechComplex
public import Mathlib.Algebra.Homology.Homotopy
import WeilConjectures.AlgebraicGeometry.AlternatingCechFirstSortingIdentity
import WeilConjectures.AlgebraicGeometry.AlternatingCechSecondSortingIdentity

/-!
# Null homotopy for the kernel of ordered restriction

## References

* Stacks Project, Tags 01FJ, 01FK and 01FM
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

/-- A full Čech endomorphism whose increasing coordinates vanish is null homotopic
(Stacks, Tag 01FM). -/
theorem alternatingCechKernelNullHomotopic (X : Scheme.{u}) {I : Type v} [LinearOrder I]
    (U : I → X.Opens) (F : X.Opensᵒᵖ ⥤ AddCommGrpCat.{w})
    (S : SiteCechComplex U (fun i ↦ homOfLE (le_top : U i ≤ ⊤)))
    (f : S.complex F ⟶ S.complex F)
    (hf : ∀ (p : ℕ) (s : S.cochains F p)
      (t : {t : Fin (p + 1) → I // StrictMono t}), (f.f p s) t.1 = 0) :
    Nonempty (Homotopy f 0) := by
  classical
  let h := Homotopy.nullHomotopy' (cechFirstSortingFamily X U F S)
  let k := Homotopy.nullHomotopy' (cechSecondSortingFamily X U F S)
  have he : f ≫ (Homotopy.nullHomotopicMap' (cechFirstSortingFamily X U F S) +
      Homotopy.nullHomotopicMap' (cechSecondSortingFamily X U F S)) = f := by
    apply HomologicalComplex.Hom.ext
    funext p
    rw [HomologicalComplex.comp_f, HomologicalComplex.add_f_apply,
      cechFirstSortingIdentity, cechSecondSortingIdentity]
    have hz : f.f p ≫ cechAlternatingProjectionMap X U F S p = 0 := by
      ext s
      funext t
      change (∑ σ : Equiv.Perm (Fin (p + 1)),
        if StrictMono (t ∘ σ) then
          (Equiv.Perm.sign σ : ℤ) • F.map (S.indexMap t σ).op
            ((f.f p s) (t ∘ σ)) else 0) = 0
      apply Finset.sum_eq_zero
      intro σ _
      split_ifs with ht
      · rw [hf p s ⟨t ∘ σ, ht⟩]
        simp
      · rfl
    rw [sub_add_sub_cancel]
    change (f.f p : S.cochains F p ⟶ S.cochains F p) ≫
      (𝟙 (S.cochains F p) - cechAlternatingProjectionMap X U F S p) = f.f p
    erw [Preadditive.comp_sub, Category.comp_id, hz, sub_zero]
  refine ⟨?_⟩
  simpa only [he, comp_zero, add_zero] using (h.add k).compLeft f

end AlgebraicGeometry.Scheme
