/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Scheme
public import WeilConjectures.CategoryTheory.SiteCechComplex
public import Mathlib.Algebra.Homology.Homotopy
import WeilConjectures.AlgebraicGeometry.AlternatingCechSection
import WeilConjectures.AlgebraicGeometry.AlternatingCechKernelNullHomotopic

/-!
# Homotopy inverse for ordered Čech restriction

## References

* Stacks Project, Tags 01FJ, 01FK and 01FM
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

/-- A complex whose terms are identified with sections on increasing tuples, and a
cochain map which is restriction in those identifications, has a homotopy inverse
(Stacks, Tags 01FJ, 01FK and 01FM). -/
theorem alternatingCechRestrictionHomotopy (X : Scheme.{u}) {I : Type v} [LinearOrder I]
    (U : I → X.Opens) (F : X.Opensᵒᵖ ⥤ AddCommGrpCat.{w})
    (S : SiteCechComplex U (fun i ↦ homOfLE (le_top : U i ≤ ⊤)))
    (A : CochainComplex AddCommGrpCat.{max v w} ℕ)
    (e : ∀ p : ℕ, A.X p ≅ AddCommGrpCat.of
      (∀ t : {t : Fin (p + 1) → I // StrictMono t}, F.obj (op (S.W p t.1))))
    (r : S.complex F ⟶ A)
    (hr : ∀ (p : ℕ) (s : S.cochains F p)
      (t : {t : Fin (p + 1) → I // StrictMono t}),
      (e p).hom ((r.f p) s) t = s t.1) :
    ∃ i : A ⟶ S.complex F,
      Nonempty (Homotopy (r ≫ i) (𝟙 (S.complex F))) ∧
      Nonempty (Homotopy (i ≫ r) (𝟙 A)) := by
  obtain ⟨i, hi⟩ := alternatingCechRestrictionHomotopy_map X U F S A e r hr
  have hz : ∀ (p : ℕ) (s : S.cochains F p)
      (t : {t : Fin (p + 1) → I // StrictMono t}),
      (((r ≫ i - 𝟙 (S.complex F)).f p) s) t.1 = 0 := by
    intro p s t
    have heq := congrArg (fun g : A ⟶ A ↦ (e p).hom (g.f p ((r.f p) s))) hi
    have ht := congrFun heq t
    simp only [HomologicalComplex.comp_f, HomologicalComplex.id_f,
      AddCommGrpCat.comp_apply, AddCommGrpCat.id_apply, hr] at ht
    change ((r ≫ i).f p s) t.1 - s t.1 = 0
    exact sub_eq_zero.mpr ht
  obtain ⟨h⟩ := alternatingCechKernelNullHomotopic X U F S (r ≫ i - 𝟙 _) hz
  exact ⟨i, ⟨⟨Homotopy.equivSubZero.symm h⟩, ⟨Homotopy.ofEq hi⟩⟩⟩

end AlgebraicGeometry.Scheme
