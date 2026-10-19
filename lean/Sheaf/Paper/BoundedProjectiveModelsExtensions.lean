/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.Plus
public import Mathlib.CategoryTheory.Preadditive.Projective.Basic
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.KProjective
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import Mathlib.Algebra.Homology.HomotopyCategory.KProjective

/-! # Extensions of bounded complexes with projective terms

Source: Stacks Project, derived.tex, Tag 064B; mapping-cone construction in
proetale.tex, Tag 09C3 (blueprint: lem-sf-bounded-projective-models-extensions).
-/

@[expose] public section

set_option autoImplicit false

universe v u w

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace DerivedCategory

/-- Bounded models in an isomorphism-invariant class of projectives closed under
binary biproducts are closed under extensions.

Source: Stacks Project, derived.tex, Tag 064B; proetale.tex, Tag 09C3
(blueprint: lem-sf-bounded-projective-models-extensions).

Proof: represent the two end objects by bounded complexes. The source of the
connecting morphism is K-projective, so that morphism has an actual chain-map
representative into the shift of the first model. The cone has terms which are
binary biproducts of the two models, and remains bounded. Two rotations of the
given triangle identify its middle object shifted by one with this cone. Shift
back by minus one. Neither the chain maps nor their matrix entries need be constant. -/
theorem bounded_projective_models_extensions
    {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    (F : C → Prop)
    (hiso : ∀ {X Y : C}, (X ≅ Y) → F X → F Y)
    (hbiprod : ∀ X Y : C, F X → F Y → F (X ⊞ Y))
    (hprojective : ∀ X : C, F X → Projective X)
    (T : Triangle (DerivedCategory C)) (hT : T ∈ distTriang _)
    (h₁ : ∃ (P : CochainComplex C ℤ) (a b : ℤ),
      P.IsStrictlyGE a ∧ P.IsStrictlyLE b ∧ (∀ i, F (P.X i)) ∧
      Nonempty (T.obj₁ ≅ Q.obj P))
    (h₃ : ∃ (P : CochainComplex C ℤ) (a b : ℤ),
      P.IsStrictlyGE a ∧ P.IsStrictlyLE b ∧ (∀ i, F (P.X i)) ∧
      Nonempty (T.obj₃ ≅ Q.obj P)) :
    ∃ (P : CochainComplex C ℤ) (a b : ℤ),
      P.IsStrictlyGE a ∧ P.IsStrictlyLE b ∧ (∀ i, F (P.X i)) ∧
      Nonempty (T.obj₂ ≅ Q.obj P) := by
  obtain ⟨P₁, a₁, b₁, hge₁, hle₁, hP₁, ⟨e₁⟩⟩ := h₁
  obtain ⟨P₃, a₃, b₃, hge₃, hle₃, hP₃, ⟨e₃⟩⟩ := h₃
  have : ∀ n, Projective (P₃.X n) := fun n ↦ hprojective _ (hP₃ n)
  have : P₃.IsKProjective := CochainComplex.isKProjective_of_projective _ b₃
  have := P₁.isStrictlyGE_shift a₁ 1 (a₁ - 1) (by omega)
  have := P₁.isStrictlyLE_shift b₁ 1 (b₁ - 1) (by omega)
  obtain ⟨ψ, hψ⟩ := CochainComplex.IsKProjective.exists_Q_map_eq P₃ (P₁⟦(1 : ℤ)⟧)
    (e₃.inv ≫ T.mor₃ ≫ e₁.hom⟦(1 : ℤ)⟧' ≫ ((Q.commShiftIso (1 : ℤ)).app P₁).inv)
  have hcomm : Q.map ψ ≫ ((Q.commShiftIso (1 : ℤ)).app P₁).hom ≫ e₁.inv⟦(1 : ℤ)⟧' =
      e₃.inv ≫ T.mor₃ := by
    rw [hψ]
    simp [← Functor.map_comp]
  obtain ⟨f, -⟩ := Pretriangulated.exists_iso_of_arrow_iso _ _
    (mappingCone_triangle_distinguished ψ)
    (Pretriangulated.rot_of_distTriang _ (Pretriangulated.rot_of_distTriang _ hT))
    (Arrow.isoMk e₃.symm (((Q.commShiftIso (1 : ℤ)).app P₁) ≪≫
      (shiftFunctor _ 1).mapIso e₁.symm) hcomm.symm)
  let P := CochainComplex.mappingCone ψ
  have hge : P.IsStrictlyGE (min (a₃ - 1) (a₁ - 1)) :=
    CochainComplex.isStrictlyGE_mappingCone ψ a₃ (a₁ - 1) _
  have hle : P.IsStrictlyLE (max (b₃ - 1) (b₁ - 1)) := by
    rw [CochainComplex.isStrictlyLE_iff]
    intro i hi
    rw [CochainComplex.mappingCone.isZero_X_iff]
    exact ⟨P₃.isZero_of_isStrictlyLE b₃ _ (by omega),
      (P₁⟦(1 : ℤ)⟧).isZero_of_isStrictlyLE (b₁ - 1) _ (by omega)⟩
  have hP (i : ℤ) : F (P.X i) := by
    apply hiso (HomologicalComplex.homotopyCofiber.XIsoBiprod ψ i (i + 1) rfl).symm
    exact hbiprod _ _ (hP₃ (i + 1)) (hP₁ (i + 1))
  have := P.isStrictlyGE_shift (min (a₃ - 1) (a₁ - 1)) (-1)
    (min (a₃ - 1) (a₁ - 1) + 1) (by omega)
  have := P.isStrictlyLE_shift (max (b₃ - 1) (b₁ - 1)) (-1)
    (max (b₃ - 1) (b₁ - 1) + 1) (by omega)
  refine ⟨P⟦(-1 : ℤ)⟧, min (a₃ - 1) (a₁ - 1) + 1,
    max (b₃ - 1) (b₁ - 1) + 1, inferInstance, inferInstance, fun i ↦ hP (i - 1), ?_⟩
  exact ⟨((shiftFunctorCompIsoId _ (1 : ℤ) (-1) (by omega)).app T.obj₂).symm ≪≫
    (shiftFunctor _ (-1)).mapIso (Triangle.π₃.mapIso f).symm ≪≫
    ((Q.commShiftIso (-1 : ℤ)).app P).symm⟩

end DerivedCategory
