/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.CartanEilenbergPresentation
import WeilConjectures.CategoryTheory.CartanEilenbergConeFiltration
import WeilConjectures.CategoryTheory.DegreewiseFilteredAcyclic
import Mathlib.Algebra.Homology.SingleHomology
import Mathlib.Algebra.Homology.Embedding.ExtendHomology
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic

/-! # Quasi-isomorphism of the augmented total

## References

* Stacks Project, Homology, Tag 0133 (Lemma 12.25.4), and Derived Categories, Tag 015J.
-/

@[expose] public section

universe uA vA

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Functor

/-- Exact augmented columns give a quasi-isomorphism to their bounded-diagonal total.
No injectivity hypothesis is needed, and the augmentation is supplied as a chain map.
Stacks Project, Homology, Tag 0133 (Lemma 12.25.4); Derived Categories, Tag 015J. -/
theorem cartanEilenberg_augmentation_quasiIso
    {A : Type uA} [Category.{vA} A] [Abelian A] [IsGrothendieckAbelian.{vA} A]
    (K : CochainComplex A ℤ)
    (I : HomologicalComplex₂ A (ComplexShape.up ℤ) (ComplexShape.up ℕ))
    (a : ((CochainComplex.single₀ A).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      K ⟶ I)
    (hbelow : ∃ b : ℤ, ∀ s : ℤ, s < b → IsZero (I.X s))
    (hrows : ∀ s : ℤ, QuasiIso (a.f s))
    (aug : K ⟶ (((CartanEilenbergPresentation.mappedFunctor (𝟭 A)).obj I).flip).total
      (ComplexShape.up ℤ))
    (haug : ∀ n : ℤ, aug.f n = (a.f n).f 0 ≫
      (HomologicalComplex.extendXIso
        (((𝟭 A).mapHomologicalComplex (ComplexShape.up ℕ)).obj (I.X n))
        ComplexShape.embeddingUpNat (i := 0) (i' := 0) rfl).inv ≫
      (((CartanEilenbergPresentation.mappedFunctor (𝟭 A)).obj I).flip).ιTotal
        (ComplexShape.up ℤ) 0 n n (zero_add n)) :
    QuasiIso aug := by
  obtain ⟨b, hb⟩ := hbelow
  have hKbelow (s : ℤ) (hs : s < b) : IsZero (K.X s) := by
    have : QuasiIso (a.f s) := hrows s
    have hi : IsZero ((I.X s).homology 0) :=
      (HomologicalComplex.homologyFunctor A (ComplexShape.up ℕ) 0).map_isZero (hb s hs)
    have hk := (asIso (HomologicalComplex.homologyMap (a.f s) 0)).isZero_iff.mpr hi
    exact (HomologicalComplex.singleObjHomologySelfIso
      (ComplexShape.up ℕ) 0 (K.X s)).isZero_iff.mp hk
  obtain ⟨F, _, hbounds, hgraded⟩ := cartanEilenberg_cone_filtration
    K I a b hb hKbelow aug haug
  apply (CochainComplex.mappingCone.quasiIso_iff_acyclic aug).mpr
  apply degreewiseFiltered_acyclic (CochainComplex.mappingCone aug) F
    (fun n ↦ ⟨b, n + 2, hbounds n⟩)
  intro p n
  obtain ⟨e⟩ := hgraded p n
  have : QuasiIso (a.f p) := hrows p
  have hcone := (CochainComplex.mappingCone.quasiIso_iff_acyclic
    (HomologicalComplex.extendMap (a.f p) ComplexShape.embeddingUpNat)).mp
      (inferInstance : QuasiIso _)
  exact ((F.gradedPiece p).exactAt_iff_isZero_homology n).mpr
    (e.isZero_iff.mpr (hcone (n - p)).isZero_homology)

end CategoryTheory.Functor
