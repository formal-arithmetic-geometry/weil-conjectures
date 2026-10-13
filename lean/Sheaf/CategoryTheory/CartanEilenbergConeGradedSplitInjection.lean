/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q3
-/
module

public import Sheaf.CategoryTheory.CartanEilenbergPresentation
public import Sheaf.Algebra.Homology.FilteredComplexSubquotients
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone

/-! # A normalized split injection from the retained column cone

Source: Stacks Project, Homology, Tags 012X and 0133; retained-column construction
(blueprint: lem-sp-cartan-eilenberg-cone-graded-split-injection).
-/

@[expose] public section

universe uA vA
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory.Functor

/-- The retained cone summands give a normalized map into the quotient with a left inverse.
Source: Stacks Project, Tags 012X and 0133; retained-column quotient construction.
(blueprint: lem-sp-cartan-eilenberg-cone-graded-split-injection).

Proof: in degree m, project the ambient cone onto the complex-index-p summands.
The cone K summand is retained only when m+1=p; otherwise the corresponding
extended-single source in the column cone is zero. On the total summand use
its coproduct universal property to project onto index p, and identify this
summand with the extended resolution term. The projection kills every
column of index greater than p and the K summand present in step p+1.
It therefore descends from step p through the evaluated cokernel to a map u.
For each retained term, its ambient inclusion factors through step p since
its image is one of the summands in the stipulated supremum. Below b that
term is zero, so use its unique zero map. The two resulting lifts, with
extension identifications, define v by the degreewise cone biproduct.
Their quotient composites are the displayed normalization equations.
The ambient projection after each inclusion is identity. Thus v followed
by u is identity, checked on the two cone coprojections. When m=p-1 the
resolution term is zero; when m>=p the extended-single term is zero. These
cases also cover p<b, when both retained terms vanish. No identity for u
followed by v is asserted here: surjectivity is a separate generating-family
argument. -/
theorem cartanEilenberg_cone_graded_split_injection
    {A : Type uA} [Category.{vA} A] [Abelian A] [IsGrothendieckAbelian.{vA} A]
    (K : CochainComplex A ℤ)
    (I : HomologicalComplex₂ A (ComplexShape.up ℤ) (ComplexShape.up ℕ))
    (a : ((CochainComplex.single₀ A).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      K ⟶ I)
    (b : ℤ)
    (hIbelow : ∀ s : ℤ, s < b → IsZero (I.X s))
    (hKbelow : ∀ s : ℤ, s < b → IsZero (K.X s))
    (aug : K ⟶ (((CartanEilenbergPresentation.mappedFunctor (𝟭 A)).obj I).flip).total
      (ComplexShape.up ℤ))
    (F : DecreasingFiltration (CochainComplex.mappingCone aug))
    (hF : ∀ p n : ℤ, F.complexStep p n =
        (if p ≤ n + 1 then imageSubobject
          ((CochainComplex.mappingCone.inl aug).v (n + 1) n (by omega)) else ⊥) ⊔
        (Finset.Icc (max b p) n).sup (fun s ↦ imageSubobject
          ((((CartanEilenbergPresentation.mappedFunctor (𝟭 A)).obj I).flip).ιTotalOrZero
            (ComplexShape.up ℤ) (n - s) s n ≫
              (CochainComplex.mappingCone.inr aug).f n)))
    (p m : ℤ) (hm : p - 1 ≤ m) :
    ∃ v : (CochainComplex.mappingCone
      (HomologicalComplex.extendMap (a.f p) ComplexShape.embeddingUpNat)).X (m - p) ⟶
        (F.gradedPiece p).X m,
      (∃ u, v ≫ u = 𝟙 _) ∧
  (∀ (r : ℕ) (h : (r : ℤ) + p = m),
    ∃ l : (I.X p).X r ⟶ (F.step p : CochainComplex A ℤ).X m,
      l ≫ (F.step p).arrow.f m =
        (HomologicalComplex.extendXIso
          (((𝟭 A).mapHomologicalComplex (ComplexShape.up ℕ)).obj (I.X p))
          ComplexShape.embeddingUpNat (i := r) (i' := m - p)
          (by change (r : ℤ) = m - p; omega)).inv ≫
        (((CartanEilenbergPresentation.mappedFunctor (𝟭 A)).obj I).flip).ιTotal
          (ComplexShape.up ℤ) (m - p) p m (by change (m - p) + p = m; omega) ≫
        (CochainComplex.mappingCone.inr aug).f m ∧
      l ≫ (F.complexQuotientπ p (p + 1) (by omega)).f m =
        (HomologicalComplex.extendXIso (I.X p) ComplexShape.embeddingUpNat
          (i := r) (i' := m - p)
          (by change (r : ℤ) = m - p; omega)).inv ≫
        (CochainComplex.mappingCone.inr
          (HomologicalComplex.extendMap (a.f p) ComplexShape.embeddingUpNat)).f (m - p) ≫
        v) ∧
  (∀ h : m + 1 = p,
    ∃ l : K.X p ⟶ (F.step p : CochainComplex A ℤ).X m,
      l ≫ (F.step p).arrow.f m =
        (K.XIsoOfEq h.symm).hom ≫
        (CochainComplex.mappingCone.inl aug).v (m + 1) m (by omega) ∧
      l ≫ (F.complexQuotientπ p (p + 1) (by omega)).f m =
        (HomologicalComplex.extendXIso ((CochainComplex.single₀ A).obj (K.X p))
          ComplexShape.embeddingUpNat (i := 0) (i' := m - p + 1)
          (by change (0 : ℤ) = m - p + 1; omega)).inv ≫
        (CochainComplex.mappingCone.inl
          (HomologicalComplex.extendMap (a.f p) ComplexShape.embeddingUpNat)).v
          (m - p + 1) (m - p) (by omega) ≫ v) := by sorry

end CategoryTheory.Functor
