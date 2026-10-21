/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weil SHEAF project
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived

/-! # Shift coherence of a normalized derived square

Source: Stacks Project, sites-cohomology.tex, Tag 0D6G, with Tag 08FI and the
integer-shift refinement in the DAG.
(blueprint: lem-weil-pbc-derived-square-shift-on-kinjectives)

The two computation maps below insert the canonical exact-functor factorization
isomorphisms. The comparison and its right-derived presentations remain specified data.
-/

@[expose] public section

universe uA uB uA' uB' vA vB vA' vB' wA wB wA' wB'

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

variable {A : Type uA} {B : Type uB} {A' : Type uA'} {B' : Type uB'}
  [Category.{vA} A] [Category.{vB} B] [Category.{vA'} A'] [Category.{vB'} B']
  [Abelian A] [Abelian B] [Abelian A'] [Abelian B']
  [HasDerivedCategory.{wA} A] [HasDerivedCategory.{wB} B]
  [HasDerivedCategory.{wA'} A'] [HasDerivedCategory.{wB'} B']

/-- The computation map `a_I = r_D(η_I) φ_r⁻¹` in the proof of Stacks Tag 0D6G.
It is defined for every complex, and is invertible on K-injectives.
(blueprint: lem-weil-pbc-derived-square-shift-on-kinjectives) -/
noncomputable def derivedSquareLeftComputation
    (F : A ⥤ B) (r : B ⥤ B') [F.Additive] [r.Additive]
    [PreservesFiniteLimits r] [PreservesFiniteColimits r]
    (RF : DerivedCategory A ⥤ DerivedCategory B)
    (ηF : F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ RF)
    (I : CochainComplex A ℤ) :
    DerivedCategory.Q.obj
        ((r.mapHomologicalComplex (.up ℤ)).obj ((F.mapHomologicalComplex (.up ℤ)).obj I)) ⟶
      (RF ⋙ r.mapDerivedCategory).obj (DerivedCategory.Q.obj I) :=
  r.mapDerivedCategoryFactors.inv.app ((F.mapHomologicalComplex (.up ℤ)).obj I) ≫
    r.mapDerivedCategory.map (ηF.app I)

/-- The computation map `b_I = RG(φ_t⁻¹) η_{C(t)I}` in Stacks Tag 0D6G.
It is defined for every complex, and is invertible when `C(t)I` is K-injective.
(blueprint: lem-weil-pbc-derived-square-shift-on-kinjectives) -/
noncomputable def derivedSquareRightComputation
    (G : A' ⥤ B') (t : A ⥤ A') [G.Additive] [t.Additive]
    [PreservesFiniteLimits t] [PreservesFiniteColimits t]
    (RG : DerivedCategory A' ⥤ DerivedCategory B')
    (ηG : G.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ RG)
    (I : CochainComplex A ℤ) :
    DerivedCategory.Q.obj
        ((G.mapHomologicalComplex (.up ℤ)).obj ((t.mapHomologicalComplex (.up ℤ)).obj I)) ⟶
      (t.mapDerivedCategory ⋙ RG).obj (DerivedCategory.Q.obj I) :=
  ηG.app ((t.mapHomologicalComplex (.up ℤ)).obj I) ≫
    RG.map (t.mapDerivedCategoryFactors.inv.app I)

/-- A normalized derived square is computed by its specified termwise comparison and
commutes with every integer shift.

Source: Stacks Project, sites-cohomology.tex, Tag 0D6G (restriction of direct images),
Tag 08FI (restriction preserves K-injectives), and derived.tex, Tags 015F and 070H.
(blueprint: lem-weil-pbc-derived-square-shift-on-kinjectives)

Proof: (1) Insert the exact factorization isomorphisms to form `a_I` and `b_I`.
The comparison units are invertible on K-injectives, and `C(t)` preserves these,
so both computation maps are isomorphisms. (2) Apply the stipulated normalization
at `I`; naturality along any representative isomorphism `QI ≅ E` gives the first
formula. (3) The K-injective-shift lemma makes `I[n]` another admissible model,
including negative integers. Additivity identifies termwise functors applied to
this model with their shifts. (4) Naturality of δ shows that both shifted chain
maps have component δ at `I.X (a+n)`; their differentials are multiplied by
`n.negOnePow`, with no sign on δ. (5) The prescribed shift compatibility of the
two units and the exact factorization isomorphisms transports this chain-map
identity to the derived square at `QI`; cancel `a_(I[n])`. (6) Every derived
object has a K-injective representative: first use essential surjectivity of Q,
then a quasi-isomorphism to a K-injective. Naturality of γ and both shift
comparisons transports the equality to every E. This proves the assertion for
the specified γ, without choosing another derived isomorphism.
-/
theorem derivedSquare_shift_on_kinjectives
    (F : A ⥤ B) (G : A' ⥤ B') (t : A ⥤ A') (r : B ⥤ B')
    [F.Additive] [G.Additive] [t.Additive] [r.Additive]
    [PreservesFiniteLimits t] [PreservesFiniteColimits t]
    [PreservesFiniteLimits r] [PreservesFiniteColimits r]
    (δ : F ⋙ r ≅ t ⋙ G)
    (hA : ∀ K : CochainComplex A ℤ, ∃ I : CochainComplex A ℤ,
      I.IsKInjective ∧ ∃ s : K ⟶ I, QuasiIso s)
    (hA' : ∀ K : CochainComplex A' ℤ, ∃ I : CochainComplex A' ℤ,
      I.IsKInjective ∧ ∃ s : K ⟶ I, QuasiIso s)
    (ht : ∀ I : CochainComplex A ℤ, I.IsKInjective →
      CochainComplex.IsKInjective ((t.mapHomologicalComplex (.up ℤ)).obj I))
    (RF : DerivedCategory A ⥤ DerivedCategory B)
    (RG : DerivedCategory A' ⥤ DerivedCategory B')
    (ηF : F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ RF)
    (ηG : G.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ RG)
    [RF.IsRightDerivedFunctor ηF (HomologicalComplex.quasiIso A (.up ℤ))]
    [RG.IsRightDerivedFunctor ηG (HomologicalComplex.quasiIso A' (.up ℤ))]
    (hηF : ∀ I : CochainComplex A ℤ, I.IsKInjective → IsIso (ηF.app I))
    (hηG : ∀ I : CochainComplex A' ℤ, I.IsKInjective → IsIso (ηG.app I))
    [RF.CommShift ℤ] [RG.CommShift ℤ]
    (hshiftF : ∀ (I : CochainComplex A ℤ), I.IsKInjective → ∀ n : ℤ,
      ηF.app (I⟦n⟧) ≫ ((DerivedCategory.Q ⋙ RF).commShiftIso n).hom.app I =
        ((F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q).commShiftIso n).hom.app I ≫
          (ηF.app I)⟦n⟧')
    (hshiftG : ∀ (I : CochainComplex A' ℤ), I.IsKInjective → ∀ n : ℤ,
      ηG.app (I⟦n⟧) ≫ ((DerivedCategory.Q ⋙ RG).commShiftIso n).hom.app I =
        ((G.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q).commShiftIso n).hom.app I ≫
          (ηG.app I)⟦n⟧')
    (γ : RF ⋙ r.mapDerivedCategory ≅ t.mapDerivedCategory ⋙ RG)
    (hnorm : ∀ K : CochainComplex A ℤ,
      derivedSquareLeftComputation F r RF ηF K ≫ γ.hom.app (DerivedCategory.Q.obj K) =
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex δ.hom (.up ℤ)).app K) ≫
          derivedSquareRightComputation G t RG ηG K) :
    (∀ (E : DerivedCategory A) (I : CochainComplex A ℤ), I.IsKInjective →
      ∀ e : DerivedCategory.Q.obj I ≅ E,
      IsIso (derivedSquareLeftComputation F r RF ηF I) ∧
      IsIso (derivedSquareRightComputation G t RG ηG I) ∧
      derivedSquareLeftComputation F r RF ηF I ≫
          (RF ⋙ r.mapDerivedCategory).map e.hom ≫ γ.hom.app E =
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex δ.hom (.up ℤ)).app I) ≫
          derivedSquareRightComputation G t RG ηG I ≫
            (t.mapDerivedCategory ⋙ RG).map e.hom) ∧
    (∀ (n : ℤ) (E : DerivedCategory A),
      γ.hom.app (E⟦n⟧) ≫ ((t.mapDerivedCategory ⋙ RG).commShiftIso n).hom.app E =
        ((RF ⋙ r.mapDerivedCategory).commShiftIso n).hom.app E ≫ (γ.hom.app E)⟦n⟧') ∧
    (∀ (I : CochainComplex A ℤ), I.IsKInjective → ∀ n : ℤ,
      (NatTrans.mapHomologicalComplex δ.hom (.up ℤ)).app (I⟦n⟧) ≫
          ((t.mapHomologicalComplex (.up ℤ) ⋙
            G.mapHomologicalComplex (.up ℤ)).commShiftIso n).hom.app I =
        ((F.mapHomologicalComplex (.up ℤ) ⋙
          r.mapHomologicalComplex (.up ℤ)).commShiftIso n).hom.app I ≫
            ((NatTrans.mapHomologicalComplex δ.hom (.up ℤ)).app I)⟦n⟧') ∧
    (∀ (I : CochainComplex A ℤ), I.IsKInjective → ∀ n a : ℤ,
      ((NatTrans.mapHomologicalComplex δ.hom (.up ℤ)).app (I⟦n⟧)).f a = δ.hom.app (I.X (a + n)) ∧
      (((NatTrans.mapHomologicalComplex δ.hom (.up ℤ)).app I)⟦n⟧').f a = δ.hom.app (I.X (a + n)) ∧
      ((r.mapHomologicalComplex (.up ℤ)).obj
          ((F.mapHomologicalComplex (.up ℤ)).obj (I⟦n⟧))).d a (a + 1) =
        n.negOnePow • r.map (F.map (I.d (a + n) (a + 1 + n))) ∧
      ((G.mapHomologicalComplex (.up ℤ)).obj
          ((t.mapHomologicalComplex (.up ℤ)).obj (I⟦n⟧))).d a (a + 1) =
        n.negOnePow • G.map (t.map (I.d (a + n) (a + 1 + n)))) := by
  sorry

end CategoryTheory
