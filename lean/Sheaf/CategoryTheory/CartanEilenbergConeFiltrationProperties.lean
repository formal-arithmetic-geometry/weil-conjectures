module

public import Sheaf.CategoryTheory.CartanEilenbergPresentation
public import Sheaf.Algebra.Homology.FilteredComplexSubquotients
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import Sheaf.CategoryTheory.DoubleComplexTotal
import Sheaf.CategoryTheory.Filtration
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic

@[expose] public section

universe uA vA
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory.Functor
/-- Bounds and graded-piece calculation for the constructed filtration.
Source: Stacks Project, Homology, Tag 0133.  On a fixed diagonal `n`, every
nonzero bicomplex summand has complex index between `b` and `n`, while the
cone's `K` summand has index `n+1`; hence the displayed image-sum is the whole
cone at step `b` and is zero at step `n+2`, including empty intervals.  For
the quotient of consecutive steps, all summands except those of index `p`
vanish.  The surviving differential is the column differential, and the
off-diagonal map is identified with `a.f p` by `haug` and the extension
isomorphism.  Reindexing degree `n` to `n-p` therefore identifies the graded
complex with the mapping cone of `extendMap (a.f p)`; applying homology gives
the asserted isomorphism.  This argument uses only canonical projections and
inclusions, so it also covers zero columns and all integer indices.
Source: Stacks Project, Homology, Tag 0133.
(blueprint: lem-sp-cartan-eilenberg-cone-filtration-properties). -/
theorem cartanEilenberg_cone_filtration_properties
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
    (haug : ∀ n : ℤ, aug.f n = (a.f n).f 0 ≫
      (HomologicalComplex.extendXIso
        (((𝟭 A).mapHomologicalComplex (ComplexShape.up ℕ)).obj (I.X n))
        ComplexShape.embeddingUpNat (i := 0) (i' := 0) rfl).inv ≫
      (((CartanEilenbergPresentation.mappedFunctor (𝟭 A)).obj I).flip).ιTotal
        (ComplexShape.up ℤ) 0 n n (zero_add n))
    (F : DecreasingFiltration (CochainComplex.mappingCone aug))
    (hF : ∀ p n : ℤ, F.complexStep p n =
        (if p ≤ n + 1 then imageSubobject
          ((CochainComplex.mappingCone.inl aug).v (n + 1) n (by omega)) else ⊥) ⊔
        (Finset.Icc (max b p) n).sup (fun s ↦ imageSubobject
          ((((CartanEilenbergPresentation.mappedFunctor (𝟭 A)).obj I).flip).ιTotalOrZero
            (ComplexShape.up ℤ) (n - s) s n ≫
              (CochainComplex.mappingCone.inr aug).f n))) :
    (∀ n : ℤ, F.complexStep b n = ⊤ ∧ F.complexStep (n + 2) n = ⊥) ∧
      ∀ p n : ℤ, Nonempty ((F.gradedPiece p).homology n ≅
        (CochainComplex.mappingCone
          (HomologicalComplex.extendMap (a.f p) ComplexShape.embeddingUpNat)).homology
            (n - p)) := by
  sorry


end CategoryTheory.Functor
