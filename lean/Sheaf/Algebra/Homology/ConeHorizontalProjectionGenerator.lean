module

public import Sheaf.Algebra.Homology.ConeHorizontalProjection
public import Sheaf.Algebra.Homology.ConeHorizontalStepStable

/-! # Generator calculation for the signed column projection

Source: Stacks Project, Homology, Tag 012X, Lemma 12.25.1(1), with the
explicit column-cone refinement of lem-sp-cone-horizontal-graded-iso.
(blueprint: lem-sp-cone-horizontal-projection-generator-vanishing)
-/

@[expose] public section

universe v u
open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject
namespace HomologicalComplex₂
variable {C : Type u} [Category.{v} C] [Abelian C]
variable [∀ L : HomologicalComplex₂ C (ComplexShape.up ℕ)
  (ComplexShape.up ℕ), L.HasTotal (ComplexShape.up ℕ)]

/-- The differential defect of the signed column projection vanishes on each
source and target generator with horizontal index at least `p`.
Source: Stacks Project, Homology, Tag 012X, Lemma 12.25.1(1); the cone refinement
is the elementary sign calculation of lem-sp-cone-horizontal-graded-iso, step 2.
(blueprint: lem-sp-cone-horizontal-projection-generator-vanishing)

Proof: write `e = (-1)^p`. A valid summand of total degree `m` and horizontal
index `h` has vertical degree `m-h`. The total differential sends it to the
sum of the horizontal term in column `h+1` and `(-1)^h` times the vertical
term in column `h`. Total maps preserve `h`. The projection is zero on every
column except `p`, so if `h>p` all terms on both sides vanish. If `h=p`,
the horizontal term vanishes and the vertical coefficient is `e`.
Use the source/target biproduct decomposition of each cone. On column `p`,
the total-map cone differential has blocks `-e*d_A`, `f`, and `e*d_B`.
The column cone shifted by `-p` has blocks `-e*d_A`, `e*f`, and `e*d_B`.
The projection has source block `e` and target block `1`. On a source
summand, applying the projection before the shifted differential therefore
has source block `-e^2*d_A` and target block `e^2*f`; applying the total-map
cone differential before the projection has blocks `-e^2*d_A` and `f`.
These agree because `e^2=1`. On a target summand both composites are
`e*d_B`. Their difference is consequently zero on both kinds of generator.
All identifications here are the canonical degree-equality isomorphisms
appearing in `horizontalExtendedProjection` and `coneHorizontalProjection`.
If `m<0`, the extended summand inclusion is zero. If `m>=0` but `h>m`,
`ιTotalOrZero` is zero since `h + (m.toNat-h) != m.toNat`. This covers invalid
summands. At `n=p-1`, only the source generator in vertical degree zero
can survive; the same source-block calculation applies. Below `n=p-1`,
both generators with `h>=p` vanish. Thus the argument covers every integer
degree, including the extension-by-zero boundary. -/
theorem coneHorizontal_projection_generator_vanishing
    {A B : HomologicalComplex₂ C (ComplexShape.up ℕ) (ComplexShape.up ℕ)}
    (f : A ⟶ B) (p : ℕ) (n : ℤ) :
    (∀ h : ℕ, p ≤ h →
      (coneHorizontalSummand A h (n + 1) ≫
        HomologicalComplex.homotopyCofiber.inlX
          (HomologicalComplex.extendMap (total.map f (ComplexShape.up ℕ))
            ComplexShape.embeddingUpNat) (n + 1) n rfl) ≫
        (coneHorizontalProjection f p n ≫
          ((CochainComplex.mappingCone
            (HomologicalComplex.extendMap (f.f p)
              ComplexShape.embeddingUpNat))⟦-(p : ℤ)⟧).d n (n + 1) -
          (CochainComplex.mappingCone
            (HomologicalComplex.extendMap (total.map f (ComplexShape.up ℕ))
              ComplexShape.embeddingUpNat)).d n (n + 1) ≫
            coneHorizontalProjection f p (n + 1)) = 0) ∧
    (∀ h : ℕ, p ≤ h →
      (coneHorizontalSummand B h n ≫
        (CochainComplex.mappingCone.inr
          (HomologicalComplex.extendMap (total.map f (ComplexShape.up ℕ))
            ComplexShape.embeddingUpNat)).f n) ≫
        (coneHorizontalProjection f p n ≫
          ((CochainComplex.mappingCone
            (HomologicalComplex.extendMap (f.f p)
              ComplexShape.embeddingUpNat))⟦-(p : ℤ)⟧).d n (n + 1) -
          (CochainComplex.mappingCone
            (HomologicalComplex.extendMap (total.map f (ComplexShape.up ℕ))
              ComplexShape.embeddingUpNat)).d n (n + 1) ≫
            coneHorizontalProjection f p (n + 1)) = 0) := by
  sorry

end HomologicalComplex₂
