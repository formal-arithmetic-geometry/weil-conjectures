/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group ND
-/
module

public import Sheaf.Paper.SmoothPurityTowerGammaData

/-! # Normalization of the compact-support and exceptional outputs

Source: latest blueprint tower-geometric gamma proof (3).
(blueprint: lem-sp-tower-normalization-preservation).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option genInjectivity false
set_option genSizeOfSpec false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry.Scheme WeilConjectures
namespace AlgebraicGeometry.ProEtale.SpTowerGamma
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
  (q : SpTowerCalculus.Coordinates l E b)


/-- Both actual adjoints preserve normalized objects in the uniform tower category.
The claim concerns only the quotient transitions; it asserts no tower orientation,
no isomorphism of whole towers, and no naturality of gamma.
Source: latest blueprint tower-geometric gamma proof (3)
(blueprint: lem-sp-tower-normalization-preservation).

Proof: CompactSupportTowerReduction identifies each actual compact-support reduction,
up to the specified evaluation isomorphisms, with the direct-image coefficient
comparison followed by compact support of the input reduction. ReductionDirectImage
makes the former invertible on the finite constructible finite-Tor input; the latter
is invertible on a normalized input because a functor preserves inverses. Cancel the
evaluation comparisons. ScalarCoordinates identifies this reduction with the original
abelian-tower reduction through an isomorphism, proving support normalization.
For exceptional output use PurityConjugatesTowerReduction at each pair m <= n.
Its pullback reduction square is scalar/pullback balancing, input reduction and
positive Tate-line reduction, with the even shift. The Tate reduction is invertible
without flatness of the quotient because the line is locally free. Thus this source
reduction is invertible on normalized input. The displayed exceptional conjugacy
expresses the output reduction as this source reduction conjugated by the finite
purity isomorphisms. All three factors are invertible. Cancel the scalar-coordinate
isomorphism to obtain the original reduction. Equal indices use the scalar unitor,
and d=0 uses the coefficient unit, so these edge cases are included. Membership in
the uniform category is supplied by hF and by the codomain of G. -/
theorem tower_normalization_preservation (D : FiniteFieldDatum.{u}) [CharP D.k D.p] (hne : l ≠ D.p)
    {X Z Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [IsSeparated (Y ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    (j : X ⟶ Z) [IsOpenImmersion j] (p : Z ⟶ Y) [IsProper p]
    [(j ≫ p).IsOver (Spec (.of D.k))]
    [QuasiCompact (j ≫ p)] [HasCompactification (j ≫ p)]
    (d : ℕ) [SmoothOfRelativeDimension d (j ≫ p)]
    (w : SpChartAdmissibility.Twists l E X)
    (hF : ∀ M : SpTowerCalculus.C l E b q X,
      spConstructibleTorTowers l E Y (q.abelian Y)
        ((SpTowerCalculus.F l E b o q (factorization j p)).obj M.obj))
    (G : SpTowerCalculus.C l E b q Y ⥤ SpTowerCalculus.C l E b q X)
    (adj : SpTowerGluing.support l E b o q (factorization j p) hF ⊣ G)
    (lv : SpTowerGluing.Levels l E b o q (factorization j p) hF G adj) 
    (roots : SpCoordinateAdjunction.RootLines l E X)
    (unitsX : ∀ n : ℕ, IsUnit ((l ^ (n + 1) : ℕ) : Γ(X, ⊤)))
    (cc : ∀ n : ℕ,
      letI : Finite (SpTowerShriek.R l E n) := b.finite n
      SpTowerP1.CoefficientCoordinates l E n X (unitsX n))
    (tc : ∀ n : ℕ,
      letI : Finite (SpTowerShriek.R l E n) := b.finite n
      SpTowerP1.TensorCoordinates l E n b X)
    (gc : ∀ n : ℕ,
      letI : Finite (SpTowerShriek.R l E n) := b.finite n
      SpTowerP1.GeometricCoordinates l E n (j ≫ p)) :
    (∀ M : SpTowerCalculus.C l E b q X,
      IsSpNormalizedTower l E X (q.abelian X) M.obj →
        IsSpNormalizedTower l E Y (q.abelian Y)
          ((SpTowerGluing.support l E b o q (factorization j p) hF).obj M).obj) ∧
    (∀ K : SpTowerCalculus.C l E b q Y,
      IsSpNormalizedTower l E Y (q.abelian Y) K.obj →
        IsSpNormalizedTower l E X (q.abelian X) (G.obj K).obj) := by
  sorry

end AlgebraicGeometry.ProEtale.SpTowerGamma

attribute [instance high] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
