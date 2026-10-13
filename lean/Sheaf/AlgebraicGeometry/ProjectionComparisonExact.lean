/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U4
-/
module

public import Sheaf.AlgebraicGeometry.DerivedTensorStructure
public import Sheaf.AlgebraicGeometry.DerivedPullback
public import Sheaf.AlgebraicGeometry.SchemeDerivedDirectImage
public import Mathlib.CategoryTheory.Triangulated.Functor
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Noetherian

/-! # Exactness of the canonical projection comparison

Source: Stacks Project, Tag 08EU, proof, and Cohomology, equation (20.54.2.1).
(blueprint: lem-sc-projection-comparison-exact).
-/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace AlgebraicGeometry

/-- The projection mate, natural in its ambient derived-category argument.
Source: Stacks Project, Cohomology, equation (20.54.2.1).
(blueprint: lem-sc-projection-comparison-exact). -/
noncomputable def projectionComparisonNatTrans
    {Z Y : Scheme.{u}} (f : Z ⟶ Y)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [Functor.Monoidal (derivedPullback f)]
    (a : derivedPullback f ⊣ schemeDerivedDirectImage f)
    (E : schemeDerivedCategory Z) :
    tensorRight ((schemeDerivedDirectImage f).obj E) ⟶
      (derivedPullback f ⋙ tensorRight E) ⋙ schemeDerivedDirectImage f where
  app K := (a.homEquiv _ _)
    ((Functor.Monoidal.μIso (derivedPullback f) K
      ((schemeDerivedDirectImage f).obj E)).inv ≫
        (derivedPullback f).obj K ◁ a.counit.app E)
  naturality {K L} g := by
    apply a.homEquiv_naturality_left_square
    dsimp
    simp only [Functor.Monoidal.μIso_inv]
    rw [← Functor.OplaxMonoidal.δ_natural_left_assoc, Category.assoc,
      whisker_exchange]

/-- The two tensor/direct-image composites are exact and their canonical projection mate
commutes with shifts for compatible exact shift structures.
Source: Stacks Project, Tag 08EU, proof (exactness of the functors involved), and
Cohomology, equation (20.54.2.1).
(blueprint: lem-sc-projection-comparison-exact).

Proof: represent derived tensor and pullback by K-flat complexes and direct image by
K-injective resolutions. Tensoring with a K-flat complex sends mapping cones to mapping
cones; direct image on K-injectives and derived pullback likewise preserve cone triangles.
The tensor shift isomorphisms on these representatives, with their Koszul signs, give
exact shift structures on the source and target composite functors. To handle the supplied
strong monoidal structure on pullback, transport its shift comparison along the inverse
tensorator and the identification K[n] = K tensor the shifted unit. The tensorator's
associativity and unit identities identify this transported comparison with the one on
K-flat representatives, up to conjugation by natural isomorphisms; hence exactness is
preserved. Tensorator naturality and counit naturality show that the mate commutes with
these comparisons: transpose the square under the adjunction, expand the inverse
tensorator followed by the whiskered counit, and use associativity and unit coherence.
The zero-shift and addition coherence follow from the same identities. Descend from
representatives by the localization universal property. This proves exactness of both
specified functors and shift compatibility of the already constructed natural
transformation, without any invertibility assumption on its components. -/
theorem projectionComparison_exact
    {Z Y : Scheme.{u}} [IsNoetherian Z] [IsNoetherian Y] (f : Z ⟶ Y) [IsProper f]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [Functor.Monoidal (derivedPullback f)]
    (a : derivedPullback f ⊣ schemeDerivedDirectImage f)
    (E : schemeDerivedQCohCategory Z) :
    ∃ (s : (tensorRight ((schemeDerivedDirectImage f).obj E.obj)).CommShift ℤ)
      (t : ((derivedPullback f ⋙ tensorRight E.obj) ⋙
        schemeDerivedDirectImage f).CommShift ℤ),
      letI := s
      letI := t
      (tensorRight ((schemeDerivedDirectImage f).obj E.obj)).IsTriangulated ∧
      ((derivedPullback f ⋙ tensorRight E.obj) ⋙
        schemeDerivedDirectImage f).IsTriangulated ∧
      NatTrans.CommShift (projectionComparisonNatTrans f a E.obj) ℤ := by sorry

end AlgebraicGeometry
