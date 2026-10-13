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
import Sheaf.AlgebraicGeometry.DerivedPullbackTensorShift
import WeilConjectures.CategoryTheory.Adjunction.ProjectionMapShift
import Mathlib.CategoryTheory.Triangulated.Adjunction

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

Proof: choose compatible exact shifts for derived pullback and tensor from
`derivedPullback_tensorShift`. Give direct image the right-adjoint shift induced by
`a`; the adjunction then commutes with shifts. Since pullback is triangulated,
Mathlib's right-adjoint exactness theorem makes direct image triangulated. Exactness
of tensor and the composition instances give the two required exact functors.
Flip the oplax tensorator natural transformation to match tensorRight. Its shift
compatibility is one clause of the tensor-shift theorem, and naturality of the tensor
shifts in the fixed factor gives compatibility for tensoring the counit. Identify
`projectionComparisonNatTrans` componentwise with `a.rightAdjointProjectionMap`
for this flipped tensorator. The upstream projection-map shift theorem now proves
the required shift equation. No projection component is cancelled or assumed
invertible. The geometric tensor/pullback shift construction remains a separate
statement; the adjunction, direct-image exactness and mate argument are proved here. -/
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
      NatTrans.CommShift (projectionComparisonNatTrans f a E.obj) ℤ := by
  obtain ⟨sF, sY, sZ, hF, hY, hZ, hmap, hδ⟩ := derivedPullback_tensorShift f
  let : (derivedPullback f).CommShift ℤ := sF
  let : (derivedPullback f).IsTriangulated := hF
  let := sY
  let := sZ
  let (M : schemeDerivedCategory Y) : (tensorRight M).IsTriangulated := hY M
  let (M : schemeDerivedCategory Z) : (tensorRight M).IsTriangulated := hZ M
  let := a.rightAdjointCommShift ℤ
  have : a.CommShift ℤ := a.commShift_of_leftAdjoint ℤ
  have : (schemeDerivedDirectImage f).IsTriangulated := a.isTriangulated_rightAdjoint
  let φ : (Functor.postcompose₂.obj (derivedPullback f)).obj
      (curriedTensor (schemeDerivedCategory Y)).flip ⟶
      (((Functor.whiskeringLeft₂ (schemeDerivedCategory Z)).obj
        (derivedPullback f)).obj (derivedPullback f)).obj
          (curriedTensor (schemeDerivedCategory Z)).flip :=
    Functor.flipping.functor.map (Functor.OplaxMonoidal.δNatTrans (derivedPullback f))
  have : NatTrans.CommShift
      (F₁ := tensorRight ((schemeDerivedDirectImage f).obj E.obj) ⋙ derivedPullback f)
      (F₂ := derivedPullback f ⋙ tensorRight
        ((derivedPullback f).obj ((schemeDerivedDirectImage f).obj E.obj)))
      (φ.app ((schemeDerivedDirectImage f).obj E.obj)) ℤ := hδ _
  have : NatTrans.CommShift
      ((curriedTensor (schemeDerivedCategory Z)).flip.map (a.counit.app E.obj)) ℤ :=
    hmap _
  refine ⟨inferInstance, inferInstance, inferInstance, inferInstance, ?_⟩
  have hη : projectionComparisonNatTrans f a E.obj =
      (a.rightAdjointProjectionMap φ).app E.obj := by
    ext K
    simp only [projectionComparisonNatTrans, Adjunction.rightAdjointProjectionMap_app_app,
      Functor.Monoidal.μIso_inv]
    rfl
  rw [hη]
  exact a.commShift_rightAdjointProjectionMap_app φ E.obj

end AlgebraicGeometry
