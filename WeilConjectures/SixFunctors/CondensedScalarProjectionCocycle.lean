/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.CondensedProjectionScalarSquare
public import WeilConjectures.SixFunctors.ScalarDirectImageMateCoherence
public import WeilConjectures.SixFunctors.ScalarSixTensorHom
public import WeilConjectures.SixFunctors.ListedCoefficientMaps
public import WeilConjectures.SixFunctors.CondensedScalarProjectionCocycleData
import WeilConjectures.SixFunctors.CondensedScalarProjectionCocycleFirst
import WeilConjectures.SixFunctors.CondensedScalarProjectionCocycleLast
import WeilConjectures.SixFunctors.ListedCoefficientCtf

/-! # Cocycle for the condensed scalar projection comparisons

Source: latest blueprint, sec-six-functors/sk-rem-sf-pf-done/
fix-prop-projection-formula.proof.md, successive-reduction and scalar-extension
compatibility (blueprint: lem-sf-condensed-scalar-projection-cocycle).

The three boundary maps `condensedProjectionScalarSource`, `condensedProjectionScalarInner`
and `condensedProjectionScalarTarget` are defined in the publicly imported module
`WeilConjectures.SixFunctors.CondensedScalarProjectionCocycleData` (blueprint:
def-sf-condensed-scalar-projection-cocycle-data). They are the source, inner and target
boundary composites built from the existing tensor, pullback and compact-support maps.
The scalar tower is the canonical adjunction conjugate `scalarSixTower`. It is the
normalized beta of internal scalar mate transitivity.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Obj CategoryTheory.Functor
open scoped AlgebraicGeometry.ProEtale.CondensedRing.CachedModInstances

namespace AlgebraicGeometry.ProEtale.CondensedRing
set_option maxHeartbeats 10000000 in
-- The conjunction assembly unfolds large derived-category endpoints.
/-- Tensor, pullback, compact-support and direct-image cocycles, and equality of the
composite projection square with the pasted one. Composition is left to right.
The last four clauses identify both boundaries, state the pasted rectangle, and state
the direct composite square for the actual projection maps. The canonical tower
is beta: it is fixed by the scalar units, rather than chosen arbitrarily.

Source: latest blueprint `fix-prop-projection-formula.proof.md`, successive coefficient
compatibility (blueprint: lem-sf-condensed-scalar-projection-cocycle).

Proof: Apply condensedScalarProjectionCocycleFirst for the tensor, pullback and
compact-support cocycles, and scalarDirectImageMateCoherence for direct image.
Apply condensedScalarProjectionCocycleLast for the two endpoint boundary
cocycles. For the pasted rectangle, form the scalar extensions of K and L as
constructible finite-Tor objects using listedCoefficientCtf. Apply the scalar
projection square for b to those objects and paste with scalar extension by b
of the square for a. Functoriality and reassociation give the stated rectangle.
Finally apply condensedProjectionScalarSquare to the composite listed map. Since
the boundary definitions are the specified composites, unfolding them and
reassociating gives the final clause. -/
theorem condensedScalarProjectionCocycle
    (ell : ℕ) [Fact ell.Prime] (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ell)]
    (_hcd : AlgebraicGeometry.ProEtale.BaseFieldFiniteCD ell k)
    {Λ₀ Λ₁ Λ₂ : ScalarSixRing.{u}}
    (a : Λ₀ ⟶ Λ₁) (b : Λ₁ ⟶ Λ₂)
    (_ha : ListedCoefficientMap ell a) (_hb : ListedCoefficientMap ell b)
    {X Y : Over (Spec (.of k))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (f : X ⟶ Y) (c : Compactification f.left) :
    (∀ (Z : Over (Spec (.of k)))
      [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]
      (U V : ConstantModelConstructibleFiniteTor Λ₀.X Z.left),
      (scalarSixTower a b Z.left).hom.app (U.obj ⊗ V.obj) ≫
          (scalarSixTensorIso (a ≫ b) Z.left U.obj V.obj).hom =
        (scalarSixChange b Z.left).map ((scalarSixTensorIso a Z.left U.obj V.obj).hom) ≫
          (scalarSixTensorIso b Z.left
              ((scalarSixChange a Z.left).obj U.obj)
              ((scalarSixChange a Z.left).obj V.obj)).hom ≫
          ((scalarSixTower a b Z.left).hom.app U.obj ▷
              (scalarSixChange b Z.left).obj ((scalarSixChange a Z.left).obj V.obj)) ≫
          ((scalarSixChange (a ≫ b) Z.left).obj U.obj ◁
              (scalarSixTower a b Z.left).hom.app V.obj)) ∧
    (∀ L : ConstantModelConstructibleFiniteTor Λ₀.X Y.left,
      (scalarSixTower a b X.left).hom.app
            ((upperStar Λ₀.X f.left).leftDerivedFunctor.obj L.obj) ≫
          (condensedScalarPullbackIso (a ≫ b) f.left).hom.app L.obj =
        (scalarSixChange b X.left).map
            ((condensedScalarPullbackIso a f.left).hom.app L.obj) ≫
          (condensedScalarPullbackIso b f.left).hom.app
            ((scalarSixChange a Y.left).obj L.obj) ≫
          (upperStar Λ₂.X f.left).leftDerivedFunctor.map
            ((scalarSixTower a b Y.left).hom.app L.obj)) ∧
    (∀ K : ConstantModelConstructibleFiniteTor Λ₀.X X.left,
      (scalarSixTower a b Y.left).hom.app
            ((rightDerivedLowerShriekOfCompactification Λ₀.X c).obj K.obj) ≫
          (scalarCompactSupportMap (a ≫ b) c.i c.g).app K.obj =
        (scalarSixChange b Y.left).map ((scalarCompactSupportMap a c.i c.g).app K.obj) ≫
          (scalarCompactSupportMap b c.i c.g).app ((scalarSixChange a X.left).obj K.obj) ≫
          (rightDerivedLowerShriekOfCompactification Λ₂.X c).map
            ((scalarSixTower a b X.left).hom.app K.obj)) ∧
    (∀ M : DerivedCategory (ModuleRingedComparison.internalModules Λ₀.X c.Z),
      (scalarSixTower a b Y.left).hom.app ((RootCoordinateFace.lower Λ₀.X c.g).obj M) ≫
          (scalarDirectImageMate (a ≫ b) c.g).app M =
        (scalarSixChange b Y.left).map ((scalarDirectImageMate a c.g).app M) ≫
          (scalarDirectImageMate b c.g).app ((scalarSixChange a c.Z).obj M) ≫
          (RootCoordinateFace.lower Λ₂.X c.g).map
            ((scalarSixTower a b c.Z).hom.app M)) ∧
    (∀ (K : ConstantModelConstructibleFiniteTor Λ₀.X X.left)
      (L : ConstantModelConstructibleFiniteTor Λ₀.X Y.left),
      ((scalarSixTower a b Y.left).hom.app
            ((rightDerivedLowerShriekOfCompactification Λ₀.X c).obj K.obj ⊗ L.obj) ≫
          condensedProjectionScalarSource (a ≫ b) c K.obj L.obj =
        (scalarSixChange b Y.left).map (condensedProjectionScalarSource a c K.obj L.obj) ≫
          condensedProjectionScalarSource b c
            ((scalarSixChange a X.left).obj K.obj) ((scalarSixChange a Y.left).obj L.obj) ≫
          ((rightDerivedLowerShriekOfCompactification Λ₂.X c).map
                ((scalarSixTower a b X.left).hom.app K.obj) ▷
              (scalarSixChange b Y.left).obj ((scalarSixChange a Y.left).obj L.obj)) ≫
          ((rightDerivedLowerShriekOfCompactification Λ₂.X c).obj
                ((scalarSixChange (a ≫ b) X.left).obj K.obj) ◁
              (scalarSixTower a b Y.left).hom.app L.obj)) ∧
      ((scalarSixTower a b Y.left).hom.app
            ((rightDerivedLowerShriekOfCompactification Λ₀.X c).obj
              (K.obj ⊗ (upperStar Λ₀.X f.left).leftDerivedFunctor.obj L.obj)) ≫
          condensedProjectionScalarTarget (a ≫ b) c K.obj L.obj =
        (scalarSixChange b Y.left).map (condensedProjectionScalarTarget a c K.obj L.obj) ≫
          condensedProjectionScalarTarget b c
            ((scalarSixChange a X.left).obj K.obj) ((scalarSixChange a Y.left).obj L.obj) ≫
          (rightDerivedLowerShriekOfCompactification Λ₂.X c).map
            (((scalarSixTower a b X.left).hom.app K.obj ▷
                (upperStar Λ₂.X f.left).leftDerivedFunctor.obj
                  ((scalarSixChange b Y.left).obj ((scalarSixChange a Y.left).obj L.obj))) ≫
              ((scalarSixChange (a ≫ b) X.left).obj K.obj ◁
                (upperStar Λ₂.X f.left).leftDerivedFunctor.map
                  ((scalarSixTower a b Y.left).hom.app L.obj)))) ∧
      ((scalarSixChange b Y.left).map (condensedProjectionScalarSource a c K.obj L.obj) ≫
          condensedProjectionScalarSource b c
            ((scalarSixChange a X.left).obj K.obj) ((scalarSixChange a Y.left).obj L.obj) ≫
          exceptionalProjectionMorphismOfCompactification Λ₂.X c
            ((scalarSixChange b X.left).obj ((scalarSixChange a X.left).obj K.obj))
            ((scalarSixChange b Y.left).obj ((scalarSixChange a Y.left).obj L.obj)) =
        (scalarSixChange b Y.left).map
            ((scalarSixChange a Y.left).map
              (exceptionalProjectionMorphismOfCompactification Λ₀.X c K.obj L.obj)) ≫
          (scalarSixChange b Y.left).map (condensedProjectionScalarTarget a c K.obj L.obj) ≫
          condensedProjectionScalarTarget b c
            ((scalarSixChange a X.left).obj K.obj)
            ((scalarSixChange a Y.left).obj L.obj)) ∧
      (condensedProjectionScalarSource (a ≫ b) c K.obj L.obj ≫
          exceptionalProjectionMorphismOfCompactification Λ₂.X c
            ((scalarSixChange (a ≫ b) X.left).obj K.obj)
            ((scalarSixChange (a ≫ b) Y.left).obj L.obj) =
        (scalarSixChange (a ≫ b) Y.left).map
            (exceptionalProjectionMorphismOfCompactification Λ₀.X c K.obj L.obj) ≫
          condensedProjectionScalarTarget (a ≫ b) c K.obj L.obj)) := by
  classical
  rcases condensedScalarProjectionCocycleFirst ell k _hcd a b _ha _hb f c with
    ⟨h1, h2, h3⟩
  refine ⟨h1, h2, h3, ?_, ?_⟩
  · intro M
    exact (scalarDirectImageMateCoherence a c.g (𝟙 Y.left)).2.2.2.2 Λ₂ b M
  · intro K L
    rcases condensedScalarProjectionCocycleLast ell k _hcd a b _ha _hb f c K L with
      ⟨h5, h6⟩
    refine ⟨h5, h6, ?_, ?_⟩
    · let K' : ConstantModelConstructibleFiniteTor Λ₁.X X.left :=
        ⟨(scalarSixChange a X.left).obj K.obj,
          (listedCoefficientCtf ell a _ha).2.2 k X K.obj K.property⟩
      let L' : ConstantModelConstructibleFiniteTor Λ₁.X Y.left :=
        ⟨(scalarSixChange a Y.left).obj L.obj,
          (listedCoefficientCtf ell a _ha).2.2 k Y L.obj L.property⟩
      have ha : condensedProjectionScalarSource a c K.obj L.obj ≫
          exceptionalProjectionMorphismOfCompactification Λ₁.X c K'.obj L'.obj =
          (scalarSixChange a Y.left).map
              (exceptionalProjectionMorphismOfCompactification Λ₀.X c K.obj L.obj) ≫
            condensedProjectionScalarTarget a c K.obj L.obj := by
        simpa only [condensedProjectionScalarSource, condensedProjectionScalarTarget,
          condensedProjectionScalarInner, Category.assoc] using
          condensedProjectionScalarSquare ell k _hcd a _ha f c K L
      have hb : condensedProjectionScalarSource b c K'.obj L'.obj ≫
          exceptionalProjectionMorphismOfCompactification Λ₂.X c
            ((scalarSixChange b X.left).obj K'.obj) ((scalarSixChange b Y.left).obj L'.obj) =
          (scalarSixChange b Y.left).map
              (exceptionalProjectionMorphismOfCompactification Λ₁.X c K'.obj L'.obj) ≫
            condensedProjectionScalarTarget b c K'.obj L'.obj := by
        simpa only [condensedProjectionScalarSource, condensedProjectionScalarTarget,
          condensedProjectionScalarInner, Category.assoc] using
          condensedProjectionScalarSquare ell k _hcd b _hb f c K' L'
      rw [hb, ← Category.assoc, ← Functor.map_comp, ha,
        Functor.map_comp]
      simp only [Category.assoc, K', L']
    · simpa only [condensedProjectionScalarSource, condensedProjectionScalarTarget,
        condensedProjectionScalarInner, Category.assoc] using
        condensedProjectionScalarSquare ell k _hcd (a ≫ b)
          (ListedCoefficientMap.comp a b _ha _hb) f c K L

end AlgebraicGeometry.ProEtale.CondensedRing
