/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A7
-/
module

public import Sheaf.Paper.SmoothPurityCoordinateFoundations

/-! # Ordered projection adjunction models

Source: blueprint latest, sec-smooth-purity/sk-prop-sp-tower-geometric,
`sk-prop-sp-tower-geometric-gluing.proof.md`, Local pairs and Levels
(blueprint: lem-sp-coordinate-projection-models).

All levels n denote exponent n+1. The full subcategories below have uniform bounds,
without normalization. Every arrow belongs to an ordinary derived tower category.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOfSpec false
set_option genCtorIdx false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe u v v' w w' z z'
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures

namespace AlgebraicGeometry.ProEtale.SpCoordinateAdjunction

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- Only the ordered projection adjunctions and their finite evaluations. No
étale chart adjunction is included. Source: Local pairs and Levels.
(blueprint: lem-sp-coordinate-projection-models). -/
structure ProjectionModels (k : Type u) [Field k] (b : SpTowerShriek.Base l E)
    (o : SpTowerShriek.Operations l E b) (q : SpTowerCalculus.Coordinates l E b)
    (z : SpTowerCalculus.FiniteCoordinates l E)
    (h : SpTowerCalculus.Preservation l E k b o q)
    (cal : SpTowerCalculus.Calculus l E k b o q z h) (w : TwistFamily l E)
    (a : Foundations l E k b o q w) where
  projection : ∀ (Y : Bases k) (d : ℕ) (c : Compactification (proj Y.val.left d)),
    ProjectionPair l E b o q (proj Y.val.left d) c (w (space Y.val.left d)) d
  _affine_hom : ∀ (Y : Bases k)
    (M : (P l E b q (space Y.val.left 1)).FullSubcategory)
    (K : (P l E b q Y.val.left).FullSubcategory)
    (f : (SpTowerCalculus.F l E b o q (affineTraceLineCompactification Y.val.left)).obj
      M.obj ⟶ K.obj),
    realizedTranspose l E b q
      (projectionRight l E b o (proj Y.val.left 1) (w (space Y.val.left 1)) 1)
      M.obj K.obj ((projection Y 1 (affineTraceLineCompactification Y.val.left)).homEquiv
        M K f) =
      openHom l E b o Y.val.left
        ((SpTowerCalculus.realization l E b (space Y.val.left 1)
          (q.abelian (space Y.val.left 1))).functor.obj M.obj)
        (((a.projective Y).presentation.G l E).obj
          ((SpTowerCalculus.realization l E b Y.val.left (q.abelian Y.val.left)).functor.obj
            K.obj))
        (projectiveHom l E (a.projective Y)
          ⟨_, a.affine_source Y M⟩ ⟨_, a.affine_target Y K⟩
          ((projectivePush l E (a.projective Y)).hom.app _ ≫
            (supportRealization l E b o q (affineTraceLineCompactification Y.val.left)).inv.app
              M.obj ≫
            (SpTowerCalculus.realization l E b Y.val.left (q.abelian Y.val.left)).functor.map f)) ≫
      (a.affine Y).comparison.hom.app
        ((SpTowerCalculus.realization l E b Y.val.left (q.abelian Y.val.left)).functor.obj K.obj)
  _projection_successor : ∀ (Y : Bases k) (d : ℕ)
    (cl : Compactification
      (AffineSpace PUnit.{u + 1} (space Y.val.left d) ↘ space Y.val.left d))
    (cp : Compactification (proj Y.val.left d))
    (cc : Compactification (proj Y.val.left (d + 1))),
    CompositeEquation (P l E b q (space Y.val.left (d + 1)))
      (P l E b q (space Y.val.left d)) (P l E b q Y.val.left)
      _ _ _ _ _ _
      (projection (coordinateBase Y d) 1 cl) (projection Y d cp)
      (projection Y (d + 1) cc)
      (cal.composition.composition
        (AffineSpace PUnit.{u + 1} (space Y.val.left d) ↘ space Y.val.left d)
        (proj Y.val.left d) (proj Y.val.left (d + 1)) rfl cl cp cc)
      (composeRight l E b q _ _ _ (a.step Y d))
  _zero : ∀ (Y : Bases k) (c : Compactification (𝟙 Y.val.left))
    (M : (P l E b q Y.val.left).FullSubcategory)
    (K : (P l E b q Y.val.left).FullSubcategory)
    (f : (SpTowerCalculus.F l E b o q c).obj M.obj ⟶ K.obj),
    (projection Y 0 c).homEquiv M K f ≫
      (SpTowerCalculus.realization l E b Y.val.left (q.abelian Y.val.left)).inverse.map
        ((Foundations.iteration l E a Y 0).inv.app
          ((SpTowerCalculus.realization l E b Y.val.left (q.abelian Y.val.left)).functor.obj
            K.obj)) ≫
      (SpTowerCalculus.realization l E b Y.val.left (q.abelian Y.val.left)).unitIso.inv.app
        K.obj = (cal.composition.identity c).inv.app M ≫ f
  projection_levels : ∀ (Y : Bases k) (d : ℕ)
    (c : Compactification (proj Y.val.left d)) (n : ℕ),
    LevelCompatibility l E b q (projection Y d c) n (SpTowerShriek.finiteF l E b c n)
      (finiteProjectionRight l E b (proj Y.val.left d) (w (space Y.val.left d)) d n)
  _projection_left_normalization : ∀ (Y : Bases k) (d : ℕ)
    (c : Compactification (proj Y.val.left d)) (n : ℕ),
    (projection_levels Y d c n).left = supportEvaluation l E b o q c n
  _projection_right_normalization : ∀ (Y : Bases k) (d : ℕ)
    (c : Compactification (proj Y.val.left d)) (n : ℕ)
    (K : spDerivedCoefficientTowers l E Y.val.left (q.abelian Y.val.left)),
    (projection_levels Y d c n).right.hom.app K =
      projectionEvaluation l E b o q (proj Y.val.left d) (w (space Y.val.left d)) d n K

/-- Ordered projection adjunctions, with the fixed projective/open Hom formula,
zero-dimensional identity, successor counit and finite evaluation normalization.
Source: latest blueprint Local pairs and Levels; original coordinate steps 2, 5, 7.
(blueprint: lem-sp-coordinate-projection-models).

Proof. Restrict the projective-line Hom equivalence to the admissible domains in a.
Compose it with extension-by-zero/inverse-image adjunction and the normalized affine
right comparison. Transport compact support by its specified realization and
compactification comparison. This is the displayed affine Hom formula. Start the
ordered induction at the identity adjunction, transported through a.zero and the
compact-support identity comparison. At the successor, compose the preceding
projection pair with the affine-line pair at the coordinate base. Transport the
left composite by cal.composition.composition and the right by a.step. The counit
formula for composition is precisely CompositeEquation, including the inverse
left comparison. Compactification refinement transports the construction to every
specified compactification and coherence makes the formula independent of the
intermediate choices. Repeat these constructions on all finite constructible
finite-Tor objects, using the finite projective/open formulas, not only objects
which lift to towers. Evaluate the actual compositions: the fixed support and
right evaluation comparisons commute with the Hom equivalences. This proves both
transpose formulas and, by transposing identities, unit and counit compatibility.
No faithfulness of derived evaluation is used. -/
theorem coordinate_projection_models
    (pchar : ℕ) [Fact pchar.Prime] (k : Type u) [Field k] [CharP k pchar]
    (_hl : l ≠ pchar) (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
    (q : SpTowerCalculus.Coordinates l E b) (z : SpTowerCalculus.FiniteCoordinates l E)
    (h : SpTowerCalculus.Preservation l E k b o q)
    (cal : SpTowerCalculus.Calculus l E k b o q z h) (w : TwistFamily l E)
    (a : Foundations l E k b o q w) :
    Nonempty (ProjectionModels l E k b o q z h cal w a) := by sorry

end AlgebraicGeometry.ProEtale.SpCoordinateAdjunction
