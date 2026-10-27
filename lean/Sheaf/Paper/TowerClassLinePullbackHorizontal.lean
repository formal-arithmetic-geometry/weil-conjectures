/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H5
-/
module

public import Sheaf.Paper.TowerClassPullback

/-! # Horizontal compatibility of the finite root-line comparisons

Source: current classes blueprint, clause (2), scalar extension of the root tower.
(blueprint: lem-sfb-tower-class-line-pullback-horizontal).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory CategoryTheory.Limits Opposite WeilConjectures
open AlgebraicGeometry.Scheme
namespace AlgebraicGeometry.ProEtale.SpTowerClasses

attribute [local irreducible] lineModule
  Scheme.proEtaleConstantRingComparison Scheme.proEtaleRingDirectImageMap

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The finite coefficient/root formula respects horizontal tower restrictions.

Source: current blueprint `sk-prop-sp-tower-geometric-classes.proof.md`, clause (2),
scalar extension of the root tower, and the transition calculation in the proof of
`lem-sfb-tower-class-line-pullback-existence`.
(blueprint: lem-sfb-tower-class-line-pullback-horizontal).

Proof: evaluate the scalar-extension sheafification unit at levels m and n.
Naturality of that unit sends a tensor a tensor z along the horizontal arrow to
coefficientMap(h)(a) tensor z^(l^(m-n)). The rootForget transition equation identifies
this root power with the horizontal restriction of c.rootModule, so the uniquely
normalized lineEvaluation comparisons carry the actual system transition to this
formula. The same argument applies on X and Y. The ordinaryPullTransition equation
of g.generic, transported by g.coefficients, g.transitions and the ordinary
comparison equalities of g, identifies the source transition with inverse image
of the Y transition followed by the identity on underlying sheaves restriction
comparison. Transpose the resulting square using the level adjunctions. Test its
two morphisms on local pure tensors before sheafification. The given normalization
of delta reduces the coefficient factors to the same section: naturality of the
constant direct-image map with respect to the quotient-ring map is precisely
this equality. The root factors agree because the global-sections ring map of the
base-change projection preserves powers. Consequently both paths send a tensor
a tensor z to the restricted coefficientMap(h)(a) tensor the restricted
z^(l^(m-n)). Tensor induction and the sheafification universal property prove
equality of morphisms, including on the empty chart. Cancel the lineEvaluation
isomorphisms and the ordinary pull evaluation isomorphisms to get the displayed
square. Only horizontal compatibility is asserted here: the finite isomorphisms,
their construction, their assembly and the tower adjoint formula are separate.
-/
theorem linePullback_components_horizontal
    {b : SpTowerShriek.Base l E} {X Y : Scheme.{u}} (f : X ⟶ Y)
    (g : SpTowerShriek.Geometry l E b f) (cY : Chern l E Y) (cX : Chern l E X)
    (δ : ∀ n : ℕ,
      (proEtaleConstantRingPullback (SpTowerShriek.R l E n) f).obj
        (finiteLine l E Y n) ≅ finiteLine l E X n)
    (hδ : ∀ (n : ℕ) (U : Y.ProEtᵒᵖ)
      (a : (SpTowerShriek.B l E Y n).obj.obj U)
      (z : (Scheme.proEtaleRootsOfUnitySheaf Y (l ^ (n + 1))).obj.obj U),
      (((proEtaleConstantRingAdjunction (SpTowerShriek.R l E n) f).homEquiv _ _)
        (δ n).hom).val.app U
          (Scheme.tateFiniteTensor Y l (FiniteRing l E n) n (finiteScalar l E n)
            U.unop a z) =
        Scheme.tateFiniteTensor X l (FiniteRing l E n) n (finiteScalar l E n)
          (chart f U).unop
          ((Scheme.proEtaleConstantDirectImageMap.{u, u + 2} f CommRingCat.{u + 1}
            (CommRingCat.of (FiniteRing l E n))).hom.app U a)
          (restrictRoot l f n U z)) :
    let d := fun n ↦ (g.ordinaryPullEvaluation n).app (lineModule l E cY) ≪≫
      (proEtaleConstantRingPullback (SpTowerShriek.R l E n) f).mapIso
        (lineEvaluation l E cY n) ≪≫ δ n ≪≫ (lineEvaluation l E cX n).symm
    ∀ {m n : ℕ} (h : n ≤ m),
      (SemilinearSections.transition.{u + 1, u, u + 1}
        (Scheme.ProEt.topology X) (SpTowerShriek.B l E X) (SpTowerShriek.tau l E X) h).app
          (g.pull.obj (lineModule l E cY)) ≫
        (SemilinearSections.res.{u + 1, u, u + 1}
          (SemilinearSections.coefficientMap.{u + 1, u, u + 1}
            (Scheme.ProEt.topology X) (SpTowerShriek.B l E X)
            (SpTowerShriek.tau l E X) h)).map (d n).hom =
      (d m).hom ≫ (SemilinearSections.transition.{u + 1, u, u + 1}
        (Scheme.ProEt.topology X) (SpTowerShriek.B l E X) (SpTowerShriek.tau l E X) h).app
          (lineModule l E cX) := by sorry

end AlgebraicGeometry.ProEtale.SpTowerClasses
