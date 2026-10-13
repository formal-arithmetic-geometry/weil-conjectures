/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.GlobalHomAdjunctionIso

/-! # Internal Hom exchange with the canonical base-change mate
Source: Stacks Project, duality.tex, Tag 0AA8, lemma-more-base-change,
final comparison diagrams; cohomology.tex, Tag 08I3.
(blueprint: lem-sc-internal-hom-base-change-exchange).
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
universe u w
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
noncomputable section
namespace AlgebraicGeometry
variable [∀ Z : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
variable [∀ (R : Type u) [Ring R], HasDerivedCategory.{w} (ModuleCat.{u} R)]

/-- The exchange identity before applying global sections.
Here `p` is the pullback of evaluation transposed by the fixed tensor-Hom bijection.
Source: Stacks Project, duality.tex, Tag 0AA8, lemma-more-base-change,
final comparison diagrams; cohomology.tex, Tag 08I3.
(blueprint: lem-sc-internal-hom-base-change-exchange).

Proof: transpose both sides by the tensor-Hom bijection on Y'. Naturality in the
first Hom input replaces precomposition by beta_M with tensoring by beta_M;
naturality in the second input replaces postcomposition by beta_N with beta_N.
Use the evaluation-mate equation for the direct-image comparisons, and the
construction of p as pulled-back evaluation. Transpose beta under the f'
adjunction: it is the pullback-composition comparison followed by the pullback
of the f counit. Naturality of that counit and the f' triangle identity cancel
the unit-counit pairs. The remaining tensor comparisons agree: on K-flat
representatives both are the ordinary tensor-pullback comparison along the
commutative square, and uniqueness of the left-derived comparison extends
this equality to all objects. Thus both transposed composites agree, and
injectivity of the tensor-Hom bijection gives the equation. -/
theorem schemeInternalHom_baseChange_exchange
    {X Y Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y)
    (M N : schemeDerivedCategory X) :
  let p := fun {S T : Scheme.{u}} (h : T ⟶ S) (P Q : schemeDerivedCategory S) ↦
    ((schemeDerivedTensorHomEquiv T)
      ((derivedPullback h).obj
        ((derivedInternalHom (Opens.grothendieckTopology S) S.sheaf).obj (op P, Q)))
      ((derivedPullback h).obj P) ((derivedPullback h).obj Q)).symm
        ((schemeHomTensorPullbackIso h).inv.app
          ((derivedInternalHom (Opens.grothendieckTopology S) S.sheaf).obj (op P, Q), P) ≫
          (derivedPullback h).map
            ((schemeDerivedTensorHomEquiv S)
              ((derivedInternalHom (Opens.grothendieckTopology S) S.sheaf).obj (op P, Q))
              P Q (𝟙 _)))
  let H := fun Z : Scheme.{u} ↦ derivedInternalHom (Opens.grothendieckTopology Z) Z.sheaf
  let c := fun {S T : Scheme.{u}} (h : T ⟶ S) ↦
    Classical.choose (exists_schemeHomDirectImageComparison h)
  schemeDerivedBaseChangeMap f (pullback.snd f g) g (pullback.fst f g)
      pullback.condition ((H X).obj (op M, N)) ≫
    (schemeDerivedDirectImage (pullback.snd f g)).map (p (pullback.fst f g) M N) ≫
    (c (pullback.snd f g)).app
      (op ((derivedPullback (pullback.fst f g)).obj M),
        (derivedPullback (pullback.fst f g)).obj N) ≫
    (H Y').map
      (X := (op ((schemeDerivedDirectImage (pullback.snd f g)).obj
        ((derivedPullback (pullback.fst f g)).obj M)),
        (schemeDerivedDirectImage (pullback.snd f g)).obj
          ((derivedPullback (pullback.fst f g)).obj N)))
      (Y := (op ((derivedPullback g).obj ((schemeDerivedDirectImage f).obj M)),
        (schemeDerivedDirectImage (pullback.snd f g)).obj
          ((derivedPullback (pullback.fst f g)).obj N)))
      ((schemeDerivedBaseChangeMap f (pullback.snd f g) g
        (pullback.fst f g) pullback.condition M).op, 𝟙 _) =
    (derivedPullback g).map ((c f).app (op M, N)) ≫
      p g ((schemeDerivedDirectImage f).obj M) ((schemeDerivedDirectImage f).obj N) ≫
      (H Y').map
        ((𝟙 _).op, schemeDerivedBaseChangeMap f (pullback.snd f g) g
          (pullback.fst f g) pullback.condition N) := by sorry

end AlgebraicGeometry
