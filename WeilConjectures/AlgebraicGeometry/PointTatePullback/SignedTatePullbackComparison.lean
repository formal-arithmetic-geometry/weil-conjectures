/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.StrictWeilCondensed.StrictWeilCondensed
public import WeilConjectures.AlgebraicGeometry.PurityTransport.TransportLinePull

/-! # Canonical signed Tate pullback comparison

Source: latest blueprint, part-duality-trace-formula/sec-poincare-duality/
sec-global-duality-and-the-poincare-pairing/sk-thm-derived-duality/
prop-pod-degree-of-the-pairing.proof.md, final sentence: pull back the point twist;
sk-prop-sfb-cartesian-coefficients, clause (1), supplies its canonical comparisons.
(blueprint: def-pod-signed-tate-pullback-comparison).

The normalized constructions use the native `StrictWeilCondensed.presentationLine`.
Their namespace is separate from the unchanged Fourier theorem module.
`coordinates` retains the root, scalar, unit and ordered tensor normalizations;
`negativeComparison` is evaluation followed by the unit and inverse positive map;
`comparison` combines these branches for every integer. No invertibility theorem
or Frobenius compatibility assertion is part of this definition node.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory MonoidalClosed
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.PointTatePullback

open CondensedRing PurityTransport

/-- The existing root-normalized coordinates, including their projection, scalar
and tensor normalization equations. No root frame is chosen.
Source: canonical twist pullback in prop-pod-degree-of-the-pairing.proof.md,
final sentence, and sk-prop-sfb-cartesian-coefficients (1)
(blueprint: def-pod-signed-tate-pullback-comparison). -/
def coordinates (ell : ℕ) [Fact ell.Prime] (c : Coefficient ell)
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (ell : X.residueField x)]
    [∀ y : Y, Invertible (ell : Y.residueField y)] : LinePullCoordinates ell c f :=
  Classical.choice (linePullCoordinates_nonempty ell c f)

/-- Evaluation-transpose comparison followed by the coefficient-unit map and the
contravariant image of the inverse positive comparison. This is the same composite
as signed dual pullback, without presupposing invertibility
of the internal-Hom comparison for an arbitrary scheme morphism.
Source: signed dual pullback in sk-prop-sfb-cartesian-coefficients (1), used in
prop-pod-degree-of-the-pairing.proof.md, final sentence
(blueprint: def-pod-signed-tate-pullback-comparison). -/
def negativeComparison (ell : ℕ) [Fact ell.Prime] (c : Coefficient ell)
    {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ)
    (e : (CondensedRing.upperStar (c.obj ell) f).obj (c.line ell Y (n + 1)) ≅
      c.line ell X (n + 1)) :
    (CondensedRing.upperStar (c.obj ell) f).obj
        (StrictWeilCondensed.presentationLine ell c Y (.negSucc n)) ⟶
      StrictWeilCondensed.presentationLine ell c X (.negSucc n) := by
  let F := CondensedRing.upperStar (c.obj ell) f
  let L := c.line ell Y (n + 1)
  let M := c.line ell X (n + 1)
  let a : F.obj ((ihom L).obj (𝟙_ _)) ⟶ (ihom (F.obj L)).obj (F.obj (𝟙_ _)) :=
    (Functor.LaxMonoidal.ihomComparison F L).natTrans.app (𝟙_ _)
  let b : (ihom (F.obj L)).obj (F.obj (𝟙_ _)) ⟶ (ihom (F.obj L)).obj (𝟙_ _) :=
    (ihom (F.obj L)).map (Functor.Monoidal.εIso F).inv
  let d : (ihom (F.obj L)).obj (𝟙_ _) ⟶ (ihom M).obj (𝟙_ _) :=
    ((MonoidalClosed.internalHom.mapIso e.symm.op).app (𝟙_ _)).hom
  exact a ≫ b ≫ d

/-- Canonical signed comparison on the existing Tate lines. Nonnegative powers
are the normalized power coordinates, whose normalization includes the unit and
monoidal recursion; the negative branch is the evaluation inverse transpose.
Source: canonical twist pullback in prop-pod-degree-of-the-pairing.proof.md,
final sentence, and sk-prop-sfb-cartesian-coefficients (1)
(blueprint: def-pod-signed-tate-pullback-comparison). -/
def comparison (ell : ℕ) [Fact ell.Prime] (c : Coefficient ell)
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (ell : X.residueField x)]
    [∀ y : Y, Invertible (ell : Y.residueField y)] :
    (m : ℤ) → (CondensedRing.upperStar (c.obj ell) f).obj
        (StrictWeilCondensed.presentationLine ell c Y m) ⟶
      StrictWeilCondensed.presentationLine ell c X m
  | .ofNat n => ((coordinates ell c f).power n).hom
  | .negSucc n => negativeComparison ell c f n ((coordinates ell c f).power (n + 1))

end AlgebraicGeometry.ProEtale.PointTatePullback
