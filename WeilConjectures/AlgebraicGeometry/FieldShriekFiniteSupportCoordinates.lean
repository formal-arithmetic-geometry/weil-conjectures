/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FieldShriekSupportEvaluation
public import WeilConjectures.AlgebraicGeometry.SmoothPurityTowerShriekLevels
public import WeilConjectures.SecSmoothPurity.ReductionDirectImageComparison

/-!
# Identity finite support coordinates

Source: latest blueprint, sec-smooth-purity/sk-lem-sp-field-extension/
`sk-lem-sp-field-extension-towers.proof.md` (2), the finite proper-image
coordinates (blueprint: lem-route-field-shriek-finite-support-coordinates).

The constant-ring proper pushforward is definitionally the ringed-site direct
image with the canonical constant-ring comparison.  Thus its finite support
coordinates are the identity natural isomorphism, whose section equation is
literal equality.  The support evaluation then is the tower comparison
followed by the right-derived identity, whiskered after finite open extension.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures

namespace AlgebraicGeometry.ProEtale.FieldShriekSystem

variable (P : PurityFiniteSetting.{u})

/-- Identity finite support coordinates exist at every coefficient level.

Source: latest blueprint, sec-smooth-purity/sk-lem-sp-field-extension/
`sk-lem-sp-field-extension-towers.proof.md` (2), first sentence: the finite
compact-support coordinates of the level-n comparison of b
(blueprint: lem-route-field-shriek-finite-support-coordinates).

Proof.
1. By def-sp-reduction-direct-image-comparison, `proEtaleConstantRingPushforward R c.g`
   is the module direct image of def-weil-pbc-proetale-operations along `c.g` with the
   canonical constant-ring comparison; it is an abbrev for exactly the target of
   `FiniteCoordinates.push`.  Take `push := Iso.refl _`.  Its component at every module
   `M` and every object `U` of `Y_proet` is the identity of `(c.g_* M)(U)`, so every
   section goes to itself and the `HEq` field `sections` holds by reflexivity.
2. By def-sp-field-shriek-support-evaluation, `supportEvaluation P D E c n z` is
   `Fcomparison` (the level comparison of det-sp-tower-shriek-levels (1) for the
   operations of `D` at `E`) followed by `rightDerivedFunctorNatIso z.push` whiskered
   after the finite open extension.  Substituting `z.push = Iso.refl _` gives the
   displayed composite; `rightDerivedFunctorNatIso (Iso.refl _)` is the identity of
   `Rp_{*,R}`, and whiskering keeps it an identity. -/
theorem exists_finite_support_coordinates
    (E : Index P) (D : Models P)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) (n : ℕ) :
    ∃ z : FiniteCoordinates P E c n,
      z.push = Iso.refl _ ∧
        supportEvaluation P D E c n z =
          SpTowerShriek.Fcomparison P.coefficients.l E.val (D.base E)
              (D.operations E) c n ≪≫
            Functor.isoWhiskerLeft _
              (Functor.isoWhiskerLeft _
                (Functor.rightDerivedFunctorNatIso (Iso.refl _))) := by
  let z : FiniteCoordinates P E c n :=
    { push := Iso.refl _
      sections := by
        intro M U x
        rfl }
  refine ⟨z, ?_, ?_⟩
  · rfl
  · rfl

end AlgebraicGeometry.ProEtale.FieldShriekSystem
