/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Integral
import Sheaf.AlgebraicGeometry.FiniteSurjectiveAffineTarget
import Sheaf.AlgebraicGeometry.IsSeparatedOfSurjectiveUniversallyClosed
import WeilConjectures.AlgebraicGeometry.Morphisms.Integral.FinitePresentationApproximation

/-! # Affine target of a surjective universally closed morphism

Source: literature/stacks-project/limits.tex, Limits, Proposition 05YU
(label proposition-affine) (blueprint: lem-weil-pbc-surjective-universally-closed-affine-target).
-/

@[expose] public section

universe u

open CategoryTheory
namespace AlgebraicGeometry

/-- A scheme receiving a surjective universally closed morphism from an affine scheme is affine.
Source: Stacks Project, Limits, Proposition 05YU (label proposition-affine).
The parenthetical integral case follows from `IsIntegralHom.instUniversallyClosed`.
(blueprint: lem-weil-pbc-surjective-universally-closed-affine-target).

Proof (Stacks 05YU):
1. The affine source is separated: its structure morphism to Spec Z is affine and hence
   separated (`pqf-def-affine-morphism`, `lem-weil-pbc-affine-morphism-permanence`).
2. Descend separatedness to the target over Spec Z, using surjectivity and universal
   closedness (`lem-weil-pbc-morphism-into-affine-scheme`,
   `lem-weil-pbc-surjective-universally-closed-separated`, Stacks 09MQ).
3. A morphism from an affine source to a separated target is affine
   (`lem-weil-pbc-affine-source-separated-target-affine-morphism`, Stacks 01SG).
   An affine universally closed morphism is integral (`pqf-lem-integral-univclosed`, 01WM).
4. The source is quasi-compact and its surjective continuous image is quasi-compact;
   the separated target is quasi-separated (`lem-weil-pbc-qcqs-over-affine`,
   `lem-weil-pbc-closed-immersion-integral-separated-uc`,
   `lem-weil-pbc-affine-morphism-permanence`, `def-weil-pbc-scheme-conventions`).
5. Approximate the integral morphism over this qcqs target by finite, finitely presented
   morphisms with affine transitions (`lem-weil-pbc-integral-morphism-limit-of-finite`,
   Stacks 09YZ, `def-weil-finite-integral-morphism`).
6. The stages are qcqs by `lem-weil-pbc-qcqs-morphism-permanence` and affineness of finite
   morphisms. Since their limit is affine, some stage is affine
   (`lem-weil-pbc-limit-affine-stage`, Stacks 01Z6).
7. The map from that stage to the target is surjective: the original surjective map factors
   through it, so every target point is the image of a stage point
   (`def-weil-surjective-morphism`).
8. Apply Chevalley's theorem to this finite surjective morphism with affine source
   (`lem-weil-pbc-finite-surjective-affine-target`, Stacks 01ZT). For the integral case,
   use that integral morphisms are universally closed (`pqf-lem-integral-univclosed`).
-/
theorem isAffine_of_surjective_of_universallyClosed {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsAffine X] [Surjective f] [UniversallyClosed f] : IsAffine Y := by
  sorry

end AlgebraicGeometry
