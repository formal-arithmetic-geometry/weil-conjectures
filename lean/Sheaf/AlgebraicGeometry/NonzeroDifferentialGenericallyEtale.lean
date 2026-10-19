/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q131
-/
module

public import WeilConjectures.AlgebraicGeometry.Curve.SmoothProjective
public import WeilConjectures.AlgebraicGeometry.Modules.Differentials
public import WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.RingTheory.Kaehler.Basic

import WeilConjectures.AlgebraicGeometry.FunctionField
import Sheaf.RingTheory.FiniteTypeDomainDimensionTrdeg
import WeilConjectures.AlgebraicGeometry.TensorPullbackTilde
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.Algebra.Module.LocalizedModule.Exact
import Sheaf.RingTheory.DimensionAtPointLocalRingTrdeg
import Sheaf.AlgebraicGeometry.UnramifiedAlgebraOverFieldProduct
import WeilConjectures.AlgebraicGeometry.Regular
import Sheaf.AlgebraicGeometry.Curve.NonconstantNormalCurveMapFlat
import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
import Sheaf.AlgebraicGeometry.UnramifiedMorphism

/-!
# Nonzero differential and generic etaleness of smooth curves

Source: Stacks Project, `curves.tex`, Tag 0C1C, `lemma-generically-etale`,
equivalence of (1) and (4) (blueprint: lem-a1-nonzero-differential-generically-etale).

The helper constructs the canonical differential using the universal derivation and the
normalized tensor-pullback adjunction. The only postponed assertion is the curve criterion.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- The differential `h^* Ω_{Y/S} ⟶ Ω_{X/S}` of a morphism over `S`.
Source: Stacks Project, Tag 0C1C, condition (1), and Tag 01UM
(blueprint: lem-a1-nonzero-differential-generically-etale).

First use the universal derivation to form `Ω_{Y/S} ⟶ h_* Ω_{X/S}`: on sections it sends
`da` to `d(h.app a)`, by `pushforwardDerivation_desc_app_d`. Transport along the triangle
identity and take its adjoint under the tensor-pullback adjunction whose unit is
`m ↦ 1 ⊗ m`. This is the specified canonical map, with actual data throughout. -/
noncomputable def Scheme.Hom.cotangentMap
    {X Y S : Scheme.{u}} (h : X ⟶ Y) (pX : X ⟶ S) (pY : Y ⟶ S)
    (w : h ≫ pY = pX) :
    (Scheme.Modules.tensorPullback h).obj pY.relativeDifferentials ⟶
      pX.relativeDifferentials :=
  ((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction h)).homEquiv
    pY.relativeDifferentials pX.relativeDifferentials).symm
    ((pY.relativeDifferentialsHomEquiv _).symm (pY.pushforwardDerivation h) ≫
      (Scheme.Modules.pushforward h).map ((h ≫ pY).relativeDifferentialsCongr w).hom)

/-- A morphism of smooth integral curves has nonzero differential exactly when it is etale
on a nonempty source open.
Source: Stacks Project, `curves.tex`, Tag 0C1C, `lemma-generically-etale`, (1) iff (4)
(blueprint: lem-a1-nonzero-differential-generically-etale).

Proof:
1. All nonempty affine opens of each integral curve have dimension one: their fraction
   fields are the generic stalk (`def-sc-function-field`), and dimension equals transcendence
   degree (`lem-weil-pbc-finite-type-domain-dimension-trdeg`). Smoothness consequently has
   relative dimension one. By `lem-sc-smooth-omega-finite-locally-free` both differential
   sheaves, and by tensor pullback also the source of `dh`, are locally free of rank one.
2. The morphism is locally of finite presentation. In affine charts, present the source
   algebra over the field by finitely many generators and relations. Over the target algebra
   add the finitely many relations equating its generators with their images. Principal
   localization preserves finite presentation. Thus the morphism is locally of finite type.
3. The first exact sequence of Kahler differentials on affine charts gives
   `h^* Ω_{Y/k} → Ω_{X/k} → Ω_{X/Y} → 0`. The tensor-pullback tilde comparison identifies its
   first map with the helper above. Localization of differentials and exactness of module
   localization identify the restricted sequences and their stalks.
4. If `dh` is nonzero, trivialize the two line bundles. The map is multiplication by a
   nonzero regular function on some nonempty integral affine chart; it becomes invertible
   on its nonempty principal open. There the relative differential sheaf vanishes, hence
   the locally finite type restriction is unramified (`def-weil-unramified-morphism`).
5. This restriction is nonconstant. A singleton generic image would embed the target's
   function field of transcendence degree one into a closed point's algebraic residue field,
   contrary to `lem-weil-pbc-dimension-at-point-local-ring-trdeg`. A singleton closed image
   factors through its residue field because the source is reduced. The source affine
   algebra would then be unramified over that field, hence a product of finite separable
   fields (`lem-weil-pbc-unramified-algebra-over-field-product`), contradicting dimension one.
6. The target is normal by `lem-sc-smooth-normal`. Automatic flatness of a nonconstant map
   of integral curves into a normal curve (`lem-a1-nonconstant-normal-curve-map-flat`) makes
   the restriction flat. Together with Steps 2 and 4 this makes it etale.
7. Conversely, on a nonempty etale open the relative differentials vanish. Step 3 makes
   the restricted differential surjective onto a line bundle. At a point of this open, its
   rank-one stalk over a nonzero local ring is nonzero. A zero map cannot surject onto it.
   Therefore the original differential is nonzero.
-/
theorem Scheme.Hom.cotangentMap_ne_zero_iff_exists_etale_open
    {k : Type u} [Field k] {X Y : Scheme.{u}}
    (pX : X ⟶ Spec (.of k)) (pY : Y ⟶ Spec (.of k))
    [IsIntegralCurve pX] [IsIntegralCurve pY] [Smooth pX] [Smooth pY]
    (h : X ⟶ Y) (w : h ≫ pY = pX) :
    h.cotangentMap pX pY w ≠ 0 ↔
      ∃ V : X.Opens, (V : Set X).Nonempty ∧ Etale (V.ι ≫ h) := by
  sorry

end AlgebraicGeometry
