/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.VectorBundleThomMaps

/-! # The prescribed direct-sum Thom product

Source: blueprint main-20261015, sec-smooth-purity/sk-prop-an,
`thm-pur-vector-bundle-thom` (blueprint: def-pur-vector-bundle-thom-sum-product).

The isomorphism concerns `vectorBundleThomTau`, not an unspecified identification
of its source and target. Base change uses the normalized proper/open exchange;
direct sums use the forward relative compact-support product. The trace is its inverse.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Opposite AlgebraicGeometry
open scoped CategoryTheory.Functor

namespace WeilConjectures.PurityFiniteSetting

variable {P : PurityFiniteSetting.{u}}

variable {B : Scheme.{u}} {hB : B ⟶ Spec (.of P.field.k)}
  [IsSeparated hB] [LocallyOfFiniteType hB] [QuasiCompact hB] {r : ℕ}

section DirectSum

variable {s : ℕ} (V : PurityVectorBundle P B hB (r + s))
  (V₁ : PurityVectorBundle P B hB r) (V₂ : PurityVectorBundle P B hB s)
  (e : V.𝓔 ≅ V₁.𝓔 ⨯ V₂.𝓔)

/-- The common Hom presentation for the prescribed sum-bundle forward product.
Source: blueprint Step 5 (blueprint: def-pur-vector-bundle-thom-sum-product). -/
abbrev VectorBundleThomSumProductHom :=
    ((ProEtale.derivedTensor (ModuleCat.{u + 1} P.Coefficient) B).obj
      ((ProEtale.rightDerivedLowerShriek (ModuleCat.{u + 1} P.Coefficient) V₁.p).obj
        (vectorBundleThomInput P V₁.E r))).obj
      ((ProEtale.rightDerivedLowerShriek (ModuleCat.{u + 1} P.Coefficient) V₂.p).obj
        (vectorBundleThomInput P V₂.E s)) ⟶
      (ProEtale.rightDerivedLowerShriek (ModuleCat.{u + 1} P.Coefficient) V.p).obj
        (vectorBundleThomInput P V.E (r + s))

/-- The full native forward product fixes this presentation uniquely.
Source: blueprint Steps 5--7 (blueprint: def-pur-vector-bundle-thom-sum-product). -/
structure VectorBundleThomSumProductSpec (f : VectorBundleThomSumProductHom V V₁ V₂) : Prop where
  /-- Normalization by every arrow of the prescribed forward construction.
  Source: blueprint Steps 5--7 (blueprint: def-pur-vector-bundle-thom-sum-product). -/
  normalized :
    letI : Finite P.Coefficient := ProEtale.finiteForwardCoefficient P
    letI : QuasiCompact (vectorBundleThomProjection₂ V V₁ V₂ e) :=
      (vectorBundleThomSum_geometry V V₁ V₂ e).2.1
    letI : HasCompactification (vectorBundleThomProjection₂ V V₁ V₂ e) :=
      (vectorBundleThomSum_geometry V V₁ V₂ e).2.2
    letI : HasCompactification (vectorBundleThomProjection₂ V V₁ V₂ e ≫ V₂.p) :=
      vectorBundleThomSum_composite_compactifiable V V₁ V₂ e
    ∃ (hMN : _) (μ : _),
        HEq μ (vectorBundleThomSumCoefficient V V₁ V₂ e) ∧
          HEq f (vectorBundleThomProductGeneric P.Coefficient
            (vectorBundleThomSum_geometry V V₁ V₂ e).1
            (vectorBundleThomSum_projection_comp V V₁ V₂ e)
            (vectorBundleThomInput P V₁.E r) (vectorBundleThomInput P V₂.E s)
            (vectorBundleThomInput P V.E (r + s)) hMN μ)

/-- The specified six-arrow product has one presentation on the Thom inputs.
Source: blueprint Steps 5--7 (blueprint: def-pur-vector-bundle-thom-sum-product).
Proof: the native tensor and localization objects are the same ones in the published
Thom inputs. Transport the full generic composite through these presentation identities.
This supplies existence; heterogeneous equality to that fixed composite gives uniqueness. -/
theorem existsUnique_vectorBundleThomSumProduct :
    ∃! f : VectorBundleThomSumProductHom V V₁ V₂,
      VectorBundleThomSumProductSpec V V₁ V₂ e f := by
  sorry

/-- The canonical relative product, including the normalized coefficient multiplication.
Source: blueprint Steps 5--7 (blueprint: def-pur-vector-bundle-thom-sum-product). -/
def vectorBundleThomSumProduct : VectorBundleThomSumProductHom V V₁ V₂ :=
  (existsUnique_vectorBundleThomSumProduct V V₁ V₂ e).exists.choose

end DirectSum

end WeilConjectures.PurityFiniteSetting
