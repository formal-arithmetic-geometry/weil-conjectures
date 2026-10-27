/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q119
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceBlowupPresentation
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentIdeal
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceArtinRees
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

import Sheaf.AlgebraicGeometry.AlgebraicSpaceModulePullbackQuasiCoherent
import Sheaf.AlgebraicGeometry.AlgebraicSpaceAffineChartCalculus
import Sheaf.AlgebraicGeometry.SpaceChartTensorRealization
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
import WeilConjectures.Blowup.BlowupUniversal
import Sheaf.AlgebraicGeometry.AlgebraicSpaceBlowupUniversalProperty

/-! # Product-ideal comparison for algebraic-space blowups

Source: Stacks Project, Spaces Divisors, Tag 085Y, lemma-blowing-up-two-ideals
(blueprint: lem-sfb-space-blowup-product-ideal-comparison).

The extended ideal is the image of the canonical tensor map. The product ideal is
specified by the existing sieve-local ideal-product sections, which are the sections
of the sheaf image of tensor multiplication. Existentially naming these two uniquely
determined subobjects avoids any assumption that global sections preserve images.
Blowups use the existing affine-etale-chart presentations of the descended Rees Proj.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

/-- Blowing up I and then the extended ideal H gives the blowup of the product I H,
by the unique isomorphism over the original space. The two existential ideals name
exactly the canonical image and the locally generated product; they are not free
choices. The assertion applies to every presentation of the two resulting blowups.
Source: Stacks Project, Spaces Divisors, Tag 085Y, lemma-blowing-up-two-ideals
(blueprint: lem-sfb-space-blowup-product-ideal-comparison).

Proof:
1. Pullback preserves quasi-coherence by lem-sfb-space-module-pullback-quasicoherent.
   Images and tensors are computed on affine charts by
   lem-sfb-space-qcoh-affine-chart-calculus. The image of a finite generating family
   generates H1, and the pairwise products of finite generating families generate L.
   These give the named quasi-coherent image H1 and product L. The local formula
   a tensor (b tensor m) maps to a k^sharp(b) tensor m of
   lem-trf-space-chart-adjunction-tensor-realization identifies iterated extensions
   with extension along the composite, and extension of products with products of
   extensions. Write p = B.projection, q = C.projection and f = q followed by p.
2. The extended I on B is Cartier by lem-sfb-space-blowup-chart-properties. On each
   affine etale chart of B, its extension to C stays Cartier by
   lemma-nagata-cartier-total-transform-blowup. These charts cover C by
   lem-trf-space-fibre-products-etale-covers. The extended H on C is the exceptional
   ideal of q, so it too is Cartier by lem-sfb-space-blowup-chart-properties.
3. Locally write these ideals as (a), (d) for regular elements. Their product (ad)
   is regular, since adx = 0 implies dx = 0 and then x = 0. Thus L extended to C
   is Cartier. The universal property lem-sfb-space-blowup-universal-property gives
   the unique map e from C to D over the original space.
4. Conversely L extended to D is Cartier. By lemma-nagata-invertible-product-factor
   on affine etale charts, both its factors I and H extended to D are Cartier.
   The same universal property first gives r from D to B, and then d from D to C,
   since H1 extended along r is H extended along D.projection.
5. Uniqueness for D.projection gives d followed by e equal to the identity on D.
   Uniqueness for p makes e followed by r equal to q. Uniqueness for q then makes
   e followed by d equal to the identity on C. These maps give an isomorphism. The
   same unique-lift clause makes every isomorphism over the base equal to this one,
   proving canonicity.
   No quasi-compactness, quasi-separatedness, reducedness or density is used. -/
theorem existsUnique_blowupPresentation_product_iso
    {S : Scheme.{u}} (T : AlgebraicSpace S)
    (I H : QuasiCoherentIdeal T)
    (hI : (I.val : T.Modules).IsFiniteType) (hH : (H.val : T.Modules).IsFiniteType)
    (B : BlowupPresentation I) :
    ∃ (H₁ : QuasiCoherentIdeal B.space) (L : QuasiCoherentIdeal T),
      (∃ a : (moduleTensorPullback B.projection).obj (H.val : T.Modules) ⟶
          (H₁.val : B.space.Modules),
        a ≫ H₁.val.arrow = idealTensorMap B.projection H ∧
          PresheafOfModules.IsLocallySurjective B.space.etaleTopology a.val) ∧
      (∀ V : T.EtaleSite,
        Set.range (L.val.arrow.val.app (op V)) =
          idealPowerSubsheafSections I.val.arrow (SheafOfModules.unit T.structureSheaf)
            (fun W ↦ Set.range (H.val.arrow.val.app (op W))) 1 V) ∧
      ∀ (C : BlowupPresentation H₁) (D : BlowupPresentation L),
        ∃! e : C.space ≅ D.space,
          e.hom ≫ D.projection = C.projection ≫ B.projection := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
