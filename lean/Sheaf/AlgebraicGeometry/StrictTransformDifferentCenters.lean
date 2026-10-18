/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q143
-/
module

public import Sheaf.AlgebraicGeometry.ModuleStrictTransform
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Invertible
public import Mathlib.CategoryTheory.Subobject.Limits
import WeilConjectures.Blowup.AdmissibleBlowup
import WeilConjectures.Blowup.Affine.ChartAlgebra
import WeilConjectures.Blowup.Principalization
import WeilConjectures.Mathlib.Algebra.Module.Torsion
import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.EffectiveCartier
import Sheaf.AlgebraicGeometry.CoherentFiniteType
import Sheaf.AlgebraicGeometry.ModuleStrictTransformKernel
import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
import Sheaf.TraceFormula.StrictTransformAffineTorsionComparison
import WeilConjectures.Blowup.Affine.StrictTransformChart
import WeilConjectures.Blowup.FiniteDegree.Algebra

/-!
# Strict transforms for centres differing by an effective Cartier factor

Source: Stacks Project, Divisors, Tag 080H, clause (2)
(blueprint: lem-trf-strict-transform-different-centers).

The comparison is stated on the common ambient module on `X ×[S] I.blowup`.
The complement open for the product centre is transported through the specified
isomorphism `id_X ×[S] φ`. Restriction to this transported open defines the transported
kernel. Thus equality below is equality of subobjects of the same pullback of `F`,
including their inclusions, rather than an unspecified isomorphism of quotient modules.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.Modules

/-- The specified blowup isomorphism induces `id_X ×[S] φ`, with no choices of lifts.
Source: Stacks Project, Tag 080H (1), and the fibre-product universal property
(blueprint: lem-trf-strict-transform-different-centers). -/
noncomputable def moduleStrictTransformCenterIso {X S : Scheme.{u}} (f : X ⟶ S)
    (I D : S.IdealSheafData) (φ : (I * D).blowup ≅ I.blowup)
    (hφ : φ.hom ≫ I.blowupMap = (I * D).blowupMap) :
    Limits.pullback f (I * D).blowupMap ≅ Limits.pullback f I.blowupMap :=
  asIso (pullback.map f (I * D).blowupMap f I.blowupMap (𝟙 X) φ.hom (𝟙 S)
    ((Category.comp_id f).trans (Category.id_comp f).symm)
    ((Category.comp_id (I * D).blowupMap).trans hφ.symm))

/-- The product-centre complement transported onto the blowup ambient for `I`.
Since the comparison is an isomorphism, its image of the complement is the inverse image
under its inverse. Source: Stacks Project, Tag 080H (2), opening of its proof
(blueprint: lem-trf-strict-transform-different-centers). -/
noncomputable def moduleStrictTransformTransportedOpen {X S : Scheme.{u}} (f : X ⟶ S)
    (I D : S.IdealSheafData) (φ : (I * D).blowup ≅ I.blowup)
    (hφ : φ.hom ≫ I.blowupMap = (I * D).blowupMap) :
    (Limits.pullback f I.blowupMap).Opens :=
  (moduleStrictTransformCenterIso f I D φ hφ).inv ⁻¹ᵁ moduleStrictTransformOpen f (I * D)

/-- Restriction of the common ambient pullback to the transported product-centre open.
Its kernel is the transported kernel defining the module strict transform for `I * D`:
an isomorphism transports sections, their zero restrictions, and the projection to `X`.
Source: Stacks Project, Tags 080D (1) and 080H (2)
(blueprint: lem-trf-strict-transform-different-centers). -/
noncomputable def moduleStrictTransformTransportedRestriction {X S : Scheme.{u}}
    (f : X ⟶ S) (I D : S.IdealSheafData) (φ : (I * D).blowup ≅ I.blowup)
    (hφ : φ.hom ≫ I.blowupMap = (I * D).blowupMap) (F : X.Modules) :
    (tensorPullback (pullback.fst f I.blowupMap)).obj F ⟶
      (pushforward (moduleStrictTransformTransportedOpen f I D φ hφ).ι).obj
        ((restrictFunctor (moduleStrictTransformTransportedOpen f I D φ hφ).ι).obj
          ((tensorPullback (pullback.fst f I.blowupMap)).obj F)) :=
  (restrictAdjunction (moduleStrictTransformTransportedOpen f I D φ hφ).ι).unit.app
    ((tensorPullback (pullback.fst f I.blowupMap)).obj F)

/-- Multiplying the centre by an effective Cartier divisor leaves the strict-transform
quotient kernel unchanged, under the specified isomorphism of the ambient fibre products.
The hypothesis `hF` says precisely that restriction to `X \ f⁻¹(D)` is injective on every
open, or equivalently that `F` has no nonzero local sections supported on `f⁻¹(D)`.
`D.IsInvertible` is the affine-local nonzerodivisor definition of an effective Cartier ideal.
The kernel of each restriction map is also the kernel of its defining strict-transform
quotient, since that quotient is the cokernel of the kernel inclusion in an abelian category.

Source: Stacks Project, Divisors, Tag 080H (2)
(blueprint: lem-trf-strict-transform-different-centers).

Proof plan:
1. The effective Cartier ideal is invertible (lemma-nagata-effective-cartier-is-invertible).
The fixed blowup isomorphism of lemma-nagata-blowup-invertible-factor induces the displayed
ambient isomorphism over `X`. Transport the product-centre complement through it. The
kernels are the supported-section subsheaves for the inverse images of `Z` and `Z ∪ D`
(def-trf-module-strict-transform); they are quasi-coherent by
lem-trf-strict-transform-sheaf-kernel. The product centre is finite type because locally
its generators are the generators of `I` times the single generator of `D`.
2. Cover the base by affine opens where `D = (x)` with `x` a nonzerodivisor and `I` is
finitely generated. Cover the blowup by its standard charts `A[I/a]`
(prop-nagata-affine-blowup-chart-cover, def-nagata-blowup-chart-ring). After affine base
change (def-nagata-strict-transform-basechange-chart-ring), the pullback of `F = M~` is
`(M ⊗[A] A[I/a])~` (def-pc-module-pullback). The two kernels are the sheaves of `a`-power
and `xa`-power torsion, respectively (def-nagata-power-torsion): the centre ideals on the
chart are `(a)` and `(xa)`, and restriction to a principal open is localization.
3. The no-supported-sections hypothesis gives zero `x`-power torsion in `M`. Apply
lem-trf-strict-transform-affine-torsion-comparison to identify the two torsion submodules.
4. The charts cover the ambient fibre product (def-pc-fibre-product), so their kernel
equalities glue to the asserted equality of subobjects. -/
theorem moduleStrictTransform_kernel_eq_of_cartier_factor {X S : Scheme.{u}}
    (f : X ⟶ S) (I D : S.IdealSheafData) [I.toModules.IsFiniteType]
    (hD : D.IsInvertible) (φ : (I * D).blowup ≅ I.blowup)
    (hφ : φ.hom ≫ I.blowupMap = (I * D).blowupMap)
    (F : X.Modules) [F.IsQuasicoherent]
    (hF : Mono ((restrictAdjunction (f ⁻¹ᵁ D.support.compl).ι).unit.app F)) :
    kernelSubobject (moduleStrictTransformRestriction f I F) =
      kernelSubobject (moduleStrictTransformTransportedRestriction f I D φ hφ F) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
