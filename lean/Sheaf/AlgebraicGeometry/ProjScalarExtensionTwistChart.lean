/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K7
-/
module

public import Sheaf.AlgebraicGeometry.ProjScalarExtensionTwistData
import Sheaf.AlgebraicGeometry.ProjScalarExtensionTwistChartBasic
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor
import Sheaf.RingTheory.HomogeneousLocalizationScalarExtension
import Sheaf.Algebra.Module.GradedLocalizationScalarExtension
import WeilConjectures.AlgebraicGeometry.ModulePullbackAffineSections
import WeilConjectures.AlgebraicGeometry.ProjGradedModuleSheafExists
import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde
import WeilConjectures.AlgebraicGeometry.ProjTwistBasicOpenFractions

/-! # The scalar-extension twist map on a single standard chart

Source: Stacks Project, constructions.tex, Tags 01MY and 01N2.
(blueprint: lem-sfb-proj-scalar-extension-twist-chart). -/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory TopologicalSpace
open AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Proj

/-- A morphism with the prescribed pointwise fraction formula is bijective on every
open inside a scalar-extended standard chart, for one fixed integer twist.

Source: Stacks Project, constructions.tex, Tag 01N2, clause (3), proof on standard
opens; Tag 01MY, the map on localized graded modules.

Proof: Let H = (A_f)_0 and L = (A_f)_j. The graded-module sheaf construction, applied
to the degree shift A(j), identifies the restriction of the concrete locally-fraction
sheaf twist A j to D_+(f) with the quasi-coherent sheaf associated to L. Indeed both
have the same homogeneous fractions on standard subopens, with the same restrictions;
the basis-extension uniqueness in the graded-module sheaf theorem identifies them.
The analogous construction identifies twist B j on D_+(psi f) with the sheaf of
(B_(psi f))_j. The affine pullback-sections theorem identifies the pullback of the
first sheaf with the sheaf associated to L tensor_H (B_(psi f))_0.

The homogeneous-localization scalar-extension equivalence identifies the last
coefficient ring with S tensor_R H. Tensor associativity and the balancing relations
give L tensor_H (S tensor_R H) = S tensor_R L, sending u tensor (s tensor h) to
s tensor h*u, with inverse s tensor u mapped to u tensor (s tensor 1). The
homogeneous-module localization scalar-extension equivalence, followed by beta on
fractions, identifies S tensor_R L with (B_(psi f))_j. These equivalences send
(a/f^m) tensor c to c*psi(a)/psi(f)^m. The grading compatibility of beta follows
from hgraded and hbeta: beta maps the span of the tensors s tensor a, a in A_n,
onto B_n. No flatness is used, since homogeneous pieces are direct summands before
localization and the comparison is an equivalence on each such piece.

The hypothesis on eta gives exactly this formula on pullbacks of chart sections.
These sections, multiplied by coefficients, generate the pullback chart module;
linearity therefore identifies eta with the displayed equivalence on chart sections.
The affine tilde--sections adjunction identifies the restriction of eta with its
associated sheaf isomorphism. Every further restriction is an isomorphism as well,
so its map on sections over any W contained in the chart is bijective. Empty charts
and empty W give the unique map between zero section modules, and negative j uses
the same shifted graded-module localization, without an invertibility assumption.
(blueprint: lem-sfb-proj-scalar-extension-twist-chart). -/
theorem scalarExtension_twistMap_basicOpen_bijective
    {R S A B : Type u} [CommRing R] [CommRing S] [CommRing A] [CommRing B]
    [Algebra R S] [Algebra R A] [Algebra S B]
    (𝒜 : ℕ → Submodule R A) (ℬ : ℕ → Submodule S B)
    [GradedRing 𝒜] [GradedRing ℬ]
    (β : TensorProduct R S A ≃ₐ[S] B) (ψ : 𝒜 →+*ᵍ ℬ)
    (hβψ : ∀ a : A, β (TensorProduct.tmul R (1 : S) a) = ψ a)
    (hgraded : ∀ n : ℕ, ℬ n = Submodule.span S (ψ '' (𝒜 n : Set A)))
    (hψ : HomogeneousIdeal.irrelevant ℬ ≤ HomogeneousIdeal.map ψ (HomogeneousIdeal.irrelevant 𝒜))
    (j : ℤ)
    (η : (tensorPullback (map ψ hψ)).obj (twist 𝒜 j) ⟶ twist ℬ j)
    (hη : ∀ (U : (Proj 𝒜).Opens) (s : Γ(twist 𝒜 j, U))
      (x : map ψ hψ ⁻¹ᵁ U),
      ((η.app (map ψ hψ ⁻¹ᵁ U)
        (tensorPullbackSection (map ψ hψ) (twist 𝒜 j) U s)).1 x :
          Localization.AtPrime x.1.asHomogeneousIdeal.toIdeal) =
        Localization.localRingHom _ _ ψ.toRingHom rfl (s.1 ⟨_, x.2⟩).val)
    (n : ℕ) (f : A) (hf : f ∈ 𝒜 n) (hn : 0 < n)
    (W : (Proj ℬ).Opens) (hW : W ≤ basicOpen ℬ (ψ f)) :
    Function.Bijective (η.app W) := by sorry

end AlgebraicGeometry.Proj
