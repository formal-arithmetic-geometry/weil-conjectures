/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NB
-/
module

public import Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids
public import Sheaf.AlgebraicGeometry.OpenModuliSubstack
public import Sheaf.AlgebraicGeometry.ModuliChartNormalization
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.AlgebraicGeometry.Group.Affine
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.MvPowerSeries.Inverse
import WeilConjectures.RingTheory.PowerSeriesQuotientVariables
import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.RingTheory.Henselian
import Sheaf.AlgebraicGeometry.AlgebraicSpace
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
import Sheaf.AlgebraicGeometry.ChartwiseEtalePermanence
import Sheaf.AlgebraicGeometry.EtaleComparison
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import Sheaf.RingTheory.EtaleHenselianRingLift
import Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite
import Mathlib.RingTheory.MvPowerSeries.NoZeroDivisors
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.AlgebraicGeometry.OpenImmersion

/-! # Trait lifting through arbitrary étale charts and density

Source: Stacks Project, moduli-curves.tex, Tags 0E86 (lemma-smooth-dense) and
0E87 (lemma-smooth-dense-in-stable), with the prescribed-lift expansion using
algebra.tex, Tag 08HQ (lemma-map-into-henselian)
(blueprint: lem-sfb-trait-specialization-etale-chart-density).

The affine objects below are Mathlib's relative spectra. The two auxiliary maps
are constant-coefficient reduction and inversion of the power-series variable.
Scheme-valued maps to a stack use the recorded discrete-moduli convention.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v w

open AlgebraicGeometry CategoryTheory.Limits Opposite

namespace CategoryTheory

/-- The closed-point inclusion into the formal disc, over the original field.
This is the relative spectrum of constant-coefficient reduction, restricted from
an Ω-algebra homomorphism to a k-algebra homomorphism.
Source: Stacks, moduli-curves.tex, Tag 0E86
(blueprint: lem-sfb-trait-specialization-etale-chart-density). -/
def moduliTraitClosed (k Ω : Type u) [Field k] [Field Ω] [Algebra k Ω] :
    (algSpec (.of k)).obj (op (CommAlgCat.of k Ω)) ⟶
      (algSpec (.of k)).obj (op (CommAlgCat.of k (PowerSeries Ω))) :=
  (algSpec (.of k)).map (CommAlgCat.ofHom
    (AlgHom.restrictScalars k
      ({ toRingHom := PowerSeries.constantCoeff
         commutes' := PowerSeries.constantCoeff_C } : PowerSeries Ω →ₐ[Ω] Ω))).op

/-- The punctured formal disc, using exactly localization at the variable.
Source: Stacks, moduli-curves.tex, Tag 0E86
(blueprint: lem-sfb-trait-specialization-etale-chart-density). -/
def moduliTraitGeneric (k Ω : Type u) [Field k] [Field Ω] [Algebra k Ω] :
    (algSpec (.of k)).obj
        (op (CommAlgCat.of k (Localization.Away (PowerSeries.X : PowerSeries Ω)))) ⟶
      (algSpec (.of k)).obj (op (CommAlgCat.of k (PowerSeries Ω))) :=
  (algSpec (.of k)).map (CommAlgCat.ofHom
    (IsScalarTower.toAlgHom k (PowerSeries Ω)
      (Localization.Away (PowerSeries.X : PowerSeries Ω)))).op

/-- Smoothing traits lift through every representable étale scheme chart, preserving
the specified special-fibre isomorphism, and the pulled-back open is dense.
Source: Stacks, moduli-curves.tex, Tags 0E86 and 0E87; algebra.tex, Tag 08HQ
(blueprint: lem-sfb-trait-specialization-etale-chart-density).

Proof:
1. The power-series local-ring and quotient-variables lemmas identify the maximal
ideal of R = Ω[[t]] with (t) and its residue map with constant coefficient. The
variables-complete lemma and complete-pair-henselian lemma make R henselian local.
2. Form E = Spec R ×_F V. Representability and the DM étale-atlas calculus make
E an étale algebraic space over Spec R. The prescribed special isomorphism gives
a point e over Spec Ω. Pull back a scheme atlas W of E to e; fibre-products-etale-
covers makes this a nonempty étale Ω-scheme. The étale-comparison lemma and the
weakly-etale-algclosed-section lemma give a lift z of the actual point e. Chartwise
étale permanence makes W → Spec R étale.
3. Pointed-etale-neighbourhood-affine-shrink gives an affine Spec B around z.
For α : R → B and θ : B → Ω, θα is constant coefficient. Apply the henselian
ring-lift lemma with S = R and β = id to get f : B → R with fα = id and εf = θ.
The resulting section s of W → Spec R restricts to z.
4. Project the section through E to obtain the lift to V and its 2-isomorphism.
Its closed restriction is the original triple (i,v,φ). In the discrete groupoids
of schemes the two scheme components of an isomorphism are identities, so the
comma compatibility equation gives exactly the prescribed φ, not just some iso.
5. The power-series-domain lemma gives the prime (0). Every nonzero series is
t^n times a unit, by its least nonzero coefficient and the local-ring unit
criterion. Thus R[1/t] is the generic field, and (t) is a specialization of (0).
Continuity of the lifted scheme map puts the image of v in the closure of the
pulled-back open, since the generic restriction lies in U.
6. Every point y of V is the image of a geometric point over an algebraic closure
of κ(y), by the residue-field description of geometric points. Apply the assumed
trait existence and steps 1--5 to that point. All points lie in the closure;
the open-scheme representation comes from U.open_pullback. Empty V is included.
Neither surjectivity of the chart, smoothness of F, nor finite type is used. -/
theorem trait_specialization_etale_chart_density (k : Type u) [Field k]
    (F : BasedCategory.{v, w} (Over (Spec (.of k))))
    (hF : IsDeligneMumfordModuliStack F) (U : OpenModuliSubstack F)
    (htraits : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] [Algebra k Ω]
      (x : BasedFunctor
        (discreteModuli (yoneda.obj ((algSpec (.of k)).obj (op (CommAlgCat.of k Ω))))) F),
      ∃ ξ : BasedFunctor (discreteModuli (yoneda.obj
          ((algSpec (.of k)).obj (op (CommAlgCat.of k (PowerSeries Ω)))))) F,
        Nonempty (ModuliTwoIso
          ((discreteModuliMap (yoneda.map (moduliTraitClosed k Ω))).comp ξ) x) ∧
        ∀ z : (discreteModuli (yoneda.obj
          ((algSpec (.of k)).obj
            (op (CommAlgCat.of k
              (Localization.Away (PowerSeries.X : PowerSeries Ω))))))).obj,
          U.property (ξ.obj ((discreteModuliMap
            (yoneda.map (moduliTraitGeneric k Ω))).obj z))) :
    ∀ (V : Over (Spec (.of k)))
      (a : BasedFunctor (discreteModuli (yoneda.obj V)) F), IsEtaleModuliMap a →
      (∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] [Algebra k Ω]
        (v₀ : (algSpec (.of k)).obj (op (CommAlgCat.of k Ω)) ⟶ V)
        (ξ : BasedFunctor (discreteModuli (yoneda.obj
          ((algSpec (.of k)).obj (op (CommAlgCat.of k (PowerSeries Ω)))))) F)
        (φ : ModuliTwoIso
          ((discreteModuliMap (yoneda.map (moduliTraitClosed k Ω))).comp ξ)
          ((discreteModuliMap (yoneda.map v₀)).comp a)),
        (∀ z : (discreteModuli (yoneda.obj
          ((algSpec (.of k)).obj
            (op (CommAlgCat.of k
              (Localization.Away (PowerSeries.X : PowerSeries Ω))))))).obj,
          U.property (ξ.obj ((discreteModuliMap
            (yoneda.map (moduliTraitGeneric k Ω))).obj z))) →
        ∃ (v₁ : (algSpec (.of k)).obj (op (CommAlgCat.of k (PowerSeries Ω))) ⟶ V),
          moduliTraitClosed k Ω ≫ v₁ = v₀ ∧
          ∃ e : ModuliTwoIso ξ ((discreteModuliMap (yoneda.map v₁)).comp a),
            HEq (Functor.whiskerLeft
              (discreteModuliMap (yoneda.map (moduliTraitClosed k Ω))).toFunctor
                e.val.hom) φ.val.hom) ∧
      ∃ (W : Over (Spec (.of k))) (j : W ⟶ V)
        (c : BasedFunctor (discreteModuli (yoneda.obj W))
          (moduliTwoFiberProduct a (fullModuliInclusion F U.property))),
        IsSchemeModuliBaseChange c j ∧ IsOpenImmersion j.left ∧ DenseRange j.left := by
  sorry

end CategoryTheory
