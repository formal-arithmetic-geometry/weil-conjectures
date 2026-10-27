/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q06
-/
module

public import WeilConjectures.Mathlib.AlgebraicGeometry.Normalization
public import WeilConjectures.AlgebraicGeometry.FunctionField
public import WeilConjectures.AlgebraicGeometry.StalkAut
public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.FieldTheory.Separable
import Sheaf.AlgebraicGeometry.FiniteOverProjective
import Sheaf.AlgebraicGeometry.NormalizationExtendsCover
import WeilConjectures.AlgebraicGeometry.SpreadFiniteSeparableExtension
import Mathlib.RingTheory.Localization.Integral
import Mathlib.RingTheory.Localization.BaseChange

/-! # The finite semilinear normalization model

Source: de Jong, Families of curves and alterations (1997), Situation 5.3 and
Lemma 5.6, pp. 613--614; Stacks Project, Tags 035H, 035I, 035K, 035L, 0AVK and 0BQL
(blueprint: lem-sfb-semilinear-normalization-finite-model).
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry.Scheme

/-- The prescribed finite separable extension has its finite projective normalization model,
with the prescribed semilinear action, even when the actions are not faithful.
The field identification is pinned by the canonical map from `Spec M`; the affine
identifications are over the specified affine open, and the generic fibre identifies both
projections. The action on function fields uses inverse geometric automorphisms.

Source: de Jong (1997), Situation 5.3 and Lemma 5.6, pp. 613--614; Stacks Project,
Tags 035H, 035I, 035K, 035L, 0AVK and 0BQL
(blueprint: lem-sfb-semilinear-normalization-finite-model).

Proof:
1. Apply lem-sfb-finite-normalization-model-functoriality to S and M. It gives normality,
   integrality, finite type, the canonical function field, finiteness and surjectivity.
   By lem-fin-finite-over-projective over the affine Noetherian field spectrum, the
   normalization is projective. The given finite type includes quasi-compactness.
2. On each nonempty affine open, def-fin-normalization-extension gives the integral closure.
   By lem-sc-integral-function-field-affine-fraction the section ring has fraction field K.
   Using lem-weil-pbc-fibre-product-affine-spectra, lem-weil-pbc-localization-base-change and
   lem-weil-pbc-integral-closure-commutes-localization, its generic fibre ring is the integral
   closure of K in M, hence M. These identifications agree with the inclusions in M.
3. Choose a nonempty Noetherian affine chart of S. Apply
   lem-weil-pbc-spread-finite-separable-extension to M/K there. Inverting the nonzero
   coefficient denominators and discriminant gives a finite etale domain with fraction
   field M. The corresponding nonempty open V is dense in integral S and is normal.
4. Apply lem-fin-normalization-extends-cover to this connected finite etale cover of V.
   Its prescribed function field identifies its normalization with S.normalizationIn M,
   so the restriction of the latter is etale. No invariance of V is required.
5. For j in J, the inverse of sigma j extends the pullback by the automorphism rho j of S.
   The semilinear isomorphism clause of lem-sfb-finite-normalization-model-functoriality
   lifts it to the normalization. Uniqueness gives the identity and multiplication laws:
   pullback reverses composition, and sigma_l inverse composed with sigma_j inverse is
   sigma_(j*l) inverse. The lift commutes with the map to S.
6. The generic geometric map is Spec of sigma_j inverse. Applying this to j inverse says
   that inverse geometric pullback on k(W), under its canonical identification with M,
   is sigma_j. Composing equivariance with the structure map of S gives the original
   action on k composed with rho.
-/
theorem semilinear_normalization_finite_model
    {k : Type u} [Field k] (S : Scheme.{u}) [IsIntegral S]
    [S.Over (Spec (.of k))] [IsHProjective (S ↘ Spec (.of k))]
    [LocallyOfFiniteType (S ↘ Spec (.of k))] [QuasiCompact (S ↘ Spec (.of k))]
    (hS : ∀ s : S, IsDomain (S.presheaf.stalk s) ∧
      IsIntegrallyClosed (S.presheaf.stalk s))
    {H : Type v} [Group H] [Finite H]
    (aS : H →* Aut S) (ak : H →* (k ≃+* k))
    (hbase : ∀ h : H, (aS h).hom ≫ (S ↘ Spec (.of k)) =
      (S ↘ Spec (.of k)) ≫ Spec.map (CommRingCat.ofHom (ak h⁻¹).toRingHom))
    (M : Type u) [Field M] [Algebra S.functionField M]
    [FiniteDimensional S.functionField M] [Algebra.IsSeparable S.functionField M]
    {J : Type w} [Group J] [Finite J]
    (ρ : J →* H) (hρ : Function.Surjective ρ) (σ : J →* (M ≃+* M))
    (hσ : ∀ (j : J) (x : S.functionField),
      σ j (algebraMap S.functionField M x) =
        algebraMap S.functionField M ((functionFieldAut (aS (ρ j)⁻¹)).hom x)) :
    (∀ z : S.normalizationIn M,
      IsDomain ((S.normalizationIn M).presheaf.stalk z) ∧
        IsIntegrallyClosed ((S.normalizationIn M).presheaf.stalk z)) ∧
    IsIntegral (S.normalizationIn M) ∧
    IsHProjective (S.fromNormalizationIn M ≫ (S ↘ Spec (.of k))) ∧
    LocallyOfFiniteType (S.fromNormalizationIn M ≫ (S ↘ Spec (.of k))) ∧
    QuasiCompact (S.fromNormalizationIn M ≫ (S ↘ Spec (.of k))) ∧
    IsFinite (S.fromNormalizationIn M) ∧ Surjective (S.fromNormalizationIn M) ∧
    (∃ V : S.Opens, Dense (V : Set S) ∧ Etale (S.fromNormalizationIn M ∣_ V)) ∧
    (∀ (U : S.Opens) [Nonempty U] (hU : IsAffineOpen U)
      [Algebra Γ(S, U) M] [IsScalarTower Γ(S, U) S.functionField M],
      ∃ e : (S.fromNormalizationIn M ⁻¹ᵁ U).toScheme ≅
        Spec (.of (integralClosure Γ(S, U) M)),
        e.inv ≫ (S.fromNormalizationIn M ⁻¹ᵁ U).ι ≫ S.fromNormalizationIn M =
          Spec.map (CommRingCat.ofHom
            (algebraMap Γ(S, U) (integralClosure Γ(S, U) M))) ≫ hU.fromSpec) ∧
    (∃ e : Spec (.of M) ≅ pullback (S.fromNormalizationIn M) S.fromSpecFunctionField,
      e.hom ≫ pullback.fst _ _ = (S.fromSpecOfAlgebraFunctionField M).toNormalization ∧
      e.hom ≫ pullback.snd _ _ =
        Spec.map (CommRingCat.ofHom (algebraMap S.functionField M))) ∧
    ∃ (e : (S.normalizationIn M).functionField ≃+* M)
      (aW : J →* Aut (S.normalizationIn M)),
      Spec.map (CommRingCat.ofHom e.toRingHom) ≫
          (S.normalizationIn M).fromSpecFunctionField =
        (S.fromSpecOfAlgebraFunctionField M).toNormalization ∧
      (∀ j : J, (aW j).hom ≫ S.fromNormalizationIn M =
        S.fromNormalizationIn M ≫ (aS (ρ j)).hom) ∧
      (∀ j : J, Spec.map (CommRingCat.ofHom (σ j).symm.toRingHom) ≫
          (S.fromSpecOfAlgebraFunctionField M).toNormalization =
        (S.fromSpecOfAlgebraFunctionField M).toNormalization ≫ (aW j).hom) ∧
      (∀ j : J, (aW j).hom ≫ S.fromNormalizationIn M ≫ (S ↘ Spec (.of k)) =
        (S.fromNormalizationIn M ≫ (S ↘ Spec (.of k))) ≫
          Spec.map (CommRingCat.ofHom (ak (ρ j)⁻¹).toRingHom)) ∧
      ∀ (j : J) (x : (S.normalizationIn M).functionField),
        e ((functionFieldAut (aW j⁻¹)).hom x) = σ j (e x) := by
  sorry

end AlgebraicGeometry.Scheme
