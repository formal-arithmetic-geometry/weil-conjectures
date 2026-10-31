/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.PurityFiniteSetting
public import WeilConjectures.AlgebraicGeometry.CondensedFiniteTorConstructible
public import WeilConjectures.SecSmoothPurity.DetPropSfCbc
public import WeilConjectures.SixFunctors.Etale.Derived.TorAmplitude
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange
public import WeilConjectures.SixFunctors.Etale.Derived.Point

import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper

/-!
# Geometric stalks of compactly supported direct image

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-prop-an/
lem-pur-cfiber-stalk.md (blueprint: lem-pur-cfiber-stalk).

The finite case uses the permitted small-etale presentation and applies derived sections
on the algebraically closed point to the canonical exchange. The other three coefficient
rings use ordinary condensed module objects: inverse image on Spec Omega is the stalk,
and compact-support direct image to Spec Omega is compactly supported cohomology there.
Both statements use the proper-mate/open-comparison map with an arbitrary compactification.
-/

@[expose] public section

set_option autoImplicit false
universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.Obj

namespace WeilConjectures

/-- Finite-coefficient clause of the geometric compact-fiber stalk comparison.
Source: latest blueprint lem-pur-cfiber-stalk, finite-coefficient proof paragraph
(blueprint: lem-pur-cfiber-stalk).
Proof: choose the supplied compactification and base change it along the geometric point.
Finite-coefficient compact-support base change makes its canonical exchange invertible.
On Spec Omega every etale covering splits, so derived global sections identifies pullback
with the derived geometric stalk. Sections of the base-changed compact-support direct
image are RΓ_c of the geometric fibre, with the restricted complex. Applying derived
sections to the exchange therefore gives exactly the displayed canonical comparison.
Compactification independence identifies this with the intrinsic Rf_! comparison. -/
theorem compactFiberStalk_finite
    (P : PurityFiniteSetting.{u})
    {X Y : Scheme.{u}}
    [X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
    [IsSeparated (X ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    [IsSeparated (Y ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y ↘ Spec (.of P.field.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of P.field.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (b : Spec (.of Ω) ⟶ Y)
    (c : Compactification f)
    (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient)))
    (_hK : Etale.DerivedCategory.constructibleFiniteTor
      (ModuleCat.{u + 1} P.Coefficient) X K) :
    IsIso ((Etale.rightDerivedGlobalSections
      (ModuleCat.{u + 1} P.Coefficient) (Spec (.of Ω))).map
        ((Etale.rightDerivedLowerShriekOfCompactificationBaseChangeMap
          (ModuleCat.{u + 1} P.Coefficient) (IsPullback.of_hasPullback f b) c).app K)) := by
  let : Finite P.Coefficient := by
    change Finite (ULift.{u + 1} (Padic.coefficientExtensionRing
      P.coefficients.l P.extension P.level))
    exact Equiv.ulift.finite_iff.mpr
      (Padic.finite_coefficientExtensionRing _ _ _ P.level_pos)
  let : IsIso (Etale.derivedBaseChangeMap (ModuleCat.{u + 1} P.Coefficient)
      (IsPullback.of_hasPullback c.g b).toCommSq) :=
    Etale.isIso_derivedBaseChangeMap_of_isProper_of_isAddTorsion_ring
      P.Coefficient isAddTorsion_of_finite (IsPullback.of_hasPullback c.g b)
  let := Etale.isIso_rightDerivedLowerShriekOfCompactificationBaseChangeMap
    (ModuleCat.{u + 1} P.Coefficient) (IsPullback.of_hasPullback f b) c
  infer_instance

/-- Ordinary condensed coefficient clause for O_E, E and Qbar_ell.
The disjunction specifies precisely these three topological coefficient rings, allowing
isomorphic ring presentations. The finite coefficient field is algebra-isomorphic to
P.extension, so it is the fixed E of the conventions; the finite quotient is above.
Source: latest blueprint lem-pur-cfiber-stalk, nonfinite-coefficient proof paragraph
(blueprint: lem-pur-cfiber-stalk).
Proof: the source of the compact-support exchange at K is (Rf_! K) pulled back to the
geometric point, and its target is RΓ_c of X times_Y Spec Omega with the pulled-back K.
The specified exchange is the proper base-change mate followed by the inverse canonical
open comparison. X and Y are Noetherian because they are finite type over k, as is the
proper compactification Z; the fibre morphism is quasi-compact by base change. Apply
clause (b) of det-prop-sf-cbc to this arbitrary geometric point and to the bounded
constructible component of hK. It makes exactly this exchange invertible. This argument
also covers points over nonclosed points: Omega need not be finite type over k. -/
theorem compactFiberStalk_condensed
    (P : PurityFiniteSetting.{u})
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (_hΛ :
      (∃ E : PadicAlgCl.FiniteIntermediateField P.coefficients.l,
        Nonempty (P.extension ≃ₐ[Padic P.coefficients.l] E) ∧
        Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicIntegersRingObj P.coefficients.l E))) ∨
      (∃ E : PadicAlgCl.FiniteIntermediateField P.coefficients.l,
        Nonempty (P.extension ≃ₐ[Padic P.coefficients.l] E) ∧
        Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj E))) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicAlgClRingObj P.coefficients.l)))
    {X Y : Scheme.{u}}
    [X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
    [IsSeparated (X ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    [IsSeparated (Y ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y ↘ Spec (.of P.field.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of P.field.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (b : Spec (.of Ω) ⟶ Y)
    (c : Compactification f)
    (K : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (ProEtale.condensedRingObj Λ X)))
    (_hK : ProEtale.CondensedRing.condensedConstructibleFiniteTor Λ X K) :
    IsIso ((ProEtale.CondensedRing.detSfCompactSupportBaseChangeComposite Λ f b c
      (ProEtale.CondensedRing.compactSupportOpenBaseChangeIso Λ f b c)).app K) := by
  let : IsNoetherian X :=
    isNoetherian_of_locallyOfFiniteType (X ↘ Spec (.of P.field.k))
  let : IsNoetherian Y :=
    isNoetherian_of_locallyOfFiniteType (Y ↘ Spec (.of P.field.k))
  let : IsNoetherian c.Z := isNoetherian_of_locallyOfFiniteType c.g
  have hΛ :
      (∃ E : PadicAlgCl.FiniteIntermediateField P.coefficients.l,
        Nonempty (Mon.mk Λ ≅ Mon.mk
          (Profinite.padicIntegersRingObj P.coefficients.l E))) ∨
      (∃ E : PadicAlgCl.FiniteIntermediateField P.coefficients.l,
        Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj E))) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicAlgClRingObj P.coefficients.l)) := by
    rcases _hΛ with ⟨E, _, hE⟩ | ⟨E, _, hE⟩ | hE
    · exact Or.inl ⟨E, hE⟩
    · exact Or.inr (Or.inl ⟨E, hE⟩)
    · exact Or.inr (Or.inr hE)
  exact (ProEtale.CondensedRing.condensed_compactSupportBaseChange
    P.coefficients.l Λ hΛ f b c K _hK.1).2.2

end WeilConjectures
