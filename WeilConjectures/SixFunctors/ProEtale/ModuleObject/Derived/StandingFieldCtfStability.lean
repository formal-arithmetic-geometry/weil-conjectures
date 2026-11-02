/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.ProEtaleCoefficients.LocalizingAdmissibleCoefficients
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.ProfiniteFiniteConstantLocalModel
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedModuleDerivedPushpull
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SkPropSfExistence
public import WeilConjectures.AlgebraicGeometry.Derived.DerivedTensor
public import WeilConjectures.SixFunctors.Etale.Derived.TorAmplitude
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriek
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Tensor
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.TorAmplitude
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# Constructible finite-Tor stability in the standing field scope

Source: literature/blueprint/latest/blueprint/part-six-operations/sec-six-functors/
sec-the-remaining-operations/sk-thm-sf-ctf-stability/
sk-thm-sf-ctf-stability-direct-images.md, clauses (1)--(4), with the finite or
algebraically closed standing-field scope confirmed by Wei Yang #1412, item 1.
(blueprint: det-thm-sf-ctf-stability-direct-images).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Scheme
open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

attribute [local irreducible] upperStarFromPoint derivedTensor

/-- The six preservation assertions in clauses (1)--(4), in the finite or algebraically
closed standing field. The third conjunct writes locally closed extension as the actual
open extension followed by closed direct image, for each open/closed factorization.
The canonical image factorization defining `coefficientHeartLocallyClosedExtension` is
included. The last conjunct states preservation by every right adjoint to the specified
localizing lower shriek; such an adjoint exists by `sk_prop_sf_existence`, and uniqueness
of right adjoints identifies these choices with the exceptional inverse image.

Source: latest blueprint, part-six-operations/sec-six-functors/sec-the-remaining-operations/
sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.md and its proof,
clauses (1)--(4); Wei Yang #1412, item 1, standing field convention.
(blueprint: det-thm-sf-ctf-stability-direct-images).

Proof plan, following the node:
1. The field has ell-cohomological dimension zero if algebraically closed, and at most
   one if finite. Finite-type schemes over it are Noetherian, hence qcqs.
2. For finite coefficients choose bounded flat constructible models. Exact pullback
   preserves these models. Their total tensor is bounded, flat and constructible and
   is K-flat; the two tensor-bound lemmas add their Tor intervals.
3. Factor a locally closed immersion through its closure. Open extension and closed
   direct image are exact and preserve constructibility. The immersion projection
   formula preserves the Tor interval against every target module sheaf.
4. For integral and rational coefficients Dctf equals Dbc. The integral tensor lemma
   and rational pullback/tensor lemmas give clause (1); E = Q_ell includes Z_ell and Q_ell.
5. For a quasi-compact open immersion, the finite open-image corollary gives Dctf
   preservation. The integral and rational open-image results give Dbc preservation,
   and hence Dctf preservation in those cases.
6. Choose the standing compactification f = p j. Proper preservation, composition
   Rf_* = Rp_* Rj_* and the defining Rf_! = Rp_* D(j_!) give both direct-image clauses.
7. Apply the restriction assertion of Brown existence in this standing field: its
   finite, rational and integral restriction inputs give clause (4) for the same
   localizing right adjoint. No later duality or comparison theorem enters this step.
-/
theorem constructibleFiniteTor_stability_direct_images_of_finite_or_isAlgClosed
    (ℓ : ℕ) [Fact ℓ.Prime]
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    (_hk : Finite k ∨ IsAlgClosed k)
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (_hΛ : IsLocalizingAdmissibleCoefficient ℓ Λ)
    {X Y : Scheme.{u}}
    [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))] [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))]
    [QuasiCompact (Y ↘ Spec (.of k))] [IsSeparated (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))]
    [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f] :
    (∀ K : DerivedCategory
        (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)),
      (constantModelBoundedConstructible Λ Y K ∧
          _root_.DerivedCategory.finiteTorAmplitude _ K) →
        constantModelBoundedConstructible Λ X ((moduleObjectDerivedPullback Λ f).obj K) ∧
          _root_.DerivedCategory.finiteTorAmplitude _ ((moduleObjectDerivedPullback Λ f).obj K)) ∧
    (∀ K M : DerivedCategory
        (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)),
      (constantModelBoundedConstructible Λ X K ∧
          _root_.DerivedCategory.finiteTorAmplitude _ K) →
      (constantModelBoundedConstructible Λ X M ∧
          _root_.DerivedCategory.finiteTorAmplitude _ M) →
        constantModelBoundedConstructible Λ X
            (((-⊗ᴸ-(X)⟦Λ⟧).obj K).obj M) ∧
          _root_.DerivedCategory.finiteTorAmplitude _ (((-⊗ᴸ-(X)⟦Λ⟧).obj K).obj M)) ∧
    (∀ {S Sbar : Scheme.{u}}
        [S.Over (Spec (.of k))] [Sbar.Over (Spec (.of k))]
        [LocallyOfFiniteType (S ↘ Spec (.of k))]
        [QuasiCompact (S ↘ Spec (.of k))] [IsSeparated (S ↘ Spec (.of k))]
        [LocallyOfFiniteType (Sbar ↘ Spec (.of k))]
        [QuasiCompact (Sbar ↘ Spec (.of k))] [IsSeparated (Sbar ↘ Spec (.of k))]
        (a : S ⟶ X) (u : S ⟶ Sbar) (i : Sbar ⟶ X)
        (_ha : a = u ≫ i) [a.IsOver (Spec (.of k))]
        [u.IsOver (Spec (.of k))] [i.IsOver (Spec (.of k))]
        [IsOpenImmersion u] [IsClosedImmersion i]
        (K : DerivedCategory
          (Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1}) (condensedRingObj Λ S))),
      (constantModelBoundedConstructible Λ S K ∧
          _root_.DerivedCategory.finiteTorAmplitude _ K) →
        constantModelBoundedConstructible Λ X
            ((D((u)_!open⟦Λ⟧) ⋙ R((i)_*⟦Λ⟧)).obj K) ∧
          _root_.DerivedCategory.finiteTorAmplitude _
            ((D((u)_!open⟦Λ⟧) ⋙ R((i)_*⟦Λ⟧)).obj K)) ∧
    (∀ K : DerivedCategory
        (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)),
      (constantModelBoundedConstructible Λ X K ∧
          _root_.DerivedCategory.finiteTorAmplitude _ K) →
        constantModelBoundedConstructible Λ Y
            ((moduleObjectDerivedPushforward Λ f).obj K) ∧
          _root_.DerivedCategory.finiteTorAmplitude _
            ((moduleObjectDerivedPushforward Λ f).obj K)) ∧
    (∀ K : DerivedCategory
        (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)),
      (constantModelBoundedConstructible Λ X K ∧
          _root_.DerivedCategory.finiteTorAmplitude _ K) →
        constantModelBoundedConstructible Λ Y
            ((rightDerivedLowerShriekOfCompactification Λ
              (@HasCompactification.compactification X Y f
              (HasCompactification.of_isOver (S := Spec (.of k)) f))).obj K) ∧
          _root_.DerivedCategory.finiteTorAmplitude _
            ((rightDerivedLowerShriekOfCompactification Λ
              (@HasCompactification.compactification X Y f
              (HasCompactification.of_isOver (S := Spec (.of k)) f))).obj K)) ∧
    (∀ (h : ∀ K, localizingClosureProEtale Λ X K →
          localizingClosureProEtale Λ Y
            ((rightDerivedLowerShriekOfCompactification Λ
              (@HasCompactification.compactification X Y f
              (HasCompactification.of_isOver (S := Spec (.of k)) f))).obj K))
        (G : (localizingClosureProEtale Λ Y).FullSubcategory ⥤
          (localizingClosureProEtale Λ X).FullSubcategory)
        (_adj : (localizingLowerShriek Λ (@HasCompactification.compactification X Y f
              (HasCompactification.of_isOver (S := Spec (.of k)) f)) h) ⊣ G),
      ∀ K : DerivedCategory
        (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)),
        (hK : constantModelBoundedConstructible Λ Y K ∧
            _root_.DerivedCategory.finiteTorAmplitude _ K) →
          constantModelBoundedConstructible Λ X
            (G.obj ⟨K, fun P _hP hS ↦ hS K hK⟩).obj ∧
          _root_.DerivedCategory.finiteTorAmplitude _ (G.obj ⟨K, fun P _hP hS ↦ hS K hK⟩).obj)
 := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
