/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Compactification.CompactificationOverField
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedFiniteTorConstructible
public import WeilConjectures.AlgebraicGeometry.BaseFieldFiniteCD.FiniteCohomologicalDimensionHypothesis
public import WeilConjectures.CategoryTheory.ProEtaleCoefficients.LocalizingAdmissibleCoefficients

/-! # Native condensed exceptional-operation restrictions

This module states the native finite-Tor restriction needed by `sk-def-set`.
It keeps the canonical compactification and the Brown right adjoint tied to a
morphism of schemes over `Spec k`; no arbitrary adjunction datum is introduced.
Source: latest blueprint `det-def-sf-operations`, clauses (vi) and (2)--(4) of
`sk-thm-existence` (blueprint: def-pd-native-condensed-operations).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u

open CategoryTheory
open AlgebraicGeometry

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- Preservation of native finite-Tor constructibility by the canonical compact-support
functor. Source: `det-def-sf-operations` (vi), `sk-prop-sf-rf-shriek-preservation`
(blueprint: def-pd-native-condensed-operations).
Proof: apply the finite-Tor preservation statement from the Brown/localizing
construction for `compactificationOverField k f.left`, then transport its
ConstantModel predicate across the canonical comparison to the intrinsic native
`condensedConstructibleFiniteTor` predicate. -/
theorem nativeLowerShriek_mem
    (ell : ℕ) [Fact ell.Prime] (k : Type u) [Field k]
    (hkp : (ringChar k).Prime) (hkl : ringChar k ≠ ell)
    (hk : Finite k ∨ IsAlgClosed k) (hcd : BaseFieldFiniteCD ell k)
    {X Y : Over (Spec (.of k))}
    [LocallyOfFiniteType (X.left ↘ Spec (.of k))]
    [QuasiCompact (X.left ↘ Spec (.of k))] [IsSeparated (X.left ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y.left ↘ Spec (.of k))]
    [QuasiCompact (Y.left ↘ Spec (.of k))] [IsSeparated (Y.left ↘ Spec (.of k))]
    (f : X ⟶ Y) (hΛ : IsLocalizingAdmissibleCoefficient ell Λ) :
    ∀ K, condensedConstructibleFiniteTor Λ X.left K →
      condensedConstructibleFiniteTor Λ Y.left
        ((rightDerivedLowerShriekOfCompactification Λ
          (compactificationOverField k f.left).obj.obj).obj K) := by
  sorry

/-- Restrict the canonical compact-support functor to the native finite-Tor
constructible categories. The compactification is the canonical
`compactificationOverField f.left` attached to the displayed morphism over
`Spec k`.
Source: `det-def-sf-operations` (vi), `sk-thm-existence`
(blueprint: def-pd-native-condensed-operations). -/
noncomputable def nativeLowerShriek
    (ell : ℕ) [Fact ell.Prime] (k : Type u) [Field k]
    (hkp : (ringChar k).Prime) (hkl : ringChar k ≠ ell)
    (hk : Finite k ∨ IsAlgClosed k) (hcd : BaseFieldFiniteCD ell k)
    {X Y : Over (Spec (.of k))}
    [LocallyOfFiniteType (X.left ↘ Spec (.of k))]
    [QuasiCompact (X.left ↘ Spec (.of k))] [IsSeparated (X.left ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y.left ↘ Spec (.of k))]
    [QuasiCompact (Y.left ↘ Spec (.of k))] [IsSeparated (Y.left ↘ Spec (.of k))]
    (f : X ⟶ Y) (hΛ : IsLocalizingAdmissibleCoefficient ell Λ) :
    CondensedConstructibleFiniteTor Λ X.left ⥤ CondensedConstructibleFiniteTor Λ Y.left :=
  letI : MonObj (condensedRingObj Λ X.left) :=
    Functor.monObjObj (F := upperStarFromPoint X.left) Λ
  letI : MonObj (condensedRingObj Λ Y.left) :=
    Functor.monObjObj (F := upperStarFromPoint Y.left) Λ
  let c := (compactificationOverField k f.left).obj.obj
  ObjectProperty.lift (condensedConstructibleFiniteTor Λ Y.left)
    ((condensedConstructibleFiniteTor Λ X.left).ι ⋙
      rightDerivedLowerShriekOfCompactification Λ c)
    (fun K ↦ AlgebraicGeometry.ProEtale.CondensedRing.nativeLowerShriek_mem
      Λ ell k hkp hkl hk hcd f hΛ K.obj K.property)

/-- Native finite-Tor preservation and the right-adjoint conclusion supplied by
the Brown construction. The field, coefficient-admissibility, separated
finite-type, quasi-compact, and finite-CD hypotheses are explicit, and the
morphism is bundled in `Over (Spec k)`. The proof transports the localizing
Brown adjunction from the ConstantModel constructible category through the
canonical comparison to the native finite-Tor category.
Source: `det-def-sf-operations` (vi), `sk-thm-existence` (blueprint:
def-pd-native-condensed-operations).
Proof: invoke the Brown/localizing right-adjoint theorem under the displayed
hypotheses for `compactificationOverField k f.left`; use the comparison
equivalence between ConstantModelConstructibleFiniteTor and
CondensedConstructibleFiniteTor, transport the adjunction Hom bijections, and
identify the transported lower functor with `nativeLowerShriek` by its objectwise
restriction. -/
theorem nativeLowerShriek_isLeftAdjoint
    (ell : ℕ) [Fact ell.Prime] (k : Type u) [Field k]
    (hkp : (ringChar k).Prime) (hkl : ringChar k ≠ ell)
    (hk : Finite k ∨ IsAlgClosed k) (hcd : BaseFieldFiniteCD ell k)
    {X Y : Over (Spec (.of k))}
    [LocallyOfFiniteType (X.left ↘ Spec (.of k))]
    [QuasiCompact (X.left ↘ Spec (.of k))] [IsSeparated (X.left ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y.left ↘ Spec (.of k))]
    [QuasiCompact (Y.left ↘ Spec (.of k))] [IsSeparated (Y.left ↘ Spec (.of k))]
    (f : X ⟶ Y) (hΛ : IsLocalizingAdmissibleCoefficient ell Λ) :
    (nativeLowerShriek Λ ell k hkp hkl hk hcd f hΛ).IsLeftAdjoint := by
  sorry

/-- The canonical exceptional inverse image on the native finite-Tor category,
selected as the right adjoint of the Brown compact-support restriction.
Source: `det-def-sf-operations` (vi), `sk-thm-existence`
(blueprint: def-pd-native-condensed-operations).
Proof: take the right-adjoint component furnished by
`nativeLowerShriek_isLeftAdjoint`; its adjunction is the transported Brown
adjunction on the native finite-Tor full subcategories. -/
noncomputable def nativeExceptionalInverseImage
    (ell : ℕ) [Fact ell.Prime] (k : Type u) [Field k]
    (hkp : (ringChar k).Prime) (hkl : ringChar k ≠ ell)
    (hk : Finite k ∨ IsAlgClosed k) (hcd : BaseFieldFiniteCD ell k)
    {X Y : Over (Spec (.of k))}
    [LocallyOfFiniteType (X.left ↘ Spec (.of k))]
    [QuasiCompact (X.left ↘ Spec (.of k))] [IsSeparated (X.left ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y.left ↘ Spec (.of k))]
    [QuasiCompact (Y.left ↘ Spec (.of k))] [IsSeparated (Y.left ↘ Spec (.of k))]
    (f : X ⟶ Y) (hΛ : IsLocalizingAdmissibleCoefficient ell Λ) :
    CondensedConstructibleFiniteTor Λ Y.left ⥤ CondensedConstructibleFiniteTor Λ X.left :=
  letI := nativeLowerShriek_isLeftAdjoint Λ ell k hkp hkl hk hcd f hΛ
  (nativeLowerShriek Λ ell k hkp hkl hk hcd f hΛ).rightAdjoint

/-- The adjunction characterizing the native exceptional inverse image.
Source: `det-def-sf-operations` (vi), `sk-thm-existence` (blueprint:
def-pd-native-condensed-operations).
Proof: apply `Adjunction.ofIsLeftAdjoint` to the Brown-transported
`IsLeftAdjoint` instance from `nativeLowerShriek_isLeftAdjoint`. -/
noncomputable def nativeExceptionalAdjunction
    (ell : ℕ) [Fact ell.Prime] (k : Type u) [Field k]
    (hkp : (ringChar k).Prime) (hkl : ringChar k ≠ ell)
    (hk : Finite k ∨ IsAlgClosed k) (hcd : BaseFieldFiniteCD ell k)
    {X Y : Over (Spec (.of k))}
    [LocallyOfFiniteType (X.left ↘ Spec (.of k))]
    [QuasiCompact (X.left ↘ Spec (.of k))] [IsSeparated (X.left ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y.left ↘ Spec (.of k))]
    [QuasiCompact (Y.left ↘ Spec (.of k))] [IsSeparated (Y.left ↘ Spec (.of k))]
    (f : X ⟶ Y) (hΛ : IsLocalizingAdmissibleCoefficient ell Λ) :
    nativeLowerShriek Λ ell k hkp hkl hk hcd f hΛ ⊣
      nativeExceptionalInverseImage Λ ell k hkp hkl hk hcd f hΛ :=
  letI := nativeLowerShriek_isLeftAdjoint Λ ell k hkp hkl hk hcd f hΛ
  Adjunction.ofIsLeftAdjoint _

end AlgebraicGeometry.ProEtale.CondensedRing
