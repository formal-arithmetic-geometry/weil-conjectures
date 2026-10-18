/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q20
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZeroExact
public import Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZeroAdjunction
public import Sheaf.AlgebraicGeometry.ProEtaleIntrinsicFiniteOperations
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategory
public import WeilConjectures.CategoryTheory.DerivedCategory.HasMonoidalDerivedCategory

import Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import Sheaf.AlgebraicGeometry.ProEtaleRingedOpenComparison
import Sheaf.CategoryTheory.LocalizedModuleExactIndependent
import Sheaf.CategoryTheory.RingedSliceExtensionTensor
import Sheaf.Algebra.Homology.KFlat
import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorClosed
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.AlgebraicGeometry.ProEtaleInverseImage
import Sheaf.Paper.KFlatRingedToposPullback
import Sheaf.Algebra.Homology.SiteDerivedTensorDescent
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous

/-!
# Tensoring an extension by zero

Source: Weil blueprint, sec-six-functors/sk-lem-sf-open-ctf, order 2160;
Stacks Project, Tags 0E8I and 0GL1 (blueprint: lem-trf-open-tensor).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- Open restriction is additive by the published extension/restriction adjunction.
Source: Stacks, Tags 03DI and 03DJ (blueprint: lem-trf-open-tensor). -/
noncomputable instance sfOpenTensorRestriction_additive {U Y : Scheme.{u}} (j : U ⟶ Y)
    [IsOpenImmersion j] (A : Type u) [CommRing A] [Finite A] :
    (sfIntrinsicOpenRestriction j A).Additive :=
  (sfIntrinsicExtensionByZeroAdjunction j A).right_adjoint_additive

/-- Left exactness of open restriction, from the published adjunction.
Source: Stacks, Tag 03DJ (blueprint: lem-trf-open-tensor). -/
noncomputable instance sfOpenTensorRestriction_preservesFiniteLimits
    {U Y : Scheme.{u}} (j : U ⟶ Y) [IsOpenImmersion j]
    (A : Type u) [CommRing A] [Finite A] :
    PreservesFiniteLimits (sfIntrinsicOpenRestriction j A) :=
  letI : PreservesLimitsOfSize.{0, 0} (sfIntrinsicOpenRestriction j A) :=
    (sfIntrinsicExtensionByZeroAdjunction j A).rightAdjoint_preservesLimits
  inferInstance

/-- Right exactness of open restriction, transported through the canonical equivalences.
Source: Stacks, Tag 03DJ (blueprint: lem-trf-open-tensor). -/
noncomputable instance sfOpenTensorRestriction_preservesFiniteColimits
    {U Y : Scheme.{u}} (j : U ⟶ Y) [IsOpenImmersion j]
    (A : Type u) [CommRing A] [Finite A] :
    PreservesFiniteColimits (sfIntrinsicOpenRestriction j A) :=
  letI : PreservesColimitsOfSize.{0, 0} (sfIntrinsicOpenRestriction j A) :=
    (((sfIntrinsicModuleEquivalence Y A).symm.toAdjunction.comp
      (ProEtale.openImmersionRestrictionLowerStarAdjunction
        (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j)).comp
          (sfIntrinsicModuleEquivalence U A).toAdjunction).leftAdjoint_preservesColimits
  inferInstance

/-- The bifunctor `(K,M) ↦ (j_!K) ⊗ᴸ_A M`, in intrinsic constant-ring modules.
The canonical realization equivalences change only the presentation of coefficients.
The middle tensor is the K-flat derived monoidal tensor, the defining expression of
`ProEtale.derivedTensor`; no new tensor structure is chosen.
Source: blueprint order 2160; Stacks, Tags 0E8I and 0GL1
(blueprint: lem-trf-open-tensor). -/
noncomputable def sfOpenTensorLeft {U Y : Scheme.{u}} (j : U ⟶ Y)
    [IsOpenImmersion j] (A : Type u) [CommRing A] [Finite A] :
    proEtaleDerivedCategory U A ⥤ proEtaleDerivedCategory Y A ⥤
      proEtaleDerivedCategory Y A :=
  (Functor.postcompose₂.obj
    (sfIntrinsicModuleEquivalence Y A).functor.mapDerivedCategory).obj
      ((((Functor.whiskeringLeft₂ _).obj
        ((sfIntrinsicExtensionByZero j A).mapDerivedCategory ⋙
          (sfIntrinsicModuleEquivalence Y A).inverse.mapDerivedCategory)).obj
            (sfIntrinsicModuleEquivalence Y A).inverse.mapDerivedCategory).obj
              (curriedTensor
                (DerivedCategory (Sheaf (ProEt.topology Y)
                  (ModuleCat.{u + 1} (ULift.{u + 1, u} A))))))

/-- The bifunctor `(K,M) ↦ j_!(K ⊗ᴸ_A j^*M)`, in intrinsic constant-ring modules.
Restriction is the published open restriction, applied termwise since it is exact.
The tensor is transported through the same canonical coefficient realization as on
`sfOpenTensorLeft`, and extension is exactly `sfIntrinsicExtensionByZero`.
Source: blueprint order 2160; Stacks, Tags 0E8I and 0GL1
(blueprint: lem-trf-open-tensor). -/
noncomputable def sfOpenTensorRight {U Y : Scheme.{u}} (j : U ⟶ Y)
    [IsOpenImmersion j] (A : Type u) [CommRing A] [Finite A] :
    proEtaleDerivedCategory U A ⥤ proEtaleDerivedCategory Y A ⥤
      proEtaleDerivedCategory Y A :=
  (Functor.postcompose₂.obj
    ((sfIntrinsicModuleEquivalence U A).functor.mapDerivedCategory ⋙
      (sfIntrinsicExtensionByZero j A).mapDerivedCategory)).obj
      ((((Functor.whiskeringLeft₂ _).obj
        (sfIntrinsicModuleEquivalence U A).inverse.mapDerivedCategory).obj
          ((sfIntrinsicOpenRestriction j A).mapDerivedCategory ⋙
            (sfIntrinsicModuleEquivalence U A).inverse.mapDerivedCategory)).obj
              (curriedTensor
                (DerivedCategory (Sheaf (ProEt.topology U)
                  (ModuleCat.{u + 1} (ULift.{u + 1, u} A))))))

/-- Tensoring an extension by zero: simultaneously natural in arbitrary unbounded
`K ∈ D(U,A)` and `M ∈ D(Y,A)`.
Source: blueprint order 2160; Stacks, Tags 0E8I and 0GL1
(blueprint: lem-trf-open-tensor).

Proof plan:
1. Identify the pro-etale site of the open with the localized ringed site using
   lem-weil-proetale-weakly-etale-localization and
   lem-weil-pbc-proetale-ringed-open-comparison. The unique factorization through
   the open identifies the extension presheaves. Both extension and restriction
   are exact by lem-pur-site-restriction-module-adjunction-exact, so descend termwise.
2. Apply lem-weil-pbc-ringed-slice-extension-tensor to obtain the underived formula,
   natural in both module sheaves.
3. The left adjoint commutes with coproducts by
   lem-weil-pbc-left-adjoint-preserves-colimits. Apply the sheaf formula to every
   summand of the total tensor complex. Naturality intertwines both differentials,
   and additivity preserves the sign in d_P tensor 1 + (-1)^p 1 tensor d_Q.
4. Extension preserves K-flatness: for acyclic N, restriction of N is acyclic;
   K-flatness and the complex formula then imply extension of P tensor N is acyclic.
   Tensor symmetry supplies either tensor order. The same exact-functor composite
   proves that flat terms remain flat.
5. Choose K-flat flat-term resolutions by lem-pc-kflat-resolution. Restriction
   preserves their K-flatness by lem-weil-pbc-ringed-pullback-preserves-kflat.
   The computation isomorphisms of lem-weil-pbc-site-derived-tensor-descent identify
   the two total complexes with the displayed derived tensor products.
6. The complex isomorphism respects chain maps and homotopies in each variable.
   Descend separately along the two K-flat localization equivalences; naturality
   extends to inverses of quasi-isomorphisms and hence to all derived morphisms.
   The canonical realization equivalences transport this same natural isomorphism
   to the intrinsic module categories used by the two displayed bifunctors. -/
theorem sfOpenTensor {U Y : Scheme.{u}} (j : U ⟶ Y) [IsOpenImmersion j]
    (A : Type u) [CommRing A] [Finite A] :
    Nonempty (sfOpenTensorLeft j A ≅ sfOpenTensorRight j A) := by
  sorry

end AlgebraicGeometry.Scheme
