/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeL2.L2NativePunctualWeights
public import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeCondensedWeil.NativeCondensedWeilReality
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartClosure
import WeilConjectures.CategoryTheory.ModuleObjects.FreeMap

/-! # Elementary lisse closure for the native purity argument

Source: sk-p-real-purity, composition-filtration paragraph
(blueprint: lem-rp-native-lisse-closure).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj ZeroObject
namespace WeilConjectures.NativeL2

variable (l : ℕ) [Fact l.Prime] (X : Scheme.{u})

/-- Lissity of actual condensed modules is invariant under isomorphisms.
Source: sk-p-real-purity, actual lisse composition series
(blueprint: lem-rp-native-lisse-closure).

Proof: apply inverse image to the isomorphism on each member of the given finite-free
trivializing cover and compose with the finite-free coordinates there. -/
theorem native_lisse_of_iso
    {M N : NativeCondensedModule.Modules l X} (e : M ≅ N)
    (hM : IsLisseCoefficientModule (Profinite.padicAlgClRingObj l) M) :
    IsLisseCoefficientModule (Profinite.padicAlgClRingObj l) N := by
  obtain ⟨U, hU⟩ := hM
  exact ⟨U, fun i ↦ (hU i).of_iso
    ((CondensedRing.upperStar (Profinite.padicAlgClRingObj l) (U.f i)).mapIso e)⟩

/-- A zero native module is lisse, with rank-zero coordinates.
Source: sk-p-real-purity, zero case (blueprint: lem-rp-native-lisse-closure).

Proof: use the identity cover; its inverse image is zero and hence isomorphic to
the empty finite biproduct of the regular module. -/
theorem native_lisse_of_isZero (M : NativeCondensedModule.Modules l X) (hM : IsZero M) :
    IsLisseCoefficientModule (Profinite.padicAlgClRingObj l) M := by
  let U : Scheme.Cover.{u} Scheme.proetalePrecoverage X :=
    .singleton (𝟙 X) (Precoverage.mem_coverings_of_isIso _)
  refine ⟨U, fun i ↦ ⟨0, ⟨?_⟩⟩⟩
  exact ((CondensedRing.upperStar (Profinite.padicAlgClRingObj l) (U.f i)).map_isZero hM).iso
    ((IsZero.iff_id_eq_zero _).mpr (by
      apply biproduct.hom_ext
      intro j
      exact j.elim0))

/-- A lisse native module is constructible for the finite-constant-model convention.
Source: sk-p-real-purity, mixed filtration paragraph
(blueprint: lem-rp-native-lisse-closure).

Proof: use the coefficient-heart stratification criterion with its single identity
stratum. Inverse image by the identity is isomorphic to the original lisse module. -/
theorem native_constructible_of_lisse [IsNoetherian X]
    (M : NativeCondensedModule.Modules l X)
    (hM : IsLisseCoefficientModule (Profinite.padicAlgClRingObj l) M) :
    IsConstantModelConstructible (Profinite.padicAlgClRingObj l) X M := by
  have h := (coefficientHeart_closure l (Profinite.padicAlgClCondensedRing l)
    (Or.inr rfl)).2 X
  apply (h.2.2.2.2.2.2 M).mpr
  let S : X.FiniteLocallyClosedStratification := {
    n := 1
    stratum := fun _ ↦ Set.univ
    isLocallyClosed_stratum := fun _ ↦ isOpen_univ.isLocallyClosed
    iUnion_stratum_eq_univ := Set.iUnion_const _
    pairwise_disjoint_stratum := fun i j hij ↦ (hij (Subsingleton.elim i j)).elim
    domain := fun _ ↦ X
    immersion := fun _ ↦ 𝟙 X
    isImmersion := fun _ ↦ inferInstance
    range_immersion := fun _ ↦ Set.range_id' }
  exact ⟨S, fun _ ↦ native_lisse_of_iso l X
    ((CondensedRing.upperStarId (Profinite.padicAlgClRingObj l) X).app M).symm hM⟩

set_option maxHeartbeats 1600000 in
-- Canonical preservation isomorphisms have large dependent module types.
attribute [local irreducible] CondensedRing.upperStar in
omit X in
/-- Lissity is closed under kernels, cokernels and extensions in actual native Weil
modules. Source: sk-p-real-purity, actual composition-filtration paragraph
(blueprint: lem-rp-native-lisse-closure).

Proof: the coefficient-heart closure theorem gives these properties for underlying
condensed modules. Forgetting Weil data preserves finite limits and colimits; transport
the kernel and cokernel assertions across the canonical preservation isomorphisms.
For an extension use the short exact sequence of the monomorphism and its cokernel. -/
theorem native_weil_lisse_closure
    (D : FiniteFieldDatum.{u}) (X₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] :
    (∀ {M N : WeilModule D l X₀} (f : M ⟶ N),
      IsLisseCoefficientModule (Profinite.padicAlgClRingObj l) M.carrier →
      IsLisseCoefficientModule (Profinite.padicAlgClRingObj l) N.carrier →
      IsLisseCoefficientModule (Profinite.padicAlgClRingObj l) (kernel f).carrier ∧
      IsLisseCoefficientModule (Profinite.padicAlgClRingObj l) (cokernel f).carrier) ∧
    (∀ {M N : WeilModule D l X₀} (f : M ⟶ N) [Mono f],
      IsLisseCoefficientModule (Profinite.padicAlgClRingObj l) M.carrier →
      IsLisseCoefficientModule (Profinite.padicAlgClRingObj l) (cokernel f).carrier →
      IsLisseCoefficientModule (Profinite.padicAlgClRingObj l) N.carrier) := by
  have : IsNoetherian (D.geometricFiber X₀).left := {
    toIsLocallyNoetherian := by
      change IsLocallyNoetherian (pullback X₀.hom _)
      infer_instance
    toCompactSpace := by
      change CompactSpace ↥(pullback X₀.hom
        (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) : Scheme.{u})
      infer_instance }
  let P : ObjectProperty (NativeCondensedModule.Modules l (D.geometricFiber X₀).left) :=
    IsLisseCoefficientModule (Profinite.padicAlgClRingObj l)
    (X := (D.geometricFiber X₀).left)
  obtain ⟨he, hk, hc⟩ := (coefficientHeart_closure l
    (Profinite.padicAlgClCondensedRing l) (Or.inr rfl)).1 (D.geometricFiber X₀).left
  let := he
  let := hk
  let := hc
  let F := Endofunctor.IsoAlgebra.forget
    (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) (D.geometricFrobenius X₀).hom)
  constructor
  · intro M N f hM hN
    exact ⟨native_lisse_of_iso l _ (PreservesKernel.iso F f).symm
      (P.prop_kernel (F.map f) hM hN),
      native_lisse_of_iso l _ (PreservesCokernel.iso F f).symm
        (P.prop_cokernel (F.map f) hM hN)⟩
  · intro M N f hf hM hQ
    let := hf
    have hS : (ShortComplex.mk f (cokernel.π f) (cokernel.condition f)).ShortExact :=
      ShortComplex.ShortExact.mk' (ShortComplex.exact_of_g_is_cokernel _
        (cokernelIsCokernel f)) inferInstance inferInstance
    exact P.prop_X₂_of_shortExact (hS.map_of_exact F) hM hQ

end WeilConjectures.NativeL2
