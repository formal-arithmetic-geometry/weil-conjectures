/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F4
-/
module

public import Sheaf.Paper.CondensedConstantConstructibility
public import Mathlib.NumberTheory.Padics.Complex
import Sheaf.Paper.ContinuousAlgClLocalFree
import all Sheaf.UpstreamExtra.WeilConjectures.CategoryTheory.ModuleObjects.GrothendieckAbelian
import all Sheaf.Paper.CondensedFiniteFreeTensorExact
import all Sheaf.AlgebraicGeometry.ProEtaleAbelianClosedSupport
import all Sheaf.Paper.CoefficientHeartLisseRestriction
import Sheaf.Paper.ConstantModelTorAmplitude
import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
import WeilConjectures.CategoryTheory.DerivedCategory.BoundedEssentiallySmall
public import Sheaf.UpstreamExtra.WeilConjectures.CategoryTheory.ModuleObjects.GrothendieckAbelian

/-!
# Finite Tor amplitude over the full continuous algebraic closure

Source: blueprint main-20261015, sk-thm-sfb-proper-base-change, the equality
Dctf = Dbc for rational coefficients, specialized to the all-continuous-map coefficient.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory MonoidalCategory Limits
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale
private lemma stratified_map_eq
    {X : Scheme.{u}} [TopologicalSpace.NoetherianSpace X]
    [IsLocallyNoetherian X]
    (S : Scheme.Stratification X)
    (R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj R]
    {P Q : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R} (f g : P ⟶ Q)
    (h : ∀ i, ((upperStar Ab.{u + 1} (S.immersion i)).mapMod R).map f =
      ((upperStar Ab.{u + 1} (S.immersion i)).mapMod R).map g) : f = g := by
  apply (Mod.forget R).map_injective
  apply sub_eq_zero.mp
  have : ∀ i : Fin S.n, TopologicalSpace.NoetherianSpace (S.domain i) :=
    fun i ↦ (S.immersion i).isEmbedding.noetherianSpace
  have : ∀ i : Fin S.n, QuasiCompact (S.immersion i) := fun i ↦ inferInstance
  apply abDetectMaps S.immersion
  · intro x
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp
      (S.iUnion_stratum_eq_univ.symm ▸ Set.mem_univ x)
    exact ⟨i, (S.range_immersion i).symm ▸ hi⟩
  · intro i
    rw [Functor.map_sub, sub_eq_zero]
    exact congrArg (fun t ↦ t.hom) (h i)

private lemma continuousAlgCl_constructible_flat
    (ℓ : ℕ) [Fact ℓ.Prime] (X : Scheme.{u})
    [IsNoetherian X]
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj (PadicAlgCl ℓ)) X))
    (hM : IsConstantModelConstructible
      (Profinite.continuousMapRingObj (PadicAlgCl ℓ)) X M) :
    ObjectProperty.flat M := by
  classical
  let Λ := Profinite.continuousMapRingObj (PadicAlgCl ℓ)
  let R := condensedRingObj Λ X
  have : CompactSpace X := inferInstance
  have : QuasiSeparatedSpace X := inferInstance
  obtain ⟨S, hS⟩ := (show IsFiniteConstantStratified Λ X M by
    simpa only [IsConstantModelConstructible,
      if_pos (show CompactSpace X ∧ QuasiSeparatedSpace X from ⟨inferInstance, inferInstance⟩)]
      using hM)
  let F (i : Fin S.n) := (upperStar Ab.{u + 1} (S.immersion i)).mapMod R
  have hF (i : Fin S.n) : PreservesFiniteLimits (Mod.tensorLeft ((F i).obj M)) := by
    have : TopologicalSpace.NoetherianSpace (S.domain i) :=
      (S.immersion i).isEmbedding.noetherianSpace
    let φ := condensedPullbackHom Λ (S.immersion i)
    have hn := constantModel_lfp Λ _ _ (hS i)
    have hc : IsLocallyFinitelyPresented _
        ((Mod.comap (inv φ)).obj ((F i).obj M)) :=
      lfp_of_iso hn ((Mod.extendScalarsIsoComapInv φ).app ((F i).obj M))
    have hp := lfp_of_comap (inv φ) hc
    exact condensed_locally_free_tensor_preservesFiniteLimits _ _
      (locally_free_pullback_coeff Λ (continuousAlgCl_lf ℓ) (S.immersion i)
        ((F i).obj M) hp)
  have hf (i : Fin S.n) : (Mod.tensorLeft M ⋙ F i).PreservesMonomorphisms := by
    have := hF i
    have : PreservesFiniteLimits (F i) := inferInstance
    have : PreservesFiniteLimits (F i ⋙ Mod.tensorLeft ((F i).obj M)) :=
      comp_preservesFiniteLimits _ _
    have hm : (F i ⋙ Mod.tensorLeft ((F i).obj M)).PreservesMonomorphisms :=
      by infer_instance
    exact Functor.PreservesMonomorphisms.of_iso (pullTensorIso (S.immersion i) R M).symm
  have : (Mod.tensorLeft M).PreservesMonomorphisms := by
    constructor
    intro P Q f hf'
    constructor
    intro T a b hab
    apply stratified_map_eq S R
    intro i
    have := hf i
    have : Mono ((F i).map ((Mod.tensorLeft M).map f)) :=
      (Mod.tensorLeft M ⋙ F i).map_mono f
    apply (cancel_mono ((F i).map ((Mod.tensorLeft M).map f))).mp
    simpa only [Functor.map_comp] using congrArg ((F i).map) hab
  rw [ObjectProperty.flat_iff_preservesFiniteLimits]
  have : (Mod.tensorLeft M).Additive :=
    Functor.additive_of_iso (Mod.relativeTensorRightIso M).symm
  have := Functor.preservesHomology_of_preservesMonos_and_cokernels (Mod.tensorLeft M)
  have : PreservesFiniteLimits (Mod.tensorLeft M) :=
    Functor.preservesFiniteLimits_of_preservesHomology (Mod.tensorLeft M)
  have : PreservesFiniteLimits (MonoidalCategory.tensorRight M) :=
    preservesFiniteLimits_of_natIso (Mod.relativeTensorRightIso M)
  exact preservesFiniteLimits_of_natIso (BraidedCategory.tensorLeftIsoTensorRight M).symm

/-- Bounded constant-model constructible complexes over the full continuous-map
algebraic closure have finite Tor amplitude.

Source: blueprint main-20261015, sk-thm-sfb-proper-base-change, equality Dctf = Dbc
for rational coefficients; sk-def-sfb-constructible, finite Tor amplitude.
(blueprint: det-sf-comp-continuous-algcl-constructible-tor).

Proof: a locally finitely presented module over a totally disconnected normed field
is locally finite free. In a finite presentation, specialization preserves every
matrix entry and hence the corank; descent makes this corank locally constant.
Gaussian elimination then gives free cokernels on a pro-etale refinement. Apply this
to the universe lift of PadicAlgCl, using its continuous coefficient isomorphism.
On each constructible stratum, a finite constant local model is locally finitely
presented, hence locally finite free. Its tensor functor is exact. Pullback commutes
with tensor, and the finite jointly surjective family of stratum immersions detects
equality of maps. Thus the tensor functor on the original scheme preserves
monomorphisms, and right exactness makes every constructible module flat. Finally,
a bounded complex is an iterated extension of its shifted cohomology modules.
A flat module in degree zero has Tor amplitude [0,0]; finite Tor amplitude is
stable under shifts, isomorphisms and extensions. This also covers an empty scheme
and the zero complex. -/
theorem continuousAlgCl_bounded_finiteTor
    (ℓ : ℕ) [Fact ℓ.Prime] (X : Scheme.{u}) [IsNoetherian X]
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj (PadicAlgCl ℓ)) X)))
    (hK : constantModelBoundedConstructible
      (Profinite.continuousMapRingObj (PadicAlgCl ℓ)) X K) :
    DerivedCategory.finiteTorAmplitude _ K := by
  let Λ := Profinite.continuousMapRingObj (PadicAlgCl ℓ)
  let C := Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)
  let Q : ObjectProperty (DerivedCategory C) := DerivedCategory.finiteTorAmplitude C
  have : Q.IsTriangulated :=
    (constantModelConstructibleFiniteTor_wellDefined Λ X).2.2.2.2.2.2.2.1
  have : Q.IsClosedUnderIsomorphisms :=
    (constantModelConstructibleFiniteTor_wellDefined Λ X).2.2.2.1
  obtain ⟨d, hd⟩ := DerivedCategory.exists_iteratedExtensions_of_bounded
    (ObjectProperty.flat (A := C)) K hK.1
    (fun n ↦ continuousAlgCl_constructible_flat ℓ X _ (hK.2 n))
  apply DerivedCategory.iteratedExtensions_le (ObjectProperty.flat (A := C))
    (Q := Q) ?_ d K hd
  rintro L ⟨n, M, hM, ⟨e⟩⟩
  have h0 : DerivedCategory.finiteTorAmplitude C
      ((DerivedCategory.singleFunctor C 0).obj M) :=
    ⟨0, 0, DerivedCategory.torAmplitudeIn_singleFunctor_obj_of_flat hM⟩
  have hn : DerivedCategory.finiteTorAmplitude C
      (((DerivedCategory.singleFunctor C 0).obj M)⟦-n⟧) :=
    (DerivedCategory.finiteTorAmplitude C).le_shift (-n) _ h0
  exact (DerivedCategory.finiteTorAmplitude C).prop_of_iso
    (e ≪≫ (((DerivedCategory.singleFunctors C).shiftIso (-n) n 0 (by lia)).app M).symm).symm hn

end AlgebraicGeometry.ProEtale
