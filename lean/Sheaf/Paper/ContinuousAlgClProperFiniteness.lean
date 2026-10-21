/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F4
-/
module

public import Sheaf.SixFunctors.ProperImageLocalizingProper
import Sheaf.Paper.ContinuousAlgClProperHeartFiniteness
import Sheaf.Paper.ContinuousAlgClLocalFree
import Sheaf.Paper.ConstantModelTorAmplitude
import all Sheaf.Paper.CoefficientHeartClosure
import all Sheaf.Paper.CoefficientHeartLisseRestriction
import all Sheaf.AlgebraicGeometry.CondensedConstructibleSerre
import WeilConjectures.CategoryTheory.DerivedCategory.BoundedEssentiallySmall
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologyProperty

/-!
# Proper direct image for the continuous-map algebraic-closure coefficient

Source: blueprint main-20261015, det-sf-comp-coherence-single, proper-image paragraph.
(blueprint: det-sf-comp-continuous-algcl-finiteness).
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry Scheme
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.CondensedRing

attribute [local irreducible] CategoryTheory.Functor.rightDerivedFunctor
  CategoryTheory.Functor.mapDerivedCategory DerivedCategory.monoidalClosed
  CategoryTheory.Mod.monoidalClosed upperStarFromPoint

private theorem constructible_iff_of_locally_free
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (hLF : ∀ (Y : Scheme.{u}) [TopologicalSpace.NoetherianSpace Y]
      (M : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)),
      IsLocallyFinitelyPresented (condensedRingObj Λ Y) M →
      ∃ U : Scheme.Cover.{u} Scheme.proetalePrecoverage Y, ∀ i,
        Mod.IsFree
          ((AlgebraicGeometry.ProEtale.upperStar Ab.{u + 1} (U.f i)).obj (condensedRingObj Λ Y))
          (((AlgebraicGeometry.ProEtale.upperStar Ab.{u + 1} (U.f i)).mapMod
            (condensedRingObj Λ Y)).obj M))
    (X : Scheme.{u}) [IsNoetherian X]
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    IsConstantModelConstructible Λ X M ↔
      IsConstructibleModuleObject (condensedRingObj Λ X) M := by
  rw [IsConstantModelConstructible, if_pos ⟨inferInstance, inferInstance⟩]
  constructor
  · rintro ⟨S, hS⟩
    refine ⟨S, fun a ↦ ?_⟩
    let φ := condensedPullbackHom Λ (S.immersion a)
    have h := constantModel_lfp Λ _ _ (hS a)
    exact lfp_of_comap (inv φ)
      (lfp_of_iso h ((Mod.extendScalarsIsoComapInv φ).app _))
  · rintro ⟨S, hS⟩
    refine ⟨S, fun a ↦ ?_⟩
    have : TopologicalSpace.NoetherianSpace (S.domain a) :=
      (S.immersion a).isEmbedding.noetherianSpace
    let φ := condensedPullbackHom Λ (S.immersion a)
    have h := lfp_of_iso (lfp_comap (inv φ) (hS a))
      ((Mod.extendScalarsIsoComapInv φ).app _).symm
    exact heart_free_model Λ _ (heart_lisse_of_free Λ (hLF _ _ h))

/-- Proper finiteness for bounded complexes over the full continuous-map algebraic closure.

Source: blueprint main-20261015, sk-thm-sfb-proper-base-change, assertion (1),
as used in the proper-image paragraph of det-sf-comp-coherence-single.
(blueprint: det-sf-comp-continuous-algcl-finiteness).

Proof: the generic local finite-free argument for this coefficient identifies finite
constant-model constructibility with stratified local finite presentation. The generic
Serre argument then gives kernel, cokernel and extension closure. Hence the complexes
on the target with constructible cohomology form a triangulated replete subcategory.
Its inverse image under the triangulated proper derived pushforward is triangulated
and replete. The proper-heart theorem puts each constructible sheaf in this inverse
image. It contains every bounded complex with constructible cohomology by the finite
Postnikov filtration: its factors are shifts of its cohomology sheaves. Convert the
output cohomology back to finite constant models. Empty schemes and zero complexes
are included. Bounds and finite Tor amplitude are supplied separately; this theorem
only asserts constructibility of each output cohomology object. -/
theorem continuousAlgCl_proper_finiteness
    (ℓ : ℕ) [Fact ℓ.Prime]
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))] [IsSeparated (Y ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    (p : X ⟶ Y) [p.IsOver (Spec (.of k))] [IsProper p]
    (K : ConstantModelConstructibleFiniteTor
      (Profinite.continuousMapRingObj (PadicAlgCl ℓ)) X) :
    ∀ n : ℤ, IsConstantModelConstructible
      (Profinite.continuousMapRingObj (PadicAlgCl ℓ)) Y
      ((DerivedCategory.homologyFunctor _ n).obj
        ((lowerStar (Profinite.continuousMapRingObj (PadicAlgCl ℓ)) p).rightDerivedFunctor.obj
          K.obj)) := by
  let Λ := Profinite.continuousMapRingObj (PadicAlgCl ℓ)
  let C := Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)
  let D := Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)
  let F : DerivedCategory C ⥤ DerivedCategory D := (lowerStar Λ p).rightDerivedFunctor
  have : IsLocallyNoetherian Y :=
    LocallyOfFiniteType.isLocallyNoetherian (Y ↘ Spec (.of k))
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (Y ↘ Spec (.of k))
  have : IsNoetherian Y := ⟨⟩
  let P : ObjectProperty D := IsConstructibleModuleObject (condensedRingObj Λ Y)
  have hserre := condensed_constructible_serre_of_locally_free
    freeEpiLocalSplitting Λ (continuousAlgCl_lf ℓ) Y
  obtain ⟨he, hk, hc⟩ := heart_closure_classes P
    (fun e h ↦ heart_constructible_iso e h)
    (fun f hM hN ↦ (hserre.1 _ _ f hM hN).1)
    (fun f hM hN ↦ (hserre.1 _ _ f hM hN).2)
    (fun S hS hM hN ↦ hserre.2 S hS hM hN)
  have : P.IsClosedUnderExtensions := he
  have : P.IsClosedUnderKernels := hk
  have : P.IsClosedUnderCokernels := hc
  have : P.IsClosedUnderIsomorphisms := ⟨fun e h ↦ heart_constructible_iso e h⟩
  have : P.ContainsZero := by
    obtain ⟨Z, hZ⟩ := (inferInstance : HasZeroObject D).zero
    exact ⟨⟨Z, hZ, heart_constructible_zero Z hZ⟩⟩
  let Q := DerivedCategory.homologyProperty P
  have : Q.IsTriangulated := inferInstance
  have : Q.IsClosedUnderIsomorphisms := inferInstance
  let R := Q.inverseImage F
  have := (constantModelConstructibleFiniteTor_wellDefined Λ X).1
  obtain ⟨d, hd⟩ := DerivedCategory.exists_iteratedExtensions_of_bounded
    (IsConstantModelConstructible Λ X) K.obj K.property.1.1 K.property.1.2
  have hR : R K.obj := by
    apply DerivedCategory.iteratedExtensions_le (IsConstantModelConstructible Λ X)
      (Q := R) ?_ d K.obj hd
    rintro L ⟨n, M, hM, ⟨e⟩⟩
    have h0 : R ((DerivedCategory.singleFunctor C 0).obj M) := by
      intro q
      exact (constructible_iff_of_locally_free Λ (continuousAlgCl_lf ℓ) Y _).mp
        (continuousAlgCl_proper_heart_finiteness ℓ k p ⟨M, hM⟩ q)
    have hn := R.le_shift (-n) _ h0
    let i := e ≪≫ (((DerivedCategory.singleFunctors C).shiftIso (-n) n 0 (by lia)).app M).symm
    exact R.prop_of_iso i.symm hn
  intro n
  exact (constructible_iff_of_locally_free Λ (continuousAlgCl_lf ℓ) Y _).mpr (hR n)

end AlgebraicGeometry.ProEtale.CondensedRing
