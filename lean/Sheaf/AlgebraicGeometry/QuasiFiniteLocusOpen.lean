/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF groups J1 and Z8
-/
module

public import Sheaf.AlgebraicGeometry.QuasiFiniteMorphism
import Sheaf.RingTheory.QuasiFiniteLocusOpen
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import WeilConjectures.AlgebraicGeometry.IsolatedFiberPointQuasiFiniteAffinePairs

/-!
# Openness of the quasi-finite locus

Source: Stacks Project, Morphisms of Schemes, Tag 01TI
(blueprint: lem-sc-quasi-finite-points-open).
-/

@[expose] public section

universe u

open CategoryTheory
namespace AlgebraicGeometry.Scheme.Hom

private theorem finiteType_affinePair {X S : Scheme.{u}} (f : X ⟶ S)
    (U : X.Opens) (V : S.Opens) (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (e : U ≤ f ⁻¹ᵁ V) (hft : (f.appLE V U e).hom.FiniteType) :
    LocallyOfFiniteType (f.resLE V U e) := by
  let : IsAffine U.toScheme := hU
  let : IsAffine V.toScheme := hV
  rw [HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFiniteType)]
  exact (RingHom.finiteType_respectsIso.arrow_mk_iso_iff
    (arrowResLEAppIso f V U e)).mpr hft

private theorem atPoint_quasiFiniteAt {X S : Scheme.{u}} (f : X ⟶ S) (x : X)
    (hfx : IsQuasiFiniteAtPoint f x) : f.QuasiFiniteAt x := by
  obtain ⟨U, hx, hU, V, hV, e, hft, hq⟩ := hfx
  let := (f.appLE V U e).hom.toAlgebra
  let := hft
  let q := hU.primeIdealOf ⟨x, hx⟩
  let p := q.comap (algebraMap Γ(S, V) Γ(X, U))
  let H := PrimeSpectrum.preimageHomeomorphFiber Γ(S, V) Γ(X, U) p
  have ho : IsOpen ({⟨q, rfl⟩} : Set
      (PrimeSpectrum.comap (algebraMap Γ(S, V) Γ(X, U)) ⁻¹' {p})) := by
    rw [← H.isOpen_image, Set.image_singleton]
    exact hq
  have hqa : Algebra.QuasiFiniteAt Γ(S, V) q.asIdeal :=
    Algebra.QuasiFiniteAt.of_isOpen_singleton_fiber q ho
  rw [QuasiFiniteAt,
    RingHom.QuasiFinite.respectsIso.arrow_mk_iso_iff
      (IsAffineOpen.arrowStalkMapIso f V hV U hU e hx)]
  apply RingHom.QuasiFinite.of_comp
    (g := algebraMap Γ(S, V)
      (Localization.AtPrime (hV.primeIdealOf ⟨f x, e hx⟩).asIdeal))
  have heq : (Localization.localRingHom _ _ (f.appLE V U e).hom
      congr($(IsAffineOpen.comap_primeIdealOf_appLE V hV U hU e hx).1).symm).comp
      (algebraMap Γ(S, V)
        (Localization.AtPrime (hV.primeIdealOf ⟨f x, e hx⟩).asIdeal)) =
      algebraMap Γ(S, V) (Localization.AtPrime q.asIdeal) := by
    ext a
    simp only [RingHom.comp_apply, Localization.localRingHom_to_map]
    rfl
  exact heq.symm ▸ RingHom.quasiFinite_algebraMap.mpr hqa

private theorem atPoint_of_quasiFiniteAt {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] (x : X) (hx : f.QuasiFiniteAt x) :
    IsQuasiFiniteAtPoint f x := by
  obtain ⟨V, hV, hyV, _⟩ := exists_isAffineOpen_mem_and_subset
    (X := S) (x := f x) (U := ⊤) (by trivial)
  obtain ⟨U, hU, hxU, hUV⟩ := exists_isAffineOpen_mem_and_subset
    (X := X) (x := x) (U := f ⁻¹ᵁ V) hyV
  exact ⟨U, hxU, hU, V, hV, hUV,
    isQuasiFiniteAtPrime_of_isOpen_singleton_asFiber f x
      (quasiFiniteAt_iff_isOpen_singleton_asFiber.mp hx) U V hU hV hxU hUV⟩

private theorem finiteType_on_locus {X S : Scheme.{u}} (f : X ⟶ S) (T : X.Opens)
    (hT : ∀ x : T, IsQuasiFiniteAtPoint f x.1) : LocallyOfFiniteType (T.ι ≫ f) := by
  let : MorphismProperty.Respects (@LocallyOfFiniteType) (@IsOpenImmersion) :=
    HasRingHomProperty.respects_isOpenImmersion
      (RingHom.finiteType_stableUnderComposition.stableUnderCompositionWithLocalizationAway
        RingHom.finiteType_holdsForLocalizationAway).left
  apply IsZariskiLocalAtSource.iff_exists_resLE.mpr
  intro x
  obtain ⟨U, hx, hU, V, hV, e, hft, _⟩ := hT x
  let := (f.appLE V U e).hom.toAlgebra
  let O : T.toScheme.Opens := T.ι ⁻¹ᵁ U
  let j := T.ι.resLE U O le_rfl
  have hj : IsOpenImmersion j := by dsimp [j]; unfold resLE; infer_instance
  have hf : LocallyOfFiniteType (f.resLE V U e) :=
    finiteType_affinePair f U V hU hV e hft
  have ej : O ≤ (T.ι ≫ f) ⁻¹ᵁ V := fun _ h ↦ e h
  refine ⟨V, O, hx, ej, ?_⟩
  have heq : (T.ι ≫ f).resLE V O ej = j ≫ f.resLE V U e := by
    apply (cancel_mono V.ι).mp
    simp only [Category.assoc, resLE_comp_ι]
    simp only [j, ← Category.assoc, resLE_comp_ι]
  rw [heq]
  infer_instance

/-- The quasi-finite locus of a morphism is open, and the induced morphism on it is
locally quasi-finite (Stacks Project, Morphisms of Schemes, Tag 01TI).
(blueprint: lem-sc-quasi-finite-points-open)

Proof:
1. At a quasi-finite point, unpack the affine source and target neighbourhoods in
   Definition 01TD. The ring-level quasi-finite locus is open by Tag 00QA.
2. Its image under the affine chart is open in the source, contains the chosen
   point, and consists of quasi-finite points, using the same affine pair.
   Therefore the whole locus is open.
3. The induced morphism on this open locus is locally of finite type: around
   each point, restrict its original finite-type affine pair to the locus.
4. The affine witness gives quasi-finiteness of the stalk map. This property
   transfers across the open inclusion of the locus. The isolated-fibre
   criterion and Tag 01TH recover Definition 01TD for the induced morphism. -/
theorem isOpen_quasiFiniteAtPoint {X S : Scheme.{u}} (f : X ⟶ S) :
    ∃ U : X.Opens,
      (∀ x : X, x ∈ U ↔ IsQuasiFiniteAtPoint f x) ∧
        IsLocallyQuasiFinite (U.ι ≫ f) := by
  have hopen : IsOpen {x : X | IsQuasiFiniteAtPoint f x} := by
    rw [isOpen_iff_forall_mem_open]
    intro x hx
    obtain ⟨U, hxU, hU, V, hV, e, hft, hq⟩ := hx
    let := (f.appLE V U e).hom.toAlgebra
    let := hft
    let L := {q : PrimeSpectrum Γ(X, U) |
      Algebra.IsQuasiFiniteAtPrime Γ(S, V) Γ(X, U) q}
    have hL : IsOpen L := (Algebra.isOpen_isQuasiFiniteAtPrime Γ(S, V) Γ(X, U)).1
    refine ⟨hU.fromSpec '' L, ?_, hU.fromSpec.isOpenEmbedding.isOpenMap _ hL, ?_⟩
    · rintro y ⟨q, hq, rfl⟩
      have hy : hU.fromSpec q ∈ U := by
        change hU.fromSpec q ∈ (U : Set X)
        rw [← hU.range_fromSpec]
        exact ⟨q, rfl⟩
      refine ⟨U, hy, hU, V, hV, e, hft, ?_⟩
      have heq : hU.primeIdealOf ⟨hU.fromSpec q, hy⟩ = q :=
        hU.fromSpec.injective (hU.fromSpec_primeIdealOf _)
      rw [heq]
      exact hq
    · exact ⟨hU.primeIdealOf ⟨x, hxU⟩, hq, hU.fromSpec_primeIdealOf _⟩
  let T : X.Opens := ⟨_, hopen⟩
  refine ⟨T, fun _ ↦ Iff.rfl, ?_⟩
  have : LocallyOfFiniteType (T.ι ≫ f) := finiteType_on_locus f T fun x ↦ x.2
  intro x
  apply atPoint_of_quasiFiniteAt
  rw [quasiFiniteAt_comp_iff_of_isOpenImmersion]
  exact atPoint_quasiFiniteAt f x.1 x.2

end AlgebraicGeometry.Scheme.Hom
