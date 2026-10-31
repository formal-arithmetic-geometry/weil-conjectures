/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.Algebra.Module.LocalizedModule.Away
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
import WeilConjectures.AlgebraicGeometry.FiniteLocallyFreeStructureSheaf
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
import Mathlib.RingTheory.Localization.Module

/-! # Principal fixed-rank bases for finite locally free affine algebras

Source: Stacks Project, Tags 02KB, 04MH, 01IA, 01HV, 00E0 and 00E8.
(blueprint: lem-a1-finite-locally-free-principal-basis-cover)
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry

variable (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]

/-- The actual structure-sheaf pushforward along the spectrum of the algebra map.
Source: Stacks Project, Tag 02KB.
(blueprint: lem-a1-finite-locally-free-principal-basis-cover) -/
noncomputable abbrev affineAlgebraStructurePushforward : (Spec (.of A)).Modules :=
  (Scheme.Modules.pushforward (Spec.map (CommRingCat.ofHom (algebraMap A B)))).obj
    (SheafOfModules.unit (Spec (.of B)).ringCatSheaf)

/-- The existing module localization, bundled with its canonical localized scalar action.
Source: Stacks Project, Tag 01IA, localization of an affine module.
(blueprint: lem-a1-finite-locally-free-principal-basis-cover) -/
noncomputable def affineAlgebraLocalizedModule (f : A) : ModuleCat (Localization.Away f) :=
  letI := LocalizedModule.moduleOfIsLocalization
    (S := Submonoid.powers f) (M := B) (T := Localization.Away f)
  ModuleCat.of (Localization.Away f) (LocalizedModule.Away f B)

private theorem finite_principal_cover (P : A → Prop)
    (h : ∀ x : PrimeSpectrum A, ∃ f : A, x ∈ PrimeSpectrum.basicOpen f ∧ P f) :
    ∃ (m : ℕ) (f : Fin m → A), Ideal.span (Set.range f) = ⊤ ∧
      (Subsingleton A → m = 0) ∧
      (∀ i, (PrimeSpectrum.basicOpen (f i) : Set (PrimeSpectrum A)).Nonempty) ∧
      ∀ i, P (f i) := by
  classical
  choose g hg hP using h
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun x : PrimeSpectrum A ↦ (PrimeSpectrum.basicOpen (g x) : Set (PrimeSpectrum A)))
    (fun _ ↦ (PrimeSpectrum.basicOpen _).isOpen)
    (fun x _ ↦ Set.mem_iUnion.mpr ⟨x, hg x⟩)
  let e := t.equivFin.symm
  refine ⟨t.card, fun i ↦ g (e i), ?_, ?_, ?_, fun i ↦ hP (e i)⟩
  · apply PrimeSpectrum.iSup_basicOpen_eq_top_iff.mp
    apply eq_top_iff.mpr
    intro x _
    obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ x))
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨e.symm ⟨y, hy⟩, by simpa using hxy⟩
  · intro hA
    have : IsEmpty (PrimeSpectrum A) := @PrimeSpectrum.instIsEmptyOfSubsingleton A _ hA
    exact Finset.card_eq_zero.mpr (Finset.eq_empty_iff_forall_notMem.mpr
      fun x _ ↦ isEmptyElim x)
  · intro i
    exact ⟨e i, hg (e i)⟩

private theorem principal_trivialization_at (M : (Spec (.of A)).Modules) (r : ℕ)
    [M.IsFiniteLocallyFreeOfRank r] (x : PrimeSpectrum A) :
    ∃ f : A, x ∈ PrimeSpectrum.basicOpen f ∧
      Nonempty (M.over (PrimeSpectrum.basicOpen f) ≅
        SheafOfModules.free (ULift.{u} (Fin r))) := by
  obtain ⟨I, V, hV, e⟩ :=
    SheafOfModules.isFiniteLocallyFreeOfRank_iff_exists_over_iso_free.{u, u, u}.1
      (inferInstance : M.IsFiniteLocallyFreeOfRank r)
  obtain ⟨i, hi⟩ := ((Opens.coversTop_iff _ _).1 hV).exists_mem x
  obtain ⟨_, ⟨f, rfl⟩, hxf, hf⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hi (V i).isOpen
  let j : PrimeSpectrum.basicOpen f ⟶ V i := homOfLE hf
  refine ⟨f, hxf, ⟨?_⟩⟩
  exact ((SheafOfModules.overFunctorMap _ j).app M).symm ≪≫
    (SheafOfModules.overMap _ j).mapIso (e i).some ≪≫
      (SheafOfModules.mapFreeIso (SheafOfModules.overMap _ j) _
        (SheafOfModules.overMapUnitIso j).symm).symm

private theorem basis_of_trivialization {X : Scheme.{u}} (M : X.Modules)
    {R N : Type u} [CommRing R] [AddCommGroup N] [Module R N]
    (U : X.Opens) (r : ℕ) (eR : R ≃+* Γ(X, U)) (eM : N ≃+ Γ(M, U))
    (h : ∀ (a : R) (z : N), eM (a • z) = eR a • eM z)
    (θ : SheafOfModules.free (ULift.{u} (Fin r)) ≅ M.over U) :
    ∃ b : Module.Basis (Fin r) R N, ∀ j : Fin r,
      θ.hom.val.app (op (Over.mk (𝟙 U)))
        ((SheafOfModules.ιFree (ULift.up j)).val.app (op (Over.mk (𝟙 U)))
          (@id Γ(X, U) 1)) = eM (b j) := by
  classical
  let W := op (Over.mk (𝟙 U))
  let E : Γ(M, U) ≃ₗ[Γ(X, U)] (ULift.{u} (Fin r) → Γ(X, U)) :=
    SheafOfModules.sectionsLinearEquivOfIsoFree θ.symm W
  let bS : Module.Basis (Fin r) Γ(X, U) Γ(M, U) :=
    ((Pi.basisFun Γ(X, U) (ULift.{u} (Fin r))).map E.symm).reindex Equiv.ulift
  let : Module R Γ(M, U) := Module.compHom _ eR.toRingHom
  let bR : Module.Basis (Fin r) R Γ(M, U) := bS.mapCoeffs eR.symm (by
    intro a z
    change eR (eR.symm a) • z = a • z
    rw [eR.apply_symm_apply])
  let L : N ≃ₗ[R] Γ(M, U) :=
    { eM with map_smul' := h }
  refine ⟨bR.map L.symm, fun j ↦ ?_⟩
  rw [Module.Basis.map_apply]
  change _ = L (L.symm (bR j))
  rw [L.apply_symm_apply]
  rw [show bR j = bS j from Module.Basis.mapCoeffs_apply _ _ _ _]
  dsimp only [bS]
  rw [Module.Basis.reindex_apply, Module.Basis.map_apply, Pi.basisFun_apply]
  change _ = E.symm (Pi.single (ULift.up j) 1)
  apply E.injective
  rw [E.apply_symm_apply]
  change SheafOfModules.freeSectionsLinearEquiv (ULift.{u} (Fin r)) W
    (θ.inv.val.app W (θ.hom.val.app W _)) = _
  rw [← ConcreteCategory.comp_apply, ← PresheafOfModules.comp_app, ← SheafOfModules.comp_val,
    θ.hom_inv_id]
  change SheafOfModules.freeSectionsLinearEquiv (ULift.{u} (Fin r)) W
    ((SheafOfModules.ιFree (R := X.ringCatSheaf.over U) (ULift.up j)).val.app W
      (@id Γ(X, U) 1)) = _
  ext k
  change (SheafOfModules.ιFree (R := X.ringCatSheaf.over U) (ULift.up j) ≫
    SheafOfModules.freeπ k).val.app W (@id Γ(X, U) 1) = _
  rw [SheafOfModules.ιFree_freeπ]
  by_cases hk : ULift.up j = k
  · subst k
    simp
  · rw [if_neg hk]
    change (0 : Γ(X, U)) =
      (Pi.single (ULift.up j) 1 : ULift.{u} (Fin r) → Γ(X, U)) k
    simp [Ne.symm hk]

private theorem localized_algebra_equiv (f : A) :
    ∃ eB : LocalizedModule.Away f B ≃+* Localization.Away (algebraMap A B f),
      ∀ (t : B) (n : ℕ),
        eB (LocalizedModule.mk t ⟨f ^ n, ⟨n, rfl⟩⟩) =
          IsLocalization.mk' (M := Submonoid.powers (algebraMap A B f))
            (Localization.Away (algebraMap A B f)) t
            ⟨(algebraMap A B f) ^ n, ⟨n, rfl⟩⟩ := by
  let C := Localization.Away (algebraMap A B f)
  let φ : B →ₐ[A] C := IsScalarTower.toAlgHom A B C
  have : IsLocalizedModule (.powers f) φ.toLinearMap :=
    IsLocalizedModule.restrictScalars_powers f (Algebra.linearMap B C)
  let E := IsLocalizedModule.iso (.powers f) φ.toLinearMap
  let e : LocalizedModule.Away f B ≃+* C :=
    { E.toAddEquiv with
      map_mul' := by
        intro x y
        induction x using LocalizedModule.induction_on with | h a s =>
          induction y using LocalizedModule.induction_on with | h b t =>
            rw [LocalizedModule.mk_mul_mk]
            exact (IsLocalizedModule.mk'_mul_mk' φ a b s t).symm }
  refine ⟨e, fun t n ↦ ?_⟩
  change IsLocalizedModule.mk' (S := .powers f) φ.toLinearMap t
    ⟨f ^ n, ⟨n, rfl⟩⟩ = _
  apply IsLocalizedModule.mk'_eq_iff.mpr
  change algebraMap B C t = (f ^ n) • _
  rw [Algebra.smul_def, IsScalarTower.algebraMap_apply A B C, map_pow]
  exact (IsLocalization.mk'_spec' (M := .powers (algebraMap A B f)) C t
    ⟨(algebraMap A B f) ^ n, ⟨n, rfl⟩⟩).symm

private theorem localized_sections_equiv (f : A) :
    ∃ (eR : Localization.Away f ≃+* Γ(Spec (.of A), PrimeSpectrum.basicOpen f))
      (eM : LocalizedModule.Away f B ≃+
        Γ(affineAlgebraStructurePushforward A B, PrimeSpectrum.basicOpen f)),
      (∀ a : A, eR (algebraMap A (Localization.Away f) a) =
        (Spec (.of A)).presheaf.map (homOfLE le_top).op
          ((Scheme.ΓSpecIso (.of A)).inv.hom a)) ∧
      (∀ (a : Localization.Away f) (z : affineAlgebraLocalizedModule A B f),
        eM (a • z) = eR a • eM z) ∧
      (∀ (t : B) (n : ℕ),
        eM (LocalizedModule.mk t ⟨f ^ n, ⟨n, rfl⟩⟩) =
          eR (IsLocalization.Away.invSelf (S := Localization.Away f) f) ^ n •
            (@id Γ(affineAlgebraStructurePushforward A B, PrimeSpectrum.basicOpen f)
              ((Spec (.of B)).presheaf.map (homOfLE le_top).op
                ((Scheme.ΓSpecIso (.of B)).inv.hom t)))) := by
  let U := PrimeSpectrum.basicOpen f
  let C : Type u := Γ(Spec (.of B), PrimeSpectrum.basicOpen (algebraMap A B f))
  let : Algebra B C := StructureSheaf.openAlgebra B
    (op (PrimeSpectrum.basicOpen (algebraMap A B f)))
  have : IsLocalization.Away (algebraMap A B f) C :=
    StructureSheaf.IsLocalization.to_basicOpen B (algebraMap A B f)
  let : Algebra A Γ(Spec (.of A), U) := StructureSheaf.openAlgebra A (op U)
  have : IsLocalization.Away f Γ(Spec (.of A), U) :=
    StructureSheaf.IsLocalization.to_basicOpen A f
  let : Algebra A C := ((algebraMap B C).comp (algebraMap A B)).toAlgebra
  have : IsScalarTower A B C := IsScalarTower.of_algebraMap_eq (fun _ ↦ rfl)
  let φ : B →ₐ[A] C := IsScalarTower.toAlgHom A B C
  have : IsLocalizedModule (.powers f) φ.toLinearMap :=
    IsLocalizedModule.restrictScalars_powers f (Algebra.linearMap B C)
  let E := IsLocalizedModule.iso (.powers f) φ.toLinearMap
  let eR := (IsLocalization.algEquiv (.powers f) (Localization.Away f)
    Γ(Spec (.of A), U)).toRingEquiv
  let p := Spec.map (CommRingCat.ofHom (algebraMap A B))
  let q : Γ(Spec (.of A), U) →+* C := (p.app U).hom
  let α : Localization.Away f →+* C := q.comp eR.toRingHom
  have hα (a : A) : α (algebraMap A (Localization.Away f) a) = algebraMap A C a := by
    change (p.app U).hom (eR (algebraMap A (Localization.Away f) a)) = _
    rw [show eR (algebraMap A (Localization.Away f) a) =
      algebraMap A Γ(Spec (.of A), U) a from
        (IsLocalization.algEquiv (.powers f) (Localization.Away f) _).commutes a]
    exact congr($(StructureSheaf.toOpen_comp_comap (algebraMap A B) U).hom a)
  let : Module (Localization.Away f) C := Module.compHom C α
  have : IsScalarTower A (Localization.Away f) C :=
    IsScalarTower.of_algebraMap_smul (fun a z ↦ by
      change α (algebraMap A (Localization.Away f) a) * z = a • z
      rw [hα, Algebra.smul_def])
  let : Module (Localization.Away f) (LocalizedModule.Away f B) :=
    LocalizedModule.moduleOfIsLocalization
  let L := E.extendScalarsOfIsLocalization (.powers f) (Localization.Away f)
  refine ⟨eR, E.toAddEquiv, ?_, ?_, ?_⟩
  · intro a
    exact (IsLocalization.algEquiv (.powers f) (Localization.Away f) _).commutes a
  · intro a z
    exact L.map_smul a z
  · intro t n
    let a := IsLocalization.Away.invSelf (S := Localization.Away f) f
    let z : C := E (LocalizedModule.mk t ⟨f ^ n, ⟨n, rfl⟩⟩)
    have hz : algebraMap A C (f ^ n) * z = φ t := by
      have H : φ.toLinearMap t =
          (⟨f ^ n, ⟨n, rfl⟩⟩ : Submonoid.powers f) • z :=
        (IsLocalizedModule.mk'_eq_iff (f := φ.toLinearMap)).mp rfl
      exact (Algebra.smul_def (f ^ n) z).symm.trans H.symm
    have hinv : algebraMap A C f * α a = 1 := by
      rw [← hα f, ← map_mul]
      exact (congrArg α (IsLocalization.Away.mul_invSelf
        (S := Localization.Away f) f)).trans (map_one α)
    have hp : algebraMap A C (f ^ n) * α (a ^ n) = 1 := by
      rw [map_pow, map_pow, ← mul_pow, hinv, one_pow]
    have hu : IsUnit (algebraMap A C (f ^ n)) := by
      rw [IsScalarTower.algebraMap_apply A B C, map_pow]
      exact IsLocalization.map_units C
        (⟨(algebraMap A B f) ^ n, ⟨n, rfl⟩⟩ :
          Submonoid.powers (algebraMap A B f))
    have hz' : z = α (a ^ n) * φ t := by
      apply hu.mul_left_cancel
      rw [hz, ← mul_assoc, hp, one_mul]
    change z = q (eR a ^ n) * φ t
    calc
      z = α (a ^ n) * φ t := hz'
      _ = (α a) ^ n * φ t := by rw [map_pow]
      _ = _ := by rw [map_pow]; rfl

/-- A finite locally free affine algebra of degree `r` has a finite principal basis cover,
with its canonical localization maps and the induced sheaf trivializations.
Source: Stacks Project, Tags 02KB, 04MH, 01IA, 01HV, 00E0 and 00E8.
(blueprint: lem-a1-finite-locally-free-principal-basis-cover)

Proof:
1. Apply lem-pc-flf-properties to the spectrum morphism. Its degree hypothesis gives
   local freeness of rank r. By def-amb-finite-locally-free-module this also gives
   quasi-coherence and local trivializations by r copies of the structure sheaf.
2. Use structure-sheaf localization on D(f) and its inverse image D(phi(f)).
   Restrict the localization of B at phi(f) along A → B: its canonical map is an
   A-module localization at f. The universal property gives the additive section
   equivalence and the ring equivalence with B[1/phi(f)]. Compatibility of constant
   sections and extension of scalars to A_f give linearity. The identity
   t/f^n = f^(-n) • (t/1) gives the fraction formulas.
3. Refine the trivializing opens by nonempty principal opens using
   lem-weil-pbc-spec-localization-away-basic-open. Compactness and the unit-ideal
   criterion in lem-weil-pbc-spec-basic-opens-unit-ideal-quasi-compact give a finite
   subcover with span equal to the unit ideal. If A is zero, unitality makes B zero
   and the empty cover suffices.
4. Take the coordinate sections of each restricted trivialization back through the
   canonical module isomorphism. They give a basis indexed by Fin r. Linearity on
   every subopen identifies the resulting sheaf map with the original trivialization.
   For r=0 all coordinate families and sums are empty, giving the zero module sheaf. -/
theorem finiteLocallyFree_principalBasisCover (r : ℕ)
    [(Spec.map (CommRingCat.ofHom (algebraMap A B))).IsFiniteLocallyFreeOfDegree r] :
    (affineAlgebraStructurePushforward A B).IsQuasicoherent ∧
    SheafOfModules.IsFiniteLocallyFreeOfRank (affineAlgebraStructurePushforward A B) r ∧
    (Subsingleton A → Subsingleton B) ∧
    ∃ (m : ℕ) (f : Fin m → A),
      Ideal.span (Set.range f) = ⊤ ∧
      (Subsingleton A → m = 0) ∧
      (Nontrivial A → ∀ i, (PrimeSpectrum.basicOpen (f i) : Set (PrimeSpectrum A)).Nonempty) ∧
      ∀ i : Fin m,
        ∃ (b : Module.Basis (Fin r) (Localization.Away (f i))
            (affineAlgebraLocalizedModule A B (f i)))
          (eR : Localization.Away (f i) ≃+*
            Γ(Spec (.of A), PrimeSpectrum.basicOpen (f i)))
          (eM : LocalizedModule.Away (f i) B ≃+
            Γ(affineAlgebraStructurePushforward A B, PrimeSpectrum.basicOpen (f i)))
          (eB : LocalizedModule.Away (f i) B ≃+* Localization.Away (algebraMap A B (f i)))
          (θ : SheafOfModules.free (ULift.{u} (Fin r)) ≅
            (affineAlgebraStructurePushforward A B).over (PrimeSpectrum.basicOpen (f i))),
          (∀ a : A, eR (algebraMap A (Localization.Away (f i)) a) =
            (Spec (.of A)).presheaf.map (homOfLE le_top).op
              ((Scheme.ΓSpecIso (.of A)).inv.hom a)) ∧
          (∀ (a : Localization.Away (f i)) (z : affineAlgebraLocalizedModule A B (f i)),
            eM (a • z) = eR a • eM z) ∧
          (∀ (t : B) (n : ℕ),
            eM (LocalizedModule.mk t ⟨(f i) ^ n, ⟨n, rfl⟩⟩) =
              eR (IsLocalization.Away.invSelf (S := Localization.Away (f i)) (f i)) ^ n •
                (@id Γ(affineAlgebraStructurePushforward A B, PrimeSpectrum.basicOpen (f i))
                  ((Spec (.of B)).presheaf.map (homOfLE le_top).op
                    ((Scheme.ΓSpecIso (.of B)).inv.hom t)))) ∧
          (∀ (t : B) (n : ℕ),
            eB (LocalizedModule.mk t ⟨(f i) ^ n, ⟨n, rfl⟩⟩) =
              IsLocalization.mk' (M := Submonoid.powers (algebraMap A B (f i)))
                (Localization.Away (algebraMap A B (f i))) t
                ⟨(algebraMap A B (f i)) ^ n, ⟨n, rfl⟩⟩) ∧
          (∀ j : Fin r,
            θ.hom.val.app (op (Over.mk (𝟙 (PrimeSpectrum.basicOpen (f i)))))
              ((SheafOfModules.ιFree (ULift.up j)).val.app
                (op (Over.mk (𝟙 (PrimeSpectrum.basicOpen (f i)))))
                (@id Γ(Spec (.of A), PrimeSpectrum.basicOpen (f i)) 1)) = eM (b j)) := by
  have hRank := (finiteLocallyFree_structureSheaf_properties
    (Spec.map (CommRingCat.ofHom (algebraMap A B))) r).1
  have : (affineAlgebraStructurePushforward A B).IsFiniteLocallyFreeOfRank r := hRank
  have := SheafOfModules.IsFiniteLocallyFreeOfRank.isLocallyFree
    (affineAlgebraStructurePushforward A B) r
  refine ⟨inferInstance, hRank, ?_, ?_⟩
  · intro hA
    let := hA
    exact Algebra.subsingleton A B
  · obtain ⟨m, f, hspan, hzero, hnonempty, hθ⟩ := finite_principal_cover A
      (fun f ↦ Nonempty ((affineAlgebraStructurePushforward A B).over
        (PrimeSpectrum.basicOpen f) ≅ SheafOfModules.free (ULift.{u} (Fin r))))
      (principal_trivialization_at A (affineAlgebraStructurePushforward A B) r)
    refine ⟨m, f, hspan, hzero, fun _ ↦ hnonempty, fun i ↦ ?_⟩
    obtain ⟨eR, eM, hR, hlin, hfrac⟩ := localized_sections_equiv A B (f i)
    obtain ⟨eB, hB⟩ := localized_algebra_equiv A B (f i)
    let θ := (hθ i).some.symm
    obtain ⟨b, hb⟩ := basis_of_trivialization (N := affineAlgebraLocalizedModule A B (f i))
      (affineAlgebraStructurePushforward A B)
      (PrimeSpectrum.basicOpen (f i)) r eR eM hlin θ
    exact ⟨b, eR, eM, eB, θ, hR, hlin, hfrac, hB, hb⟩

end AlgebraicGeometry
