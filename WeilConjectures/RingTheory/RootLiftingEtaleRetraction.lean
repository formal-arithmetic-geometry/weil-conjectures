/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Unramified.LocalStructure

/-!
# Étale retractions from simple-root lifting

A local ring in which simple roots of monic polynomials over the residue field lift admits a
unique retraction from an étale algebra through a prime with trivial residue field extension.

## References

* [Stacks, Tag 04GG], implication (1) ⇒ (8)
* [Stacks, Tag 00UE]
* [Stacks, Tag 06RR]
-/

@[expose] public section

universe u

open AlgebraicGeometry

namespace IsLocalRing

open CategoryTheory in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- A prime over the closed point with trivial scheme residue-field extension gives an
R-algebra map to the residue field with that prime as its kernel. -/
private theorem exists_algHom_residueField_of_bijective_spec_residueFieldMap
    {R S : Type u} [CommRing R] [CommRing S] [IsLocalRing R] [Algebra R S]
    (q : Ideal S) [q.IsPrime]
    (hq : q.comap (algebraMap R S) = maximalIdeal R)
    (hres : Function.Bijective
      ((Spec.map (CommRingCat.ofHom (algebraMap R S))).residueFieldMap
        (⟨q, inferInstance⟩ : Spec (.of S))).hom) :
    ∃ ρ : S →ₐ[R] ResidueField R, RingHom.ker ρ.toRingHom = q := by
  classical
  let x : PrimeSpectrum S := ⟨q, inferInstance⟩
  let f := Spec.map (CommRingCat.ofHom (algebraMap R S))
  let y : PrimeSpectrum R := f x
  let β : S →+* (Spec (.of S)).residueField x :=
    (Scheme.Spec.residueFieldIso (.of S) x).inv.hom.comp (algebraMap S q.ResidueField)
  let α : R →+* (Spec (.of R)).residueField y :=
    (Scheme.Spec.residueFieldIso (.of R) y).inv.hom.comp
      (algebraMap R y.asIdeal.ResidueField)
  have hnat : β.comp (algebraMap R S) = (f.residueFieldMap x).hom.comp α := by
    have hn : CommRingCat.ofHom (algebraMap R S) ≫
        (CommRingCat.ofHom (algebraMap S q.ResidueField) ≫
          (Scheme.Spec.residueFieldIso (.of S) x).inv) =
        (CommRingCat.ofHom (algebraMap R y.asIdeal.ResidueField) ≫
          (Scheme.Spec.residueFieldIso (.of R) y).inv) ≫ f.residueFieldMap x := by
      erw [Scheme.Spec.algebraMap_residueFieldIso_inv,
        Scheme.Spec.algebraMap_residueFieldIso_inv]
      change CommRingCat.ofHom (algebraMap R S) ≫
        ((Scheme.ΓSpecIso (.of S)).inv ≫ (Spec (.of S)).Γevaluation x) =
        ((Scheme.ΓSpecIso (.of R)).inv ≫ (Spec (.of R)).Γevaluation y) ≫
          f.residueFieldMap x
      simp only [CategoryTheory.Category.assoc, Scheme.ΓSpecIso_inv_naturality_assoc]
      erw [Scheme.Γevaluation_naturality f x]
    exact congrArg (fun h : CommRingCat.of R ⟶ (Spec (.of S)).residueField x ↦ h.hom) hn
  have hy : y.asIdeal = maximalIdeal R := hq
  have hym : y.asIdeal.IsMaximal := hy ▸ inferInstance
  have hα : Function.Surjective α :=
    (Scheme.Spec.residueFieldIso (.of R) y).commRingCatIsoToRingEquiv.symm.surjective.comp
      y.asIdeal.algebraMap_residueField_surjective
  let γ : R →+* (Spec (.of S)).residueField x := β.comp (algebraMap R S)
  have hγ : Function.Surjective γ := by
    rw [show γ = (f.residueFieldMap x).hom.comp α from hnat]
    exact hres.2.comp hα
  have hβker : RingHom.ker β = q := by
    ext s
    change (Scheme.Spec.residueFieldIso (.of S) x).inv.hom
      (algebraMap S q.ResidueField s) = 0 ↔ s ∈ q
    erw [(Scheme.Spec.residueFieldIso (.of S) x).commRingCatIsoToRingEquiv.symm.map_eq_zero_iff]
    exact Ideal.algebraMap_residueField_eq_zero
  have hγker : RingHom.ker γ = maximalIdeal R := by
    change (RingHom.ker β).comap (algebraMap R S) = maximalIdeal R
    rw [hβker, hq]
  have hinj : Function.Injective (Ideal.Quotient.lift (maximalIdeal R) γ hγker.ge) :=
    (Ideal.injective_lift_iff _).mpr hγker
  let e : ResidueField R ≃+* (Spec (.of S)).residueField x :=
    RingEquiv.ofBijective (Ideal.Quotient.lift (maximalIdeal R) γ hγker.ge)
      ⟨hinj, Ideal.Quotient.lift_surjective_of_surjective _ _ hγ⟩
  let ρ : S →ₐ[R] ResidueField R :=
    { e.symm.toRingHom.comp β with
      commutes' := by
        intro r
        apply e.injective
        change e (e.symm (β (algebraMap R S r))) = e (algebraMap R (ResidueField R) r)
        rw [e.apply_symm_apply]
        change β (algebraMap R S r) =
          Ideal.Quotient.lift (maximalIdeal R) γ hγker.ge
            (Ideal.Quotient.mk (maximalIdeal R) r)
        rfl }
  refine ⟨ρ, ?_⟩
  ext s
  change e.symm (β s) = 0 ↔ s ∈ q
  rw [e.symm.map_eq_zero_iff]
  exact Ideal.ext_iff.mp hβker s

/-- A residue-field map from a standard étale algebra has a unique lift to R. -/
private theorem standardEtale_unique_lift
    {R : Type u} [CommRing R] [IsLocalRing R]
    (hroot : ∀ f : Polynomial R, f.Monic → ∀ a₀ : ResidueField R,
      Polynomial.aeval a₀ f = 0 → Polynomial.aeval a₀ f.derivative ≠ 0 →
        ∃ a : R, f.IsRoot a ∧ residue R a = a₀)
    (P : StandardEtalePair R) (ρ : P.Ring →ₐ[R] ResidueField R) :
    ∃! σ : P.Ring →ₐ[R] R,
      (IsScalarTower.toAlgHom R R (ResidueField R)).comp σ = ρ := by
  let π : R →ₐ[R] ResidueField R := IsScalarTower.toAlgHom R R (ResidueField R)
  have h₀ : P.HasMap (ρ P.X) := P.hasMap_X.map ρ
  have hd₀ : Polynomial.aeval (ρ P.X) P.f.derivative ≠ 0 :=
    isUnit_iff_ne_zero.mp h₀.isUnit_derivative_f
  obtain ⟨a, ha, har⟩ := hroot P.f P.monic_f (ρ P.X) h₀.1 hd₀
  have hmap : P.HasMap a := by
    refine ⟨?_, ?_⟩
    · simpa only [Polynomial.aeval_def, Algebra.algebraMap_self, Polynomial.eval₂_id,
        Polynomial.IsRoot] using ha
    · apply (residue_ne_zero_iff_isUnit _).mp
      have hg₀ := isUnit_iff_ne_zero.mp h₀.2
      rw [← ResidueField.algebraMap_eq, ← Polynomial.aeval_algebraMap_apply,
        ResidueField.algebraMap_eq, har]
      exact hg₀
  refine ⟨P.lift a hmap, ?_, ?_⟩
  · apply P.hom_ext
    simpa [π, ResidueField.algebraMap_eq] using har
  · intro σ hσ
    have hs : P.HasMap (σ P.X) := P.hasMap_X.map σ
    have hsres : residue R (σ P.X) = ρ P.X := by
      simpa [ResidueField.algebraMap_eq] using congrArg (fun ψ ↦ ψ P.X) hσ
    have hsub : ¬ IsUnit (σ P.X - a) := by
      rw [← residue_ne_zero_iff_isUnit, not_not]
      simp [hsres, har]
    have heq : σ P.X = a :=
      eq_of_eval_eq_zero_of_not_isUnit_sub
        (by simpa only [Polynomial.aeval_def, Algebra.algebraMap_self, Polynomial.eval₂_id,
          Polynomial.IsRoot] using hs.1)
        ha hsub
        (by simpa only [Polynomial.aeval_def, Algebra.algebraMap_self, Polynomial.eval₂_id,
          Polynomial.IsRoot] using hs.isUnit_derivative_f)
    apply P.hom_ext
    simpa using heq

/-- A local ring in which simple residue roots of monic polynomials lift admits a unique
retraction from an étale algebra through a prime with trivial residue field extension. -/
theorem existsUnique_algHom_of_monic_simple_root_lifting_etale
    {R S : Type u} [CommRing R] [CommRing S] [IsLocalRing R] [Algebra R S]
    (hroot : ∀ f : Polynomial R, f.Monic → ∀ a₀ : ResidueField R,
      Polynomial.aeval a₀ f = 0 → Polynomial.aeval a₀ f.derivative ≠ 0 →
        ∃ a : R, f.IsRoot a ∧ residue R a = a₀)
    [Etale (Spec.map (CommRingCat.ofHom (algebraMap R S)))]
    (q : Ideal S) [q.IsPrime]
    (hq : q.comap (algebraMap R S) = maximalIdeal R)
    (hres : Function.Bijective
      ((Spec.map (CommRingCat.ofHom (algebraMap R S))).residueFieldMap
        (⟨q, inferInstance⟩ : Spec (.of S))).hom) :
    ∃! τ : S →ₐ[R] R, (maximalIdeal R).comap τ.toRingHom = q := by
  classical
  have : Algebra.Etale R S := RingHom.etale_algebraMap.mp
    ((HasRingHomProperty.Spec_iff (P := @Etale)
      (φ := CommRingCat.ofHom (algebraMap R S))).mp inferInstance)
  obtain ⟨ρ, hρ⟩ := exists_algHom_residueField_of_bijective_spec_residueFieldMap q hq hres
  obtain ⟨g, hg, hstd⟩ := Algebra.IsEtaleAt.exists_isStandardEtale (R := R) q
  have : Algebra.IsStandardEtale R (Localization.Away g) := hstd
  obtain ⟨P⟩ := Algebra.IsStandardEtale.nonempty_standardEtalePresentation
    (R := R) (S := Localization.Away g)
  have hρg : IsUnit (ρ g) := by
    rw [isUnit_iff_ne_zero]
    intro h
    exact hg (hρ ▸ h)
  let ρg : Localization.Away g →ₐ[R] ResidueField R :=
    IsLocalization.Away.liftAlgHom g hρg
  let ρC : P.Ring →ₐ[R] ResidueField R := ρg.comp P.equivRing.symm.toAlgHom
  obtain ⟨σ, hσ, hσunique⟩ := standardEtale_unique_lift hroot P.P ρC
  let τ : S →ₐ[R] R := (σ.comp P.equivRing.toAlgHom).comp
    (Algebra.algHom R S (Localization.Away g))
  let π : R →ₐ[R] ResidueField R := IsScalarTower.toAlgHom R R (ResidueField R)
  have hτred : π.comp τ = ρ := by
    ext s
    have h := congrArg (fun ψ ↦ ψ (P.equivRing (algebraMap S (Localization.Away g) s))) hσ
    simpa [τ, ρC, ρg, π, Algebra.algHom] using h
  have hτ : (maximalIdeal R).comap τ.toRingHom = q := by
    rw [← hρ, ← ker_residue (R := R)]
    change RingHom.ker ((residue R).comp τ.toRingHom) = RingHom.ker ρ.toRingHom
    exact congrArg (fun ψ : S →ₐ[R] ResidueField R ↦ RingHom.ker ψ.toRingHom) hτred
  refine ⟨τ, hτ, ?_⟩
  intro τ' hτ'
  have hτ'red : π.comp τ' = ρ := by
    ext s
    obtain ⟨r, hr⟩ := residue_surjective (ρ s)
    have hmem : s - algebraMap R S r ∈ q := by
      rw [← hρ, RingHom.mem_ker]
      simp [ρ.commutes, ResidueField.algebraMap_eq, hr]
    have hz : residue R (τ' s) - residue R r = 0 := by
      have := (residue_eq_zero_iff (τ' (s - algebraMap R S r))).mpr
        (show s - algebraMap R S r ∈ (maximalIdeal R).comap τ'.toRingHom from
          hτ'.symm ▸ hmem)
      simpa using this
    simpa [π, ResidueField.algebraMap_eq, ← hr] using sub_eq_zero.mp hz
  have hτ'g : IsUnit (τ' g) := by
    rw [← notMem_maximalIdeal]
    intro hm
    exact hg (hτ' ▸ hm)
  let τ'g : Localization.Away g →ₐ[R] R :=
    IsLocalization.Away.liftAlgHom g hτ'g
  let σ' : P.Ring →ₐ[R] R := τ'g.comp P.equivRing.symm.toAlgHom
  have hσ' : π.comp σ' = ρC := by
    have hext : π.comp τ'g = ρg := by
      apply IsLocalization.algHom_ext (Submonoid.powers g)
      ext s
      have h := congrArg (fun ψ ↦ ψ s) hτ'red
      simpa [τ'g, ρg, Algebra.algHom] using h
    exact congrArg (fun ψ ↦ ψ.comp P.equivRing.symm.toAlgHom) hext
  have heq : σ' = σ := hσunique σ' hσ'
  ext s
  have h := congrArg (fun ψ ↦ ψ (P.equivRing (algebraMap S (Localization.Away g) s))) heq
  simpa [σ', τ'g, τ, Algebra.algHom] using h

end IsLocalRing
