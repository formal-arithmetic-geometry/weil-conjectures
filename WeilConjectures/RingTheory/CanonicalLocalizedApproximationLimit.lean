/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Localization.Module
public import WeilConjectures.RingTheory.LocalizedApproximationColimits

import WeilConjectures.RingTheory.LocalizedRingColimitComparison
import WeilConjectures.RingTheory.LocalizedModuleColimitComparison
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic

/-! # Comparison of canonical localized approximation colimits

Localization at a prime commutes with filtered colimit presentations of a ring map and a module.

## Implementation details

The ring statements follow since localization commutes with filtered colimits [Stacks, Tag 037D],
transported through `ULift` ring equivalences. For modules, numerators and denominators lift to
a common stage, and zero relations descend by eventual equality in the additive-group colimit.
The supplied `ψ` and action agree with the canonical ones on every coprojection, hence
everywhere. The argument covers zero modules, singleton diagrams and noninjective transitions.

## References

* [Stacks, Tag 00RC], first reduction
* [Stacks, Tag 037D]
-/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace Algebra

/-- Given filtered colimit presentations of `R → S` and of the `S`-module `M`, and a prime `q`
of `S`, localizing every stage at the contracted primes gives colimit presentations of
`R_(q∩R) → S_q` and of `M_q`, compatible with the module actions. The ring map and the action
are supplied rather than chosen. -/
theorem canonical_localized_approximation_limit
    (R : Type u) (S : Type v) (M : Type w)
    [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M] :
    let R' := ULift.{max u v w} R
    let S' := ULift.{max u v w} S
    let M' := ULift.{max u v w} M
    letI : Algebra R' S' := ULift.algebra' R S'
    ∀
    {Λ : Type (max u v w)} [Preorder Λ] [Nonempty Λ] [IsDirected Λ (· ≤ ·)]
    (A B : Λ ⥤ CommRingCat.{max u v w}) (η : A ⟶ B)
      (π : A ⟶ (Functor.const Λ).obj (CommRingCat.of R'))
      (κ : B ⟶ (Functor.const Λ).obj (CommRingCat.of S'))
      (D : Λ ⥤ AddCommGrpCat.{max u v w})
      (ν : D ⟶ (Functor.const Λ).obj (AddCommGrpCat.of M'))
    [∀ i : Λ, Module (B.obj i) (D.obj i)]
    (hmodel :
      -- (1) the three colimits, compatible with `R' → S'` and the module actions
      Nonempty (IsColimit (Cocone.mk (CommRingCat.of R') π)) ∧
      Nonempty (IsColimit (Cocone.mk (CommRingCat.of S') κ)) ∧
      Nonempty (IsColimit (Cocone.mk (AddCommGrpCat.of M') ν)) ∧
      (∀ i, η.app i ≫ κ.app i = π.app i ≫ CommRingCat.ofHom (algebraMap R' S')) ∧
      (∀ (i j : Λ) (h : i ≤ j) (y : B.obj i) (x : D.obj i),
        (D.map (homOfLE h)).hom (y • x) =
          (B.map (homOfLE h)).hom y • (D.map (homOfLE h)).hom x) ∧
      (∀ i (y : B.obj i) (x : D.obj i),
        (@AddCommGrpCat.Hom.hom _ (AddCommGrpCat.of M') (ν.app i)) (y • x) =
          (@CommRingCat.Hom.hom _ (CommRingCat.of S') (κ.app i)) y •
            (@AddCommGrpCat.Hom.hom _ (AddCommGrpCat.of M') (ν.app i)) x))
    (q : PrimeSpectrum S),
    let q' : PrimeSpectrum S' := ⟨q.asIdeal.comap ULift.ringEquiv.toRingHom,
      Ideal.IsPrime.comap _⟩
    let hs := fun (i j : Λ) (f : i ⟶ j) (b : B.obj i) (x : D.obj i) ↦
      hmodel.2.2.2.2.1 i j (leOfHom f) b x
    let Aₗ := primeRingDiagram A (η ≫ κ) q'
    let Bₗ := primeRingDiagram B κ q'
    let Dₗ := primeModuleDiagram B κ q' D hs
    ∀ (ψ : (colimit Aₗ : CommRingCat.{max u v w}) →+*
        (colimit Bₗ : CommRingCat.{max u v w}))
      (act : Module (colimit Bₗ : CommRingCat.{max u v w})
        (colimit Dₗ : AddCommGrpCat.{max u v w})),
      letI := act
      (∀ i, ψ.comp (colimit.ι Aₗ i).hom =
        (colimit.ι Bₗ i).hom.comp (primeDiagramHom A B η κ q' i)) →
      (∀ (i : Λ) (b : Bₗ.obj i) (x : Dₗ.obj i),
        (colimit.ι Dₗ i).hom (b • x) =
          (colimit.ι Bₗ i).hom b • (colimit.ι Dₗ i).hom x) →
      (∃ ρ : R →+* (colimit Aₗ : CommRingCat.{max u v w}),
        letI := ρ.toAlgebra
        letI := Module.compHom (colimit Dₗ : AddCommGrpCat.{max u v w}) ψ
        letI := Module.compHom (colimit Dₗ : AddCommGrpCat.{max u v w}) ρ
        IsLocalization (q.asIdeal.comap (algebraMap R S)).primeCompl
          (colimit Aₗ : CommRingCat.{max u v w}) ∧
        Nonempty (LocalizedModule q.asIdeal.primeCompl M ≃ₗ[R]
          (colimit Dₗ : AddCommGrpCat.{max u v w}))) := by
  classical
  dsimp only
  intro Λ _ _ _ A B η π κ D ν _ hmodel q
  let R' := ULift.{max u v w} R
  let S' := ULift.{max u v w} S
  let M' := ULift.{max u v w} M
  let : Algebra R' S' := ULift.algebra' R S'
  let q' : PrimeSpectrum S' :=
    ⟨q.asIdeal.comap ULift.ringEquiv.toRingHom, Ideal.IsPrime.comap _⟩
  let hs := fun (i j : Λ) (f : i ⟶ j) (b : B.obj i) (x : D.obj i) ↦
    hmodel.2.2.2.2.1 i j (leOfHom f) b x
  let Aq := primeRingDiagram A (η ≫ κ) q'
  let Bq := primeRingDiagram B κ q'
  let Nq := primeModuleDiagram B κ q' D hs
  intro ψ act hψ hscalar
  let := act
  obtain ⟨eB, heB⟩ := localizedRingColimitComparison B Bq κ hmodel.2.1 q'.asIdeal
    (fun i ↦ q'.asIdeal.comap (κ.app i).hom) (fun _ ↦ rfl)
    (fun _ ↦ RingEquiv.refl _) (by
      intro i j f x
      exact Localization.localRingHom_to_map _ _ _
        (contractedPrime_map B κ q' i j f) x)
  let g : ∀ i, Nq.obj i →+ LocalizedModule q'.asIdeal.primeCompl M' := fun i ↦
    primeModuleMap _ _ (κ.app i).hom rfl (ν.app i).hom (hmodel.2.2.2.2.2 i)
  obtain ⟨eN, heN⟩ := exists_colimit_addEquiv_localizedModule B D Nq κ ν
    hmodel.2.1 hmodel.2.2.1 hs hmodel.2.2.2.2.2 q'
    (fun _ ↦ AddEquiv.refl _) (by
      intro i j f x s
      exact ⟨⟨(B.map f).hom s, by
        change (B.map f).hom s ∉ q'.asIdeal.comap (κ.app j).hom
        change (s : B.obj i) ∉ (q'.asIdeal.comap (κ.app j).hom).comap (B.map f).hom
        rw [← contractedPrime_map B κ q' i j f]
        exact s.property⟩, rfl,
        primeModuleMap_mk _ _ (B.map f).hom
          (contractedPrime_map B κ q' i j f) (D.map f).hom (hs i j f) x s⟩)
    g (by
      intro i x s
      exact primeModuleMap_mk (R := B.obj i) (S := S') (M := D.obj i) (N := M')
        _ _ (κ.app i).hom rfl (ν.app i).hom (hmodel.2.2.2.2.2 i) x s)
  -- Lift the scalar and vector to one common stage to use the supplied action formula.
  have hsemilinear (b : (colimit Bq : CommRingCat))
      (x : (colimit Nq : AddCommGrpCat)) : eN (b • x) = eB b • eN x := by
    obtain ⟨i, b, rfl⟩ := Concrete.colimit_exists_rep Bq b
    obtain ⟨j, x, rfl⟩ := Concrete.colimit_exists_rep Nq x
    obtain ⟨k, hi, hj⟩ := exists_ge_ge i j
    have hb := ConcreteCategory.congr_hom (colimit.w Bq (homOfLE hi)) b
    have hx := ConcreteCategory.congr_hom (colimit.w Nq (homOfLE hj)) x
    change (colimit.ι Bq k).hom ((Bq.map (homOfLE hi)).hom b) =
      (colimit.ι Bq i).hom b at hb
    change (colimit.ι Nq k).hom ((Nq.map (homOfLE hj)).hom x) =
      (colimit.ι Nq j).hom x at hx
    rw [← hb, ← hx, ← hscalar, heN, heB, heN]
    exact primeModuleMap_smul _ _ _ rfl _ (hmodel.2.2.2.2.2 k) _ _
  let p := q'.asIdeal.comap (algebraMap R' S')
  have hp : ∀ i, q'.asIdeal.comap ((η ≫ κ).app i).hom = p.comap (π.app i).hom := by
    intro i
    change q'.asIdeal.comap ((η.app i ≫ κ.app i).hom) =
      (q'.asIdeal.comap (algebraMap R' S')).comap (π.app i).hom
    rw [hmodel.2.2.2.1 i, Ideal.comap_comap]
    rfl
  obtain ⟨eA, heA⟩ := localizedRingColimitComparison A Aq π hmodel.1 p
    (fun i ↦ q'.asIdeal.comap ((η ≫ κ).app i).hom) hp
    (fun _ ↦ RingEquiv.refl _) (by
      intro i j f x
      exact Localization.localRingHom_to_map _ _ _
        (contractedPrime_map A (η ≫ κ) q' i j f) x)
  let ℓ := Localization.localRingHom p q'.asIdeal (algebraMap R' S') rfl
  have square : eB.toRingHom.comp ψ = ℓ.comp eA.toRingHom := by
    suffices hh : CommRingCat.ofHom (eB.toRingHom.comp ψ) =
        CommRingCat.ofHom (ℓ.comp eA.toRingHom) from congrArg CommRingCat.Hom.hom hh
    apply colimit.hom_ext
    intro i
    apply CommRingCat.hom_ext
    apply IsLocalization.ringHom_ext (q'.asIdeal.comap ((η ≫ κ).app i).hom).primeCompl
    ext x
    change eB (ψ ((colimit.ι Aq i).hom (algebraMap _ _ x))) =
      ℓ (eA ((colimit.ι Aq i).hom (algebraMap _ _ x)))
    have hψx := DFunLike.congr_fun (hψ i) (algebraMap _ _ x)
    rw [RingHom.comp_apply, RingHom.comp_apply] at hψx
    rw [hψx, heB, heA]
    change Localization.localRingHom _ _ (κ.app i).hom rfl
      (primeDiagramHom A B η κ q' i (algebraMap _ _ x)) =
      ℓ (Localization.localRingHom _ _ (π.app i).hom (hp i) (algebraMap _ _ x))
    rw [show primeDiagramHom A B η κ q' i (algebraMap _ _ x) =
      algebraMap _ _ ((η.app i).hom x) from
      Localization.localRingHom_to_map _ _ (η.app i).hom rfl x]
    dsimp only [ℓ]
    rw [Localization.localRingHom_to_map, Localization.localRingHom_to_map]
    change algebraMap S' (Localization.AtPrime q'.asIdeal)
        ((κ.app i).hom ((η.app i).hom x)) =
      Localization.localRingHom p q'.asIdeal (algebraMap R' S') rfl
        (algebraMap R' (Localization.AtPrime p) ((π.app i).hom x))
    rw [Localization.localRingHom_to_map]
    exact congrArg (algebraMap S' (Localization.AtPrime q'.asIdeal))
      (ConcreteCategory.congr_hom (hmodel.2.2.2.1 i) x)
  -- The base comparison determines the localization map uniquely.
  let ρ' : R' →+* (colimit Aq : CommRingCat) :=
    eA.symm.toRingHom.comp (algebraMap R' (Localization.AtPrime p))
  let : Algebra R' (colimit Aq : CommRingCat) := ρ'.toAlgebra
  have hloc' : IsLocalization p.primeCompl (colimit Aq : CommRingCat) :=
    (IsLocalization.isLocalization_iff_of_ringEquiv p.primeCompl eA.symm).mp
      (inferInstance : IsLocalization p.primeCompl (Localization.AtPrime p))
  let ρ : R →+* (colimit Aq : CommRingCat) :=
    ρ'.comp (ULift.ringEquiv : R' ≃+* R).symm.toRingHom
  refine ⟨ρ, ?_, ?_⟩
  · let : Algebra R (colimit Aq : CommRingCat) := ρ.toAlgebra
    let : IsLocalization p.primeCompl (colimit Aq : CommRingCat) := hloc'
    apply IsLocalization.of_ringEquiv_left (ULift.ringEquiv : R' ≃+* R).symm
      (M₁ := p.primeCompl)
    · ext r
      simp only [Submonoid.mem_map, Ideal.mem_primeCompl_iff]
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact hx
      · intro hr
        exact ⟨r.down, hr, rfl⟩
    · intro r
      rfl
  · -- Transport fractions explicitly, including the inverse, across ULift.down.
    let down : M' →+ M := (ULift.moduleEquiv : M' ≃ₗ[R] M).toAddEquiv.toAddMonoidHom
    let up : M →+ M' := (ULift.moduleEquiv : M' ≃ₗ[R] M).symm.toAddEquiv.toAddMonoidHom
    let gd : LocalizedModule q'.asIdeal.primeCompl M' →+
        LocalizedModule q.asIdeal.primeCompl M :=
      primeModuleMap _ _ (ULift.ringEquiv : S' ≃+* S).toRingHom rfl down
        (fun _ _ ↦ rfl)
    have hqu : q.asIdeal = q'.asIdeal.comap
        (ULift.ringEquiv : S' ≃+* S).symm.toRingHom := by
      ext x
      rfl
    let gu : LocalizedModule q.asIdeal.primeCompl M →+
        LocalizedModule q'.asIdeal.primeCompl M' :=
      primeModuleMap _ _ (ULift.ringEquiv : S' ≃+* S).symm.toRingHom hqu up
        (fun _ _ ↦ rfl)
    let eU : LocalizedModule q'.asIdeal.primeCompl M' ≃+
        LocalizedModule q.asIdeal.primeCompl M :=
      { gd with
        invFun := gu
        left_inv := by
          intro z
          induction z using LocalizedModule.induction_on with
          | h x s =>
            rfl
        right_inv := by
          intro z
          induction z using LocalizedModule.induction_on with
          | h x s =>
            rfl }
    let : Module (colimit Aq : CommRingCat) (colimit Nq : AddCommGrpCat) :=
      Module.compHom _ ψ
    let : Module R (colimit Nq : AddCommGrpCat) := Module.compHom _ ρ
    let e := eN.trans eU
    have hlinear (r : R) (x : (colimit Nq : AddCommGrpCat)) :
        e (r • x) = r • e x := by
      change eU (eN (ψ (ρ r) • x)) = r • eU (eN x)
      rw [hsemilinear]
      have hsq := DFunLike.congr_fun square (ρ r)
      change eB (ψ (ρ r)) = ℓ (eA (ρ r)) at hsq
      rw [hsq]
      have hρ : eA (ρ r) = algebraMap R' (Localization.AtPrime p) (ULift.up r) := by
        exact eA.apply_symm_apply _
      rw [hρ]
      dsimp only [ℓ]
      rw [Localization.localRingHom_to_map]
      induction eN x using LocalizedModule.induction_on with
      | h m s =>
        rw [← Localization.mk_one_eq_algebraMap, LocalizedModule.mk_smul_mk, one_mul]
        change gd (LocalizedModule.mk _ s) = r • gd (LocalizedModule.mk m s)
        rw [show gd (LocalizedModule.mk _ s) = _ from
          primeModuleMap_mk _ _ _ rfl down (fun _ _ ↦ rfl) _ s]
        rw [show gd (LocalizedModule.mk m s) = _ from
          primeModuleMap_mk _ _ _ rfl down (fun _ _ ↦ rfl) m s]
        rw [LocalizedModule.smul'_mk]
        congr 1
        exact IsScalarTower.algebraMap_smul S r m.down
    exact ⟨({ e with map_smul' := hlinear } :
      (colimit Nq : AddCommGrpCat) ≃ₗ[R] LocalizedModule q.asIdeal.primeCompl M).symm⟩

end Algebra
