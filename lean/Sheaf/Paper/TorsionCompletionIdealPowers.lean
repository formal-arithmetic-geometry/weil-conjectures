/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S1
-/
module

public import Sheaf.Paper.TorsionCompletionDefinitions
import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafSections
import Mathlib.Algebra.Category.ModuleCat.Kernels
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
import Mathlib.RingTheory.Ideal.Operations

/-! # Powers of sections of the extended constant ideal

Source: Stacks Project, proetale.tex, Tag 099P.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe t u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

private theorem quotientMap_apply (X : Scheme.{t}) {A : Type u} [CommRing A]
    (I : Ideal A) (U : coefficientProEtaleSiteModel.{t, u} X)
    (x : (torsionCompletionRing X A).obj.obj (op U)) :
    (torsionCompletionQuotientMap X I).val.app (op U) x =
      (torsionCompletionQuotient X I).hom.app (op U) x := by
  change (torsionCompletionQuotient X I).hom.app (op U) x * 1 = _
  exact mul_one _

private theorem ideal_section_iff (X : Scheme.{t}) {A : Type u} [CommRing A]
    (I : Ideal A) (U : coefficientProEtaleSiteModel.{t, u} X)
    (x : (torsionCompletionRing X A).obj.obj (op U)) :
    (∃ y : (torsionCompletionIdeal X I).val.obj (op U),
      (torsionCompletionIdealInclusion X I).val.app (op U) y = x) ↔
      (torsionCompletionQuotient X I).hom.app (op U) x = 0 := by
  rw [← quotientMap_apply]
  let E := SheafOfModules.evaluation (torsionCompletionModuleRing X A) (op U)
  let q := torsionCompletionQuotientMap X I
  let e := PreservesKernel.iso E q ≪≫ ModuleCat.kernelIsoKer (E.map q)
  have he : e.inv ≫ E.map (kernel.ι q) =
      ModuleCat.ofHom (E.map q).hom.ker.subtype := by
    simp only [e, Iso.trans_inv, Category.assoc,
      PreservesKernel.iso_inv_ι, ModuleCat.kernelIsoKer_inv_kernel_ι]
  constructor
  · rintro ⟨y, rfl⟩
    exact congrArg (fun a ↦ (a.val.app (op U)) y) (kernel.condition q)
  · intro h
    refine ⟨e.inv ⟨x, h⟩, ?_⟩
    exact congrArg (fun a ↦ a ⟨x, h⟩) he

private abbrev constantSection (X : Scheme.{t}) (A : Type u) [CommRing A]
    (U : coefficientProEtaleSiteModel.{t, u} X) :=
  (toSheafify (coefficientProEtaleModelTopology.{t, u} X)
    ((Functor.const (coefficientProEtaleSiteModel.{t, u} X)ᵒᵖ).obj
      (CommRingCat.of (ULift.{t + 1} A)))).app (op U)

private theorem quotient_constant (X : Scheme.{t}) {A : Type u} [CommRing A]
    (I : Ideal A) (U : coefficientProEtaleSiteModel.{t, u} X) (a : ULift.{t + 1} A) :
    (torsionCompletionQuotient X I).hom.app (op U) (constantSection X A U a) =
      constantSection X (A ⧸ I) U ⟨Ideal.Quotient.mk I a.down⟩ := by
  have h := toSheafify_naturality (D := CommRingCat.{max u (t + 1)})
    (coefficientProEtaleModelTopology.{t, u} X)
    ((Functor.const (coefficientProEtaleSiteModel.{t, u} X)ᵒᵖ).map
      (CommRingCat.ofHom (RingHom.ulift (Ideal.Quotient.mk I))))
  exact (congrArg (fun k ↦ k.app (op U) a) h).symm

/-- A power of a section of the extended ideal belongs to the corresponding
extended power ideal. The ideals here are the actual kernels of constant quotient maps.

Source: Stacks Project, proetale.tex, Tag 099P (section-derived-completion-proetale),
first item; exactness and local descriptions of constant sheafification.
(blueprint: lem-weil-pbc-torsion-completion-ideal-powers).

Proof: Locally lift the coefficient section to an element a of A, using local
surjectivity of the constant-presheaf sheafification unit. Its quotient class in
A/I has zero associated section, since the original section is in the kernel.
Local injectivity of the sheafification unit refines the cover so that a belongs
to I. Then a^n belongs to I^n; its constant section lies in the kernel of the map
to the constant A/I^n sheaf. These local lifts of f^n glue uniquely, because the
kernel inclusion is monic. The argument includes n=0, the zero ring, and empty
covering sieves. -/
theorem torsionCompletionIdeal_section_pow (X : Scheme.{t}) {A : Type u} [CommRing A]
    (I : Ideal A) (U : coefficientProEtaleSiteModel.{t, u} X)
    (f : (torsionCompletionRing X A).obj.obj (op U))
    (hf : ∃ y : (torsionCompletionIdeal X I).val.obj (op U),
      (torsionCompletionIdealInclusion X I).val.app (op U) y = f) (n : ℕ) :
    ∃ y : (torsionCompletionIdeal X (I ^ n)).val.obj (op U),
      (torsionCompletionIdealInclusion X (I ^ n)).val.app (op U) y = f ^ n := by
  classical
  let J := coefficientProEtaleModelTopology.{t, u} X
  let O := torsionCompletionModuleRing X A
  let η := toSheafify J ((Functor.const (coefficientProEtaleSiteModel.{t, u} X)ᵒᵖ).obj
    (CommRingCat.of (ULift.{t + 1} A)))
  have hq := (ideal_section_iff X I U f).mp hf
  apply (ideal_section_iff X (I ^ n) U (f ^ n)).mpr
  apply (torsionCompletionRing X (A ⧸ I ^ n)).isSeparated
    U (Presheaf.imageSieve η f) (Presheaf.imageSieve_mem J η f)
  intro V g hg
  obtain ⟨a, ha⟩ := hg
  change constantSection X A V a = O.obj.map g.op f at ha
  have hlocal : (torsionCompletionQuotient X I).hom.app (op V)
      (constantSection X A V a) = 0 := by
    rw [ha]
    exact (congrArg (fun k ↦ k f)
      ((torsionCompletionQuotient X I).hom.naturality g.op)).trans (by
        change (torsionCompletionModuleRing X (A ⧸ I)).obj.map g.op
          ((torsionCompletionQuotient X I).hom.app (op U) f) = 0
        rw [hq, map_zero])
  by_cases hV : (⊥ : Sieve V) ∈ J V
  · apply (torsionCompletionRing X (A ⧸ I ^ n)).isSeparated V ⊥ hV
    intro W k hk
    exact False.elim hk
  · have haI : a.down ∈ I := by
      rw [quotient_constant] at hlocal
      have hz : (⟨Ideal.Quotient.mk I a.down⟩ : ULift.{t + 1} (A ⧸ I)) = 0 :=
        J.toSheafify_const_app_injective (CommRingCat.of (ULift.{t + 1} (A ⧸ I))) hV
          (hlocal.trans (map_zero (constantSection X (A ⧸ I) V).hom).symm)
      exact Ideal.Quotient.eq_zero_iff_mem.mp (congrArg ULift.down hz)
    change (torsionCompletionModuleRing X (A ⧸ I ^ n)).obj.map g.op
      ((torsionCompletionQuotient X (I ^ n)).hom.app (op U) (f ^ n)) = _
    rw [← NatTrans.naturality_apply, map_pow, ← ha]
    have hp : (constantSection X A V a) ^ n = constantSection X A V (a ^ n) :=
      (map_pow (constantSection X A V).hom a n).symm
    rw [hp, quotient_constant]
    have hz : (⟨Ideal.Quotient.mk (I ^ n) (a ^ n).down⟩ :
        ULift.{t + 1} (A ⧸ I ^ n)) = 0 := by
      apply ULift.ext
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.pow_mem_pow haI n)
    rw [hz, map_zero, map_zero]

end AlgebraicGeometry.Scheme
