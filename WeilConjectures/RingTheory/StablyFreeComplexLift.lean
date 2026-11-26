/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.RingPseudoCoherent
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Module.StablyFree.Basic
public import Mathlib.Algebra.Homology.Additive
public import Mathlib.LinearAlgebra.Basis.Prod
public import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.RingTheory.Finiteness.Prod
import WeilConjectures.AlgebraicGeometry.ComplexLiftClassProjective
import WeilConjectures.RingTheory.StablyFreeModuleLift
import WeilConjectures.RingTheory.FiniteProjectiveFreeModIdeal
import WeilConjectures.RingTheory.FiniteModuleSurjectiveModIdeal

/-!
# Lifting finite stably free complexes modulo an ideal

Let `I` be an ideal of `R` such that every `1 + x` with `x ∈ I` is a unit. A bounded above
complex of finite stably free `R/I`-modules representing the derived reduction of a
pseudo-coherent object `K` lifts to a bounded above complex of finite stably free `R`-modules
representing `K`; terms whose reductions are free can be chosen free.

## Implementation details

The representative `Classical.choose hK` is bounded above and finite free, hence K-flat.
Consequently its termwise extension of scalars computes `K ⊗ᴸ R/I`; the hypothesis `hE` says
precisely that `E` represents this derived reduction. `Module.Finite` together with
`Module.IsStablyFree` means finite stably free, equivalently a finite free stabilization of
finite rank.

## References

* [Stacks, Tag 0BCB]
-/

@[expose] public section

universe u v w w'

open CategoryTheory

namespace DerivedCategory

private theorem stablyFree_prod {R : Type u} [CommRing R]
    (M N : ModuleCat.{max u v} R)
    [Module.IsStablyFree R M] [Module.IsStablyFree R N] :
    Module.IsStablyFree R (M × N) := by
  obtain ⟨A, _, _, _, _, hA⟩ := Module.IsStablyFree.exist_free_prod R M
  obtain ⟨B, _, _, _, _, hB⟩ := Module.IsStablyFree.exist_free_prod R N
  have : Module.Free R ((M × N) × (A × B)) :=
    Module.Free.of_equiv (LinearEquiv.prodProdProdComm R M A N B)
  exact Module.IsStablyFree.of_free_prod R (M × N) (A × B)

private theorem stablyFree_snd {R : Type u} [CommRing R]
    (M N : ModuleCat.{max u v} R) [Module.Finite R M]
    [Module.IsStablyFree R M] [Module.IsStablyFree R (M × N)] :
    Module.IsStablyFree R N := by
  obtain ⟨A, _, _, _, _, hA⟩ := Module.IsStablyFree.exist_free_prod R M
  obtain ⟨B, _, _, _, _, hB⟩ := Module.IsStablyFree.exist_free_prod R (M × N)
  have : Module.Free R (((M × N) × B) × A) := inferInstance
  let e : (((M × N) × B) × A) ≃ₗ[R] N × ((M × A) × B) :=
    { toFun := fun x ↦ (x.1.1.2, ((x.1.1.1, x.2), x.1.2))
      invFun := fun x ↦ (((x.2.1.1, x.1), x.2.2), x.2.1.2)
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  have : Module.Free R (N × ((M × A) × B)) := Module.Free.of_equiv e
  exact Module.IsStablyFree.of_free_prod R N ((M × A) × B)

private theorem finite_stablyFree_class_closed {R : Type u} [CommRing R]
    (M N T : ModuleCat.{max u v} R) (h : Nonempty (T ≅ ModuleCat.of R (M × N))) :
    ((Module.Finite R M ∧ Module.IsStablyFree R M) ∧
        (Module.Finite R T ∧ Module.IsStablyFree R T)) ↔
      ((Module.Finite R M ∧ Module.IsStablyFree R M) ∧
        (Module.Finite R N ∧ Module.IsStablyFree R N)) := by
  obtain ⟨e⟩ := h
  constructor
  · rintro ⟨⟨hMfin, hMsf⟩, ⟨hTfin, hTsf⟩⟩
    have : Module.Finite R (M × N) := Module.Finite.equiv e.toLinearEquiv
    have : Module.IsStablyFree R (M × N) := Module.IsStablyFree.equiv e.toLinearEquiv
    exact ⟨⟨hMfin, hMsf⟩,
      ⟨Module.Finite.of_surjective (LinearMap.snd R M N) (fun n ↦ ⟨(0, n), rfl⟩),
        stablyFree_snd M N⟩⟩
  · rintro ⟨⟨hMfin, hMsf⟩, ⟨hNfin, hNsf⟩⟩
    have : Module.IsStablyFree R (M × N) := stablyFree_prod M N
    exact ⟨⟨hMfin, hMsf⟩,
      ⟨Module.Finite.equiv e.symm.toLinearEquiv,
        Module.IsStablyFree.equiv e.symm.toLinearEquiv⟩⟩

/-- A bounded above finite stably free complex representing the derived reduction of a
pseudo-coherent object lifts to such a complex over the original ring. Terms whose reductions
are free are free simultaneously. -/
theorem exists_stablyFree_lift_mod_ideal
    {R : Type u} [CommRing R] (I : Ideal R)
    (hunits : ∀ x : I, IsUnit (1 + (x : R)))
    [HasDerivedCategory.{w} (ModuleCat.{max u v} R)]
    [HasDerivedCategory.{w'} (ModuleCat.{max u v} (R ⧸ I))]
    (K : DerivedCategory (ModuleCat.{max u v} R)) (hK : IsPseudoCoherent K)
    (E : CochainComplex (ModuleCat.{max u v} (R ⧸ I)) ℤ)
    (hEbound : ∃ b : ℤ, E.IsStrictlyLE b)
    (hEterms : ∀ i : ℤ,
      Module.Finite (R ⧸ I) (E.X i) ∧ Module.IsStablyFree (R ⧸ I) (E.X i))
    (hE : Nonempty (Q.obj
      (((ModuleCat.extendScalars (Ideal.Quotient.mk I)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (Classical.choose hK)) ≅ Q.obj E)) :
    ∃ P : CochainComplex (ModuleCat.{max u v} R) ℤ,
      (∃ b : ℤ, P.IsStrictlyLE b) ∧
      (∀ i : ℤ, Module.Finite R (P.X i) ∧ Module.IsStablyFree R (P.X i)) ∧
      Nonempty (Q.obj P ≅ K) ∧
      Nonempty (((ModuleCat.extendScalars (Ideal.Quotient.mk I)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj P ≅ E) ∧
      (∀ i : ℤ, Module.Free (R ⧸ I) (E.X i) → Module.Free R (P.X i)) := by
  classical
  let Pclass : Set (ModuleCat.{max u v} R) :=
    {M | Module.Finite R M ∧ Module.IsStablyFree R M}
  have hproj : ∀ M : ModuleCat.{max u v} R, M ∈ Pclass → Projective M := by
    intro M hM
    have : Module.IsStablyFree R M := hM.2
    have : Module.Projective R M := Module.instProjectiveOfIsStablyFree R M
    exact M.projective_of_categoryTheory_projective
  have hsurj : ∀ (M N : ModuleCat.{max u v} R) (f : M ⟶ N),
      M ∈ Pclass → N ∈ Pclass →
      Function.Surjective ((ModuleCat.extendScalars (Ideal.Quotient.mk I)).map f) →
      Function.Surjective f := by
    intro M N f _ hN hf
    have : Module.Finite R N := hN.1
    exact ModuleCat.surjective_of_extendScalars_mod_ideal I hunits M N f hf
  have hterms : ∀ i : ℤ, ∃ M : ModuleCat.{max u v} R, M ∈ Pclass ∧
      Nonempty (E.X i ≅ (ModuleCat.extendScalars (Ideal.Quotient.mk I)).obj M) := by
    intro i
    have : Module.Finite (R ⧸ I) (E.X i) := (hEterms i).1
    have : Module.IsStablyFree (R ⧸ I) (E.X i) := (hEterms i).2
    exact ModuleCat.exists_finite_stablyFree_lift I hunits (E.X i)
  have hmodel : ∃ K₀ : CochainComplex (ModuleCat.{max u v} R) ℤ,
      (∃ b : ℤ, K₀.IsStrictlyLE b) ∧ (∀ i : ℤ, K₀.X i ∈ Pclass) ∧
      Nonempty (Q.obj K₀ ≅ K) ∧
      Nonempty (Q.obj (((ModuleCat.extendScalars (Ideal.Quotient.mk I)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj K₀) ≅ Q.obj E) := by
    refine ⟨Classical.choose hK, ?_, ?_, ?_, hE⟩
    · obtain ⟨b, hb, _, _⟩ := Classical.choose_spec hK
      exact ⟨b, hb⟩
    · intro i
      obtain ⟨_, _, hfree, _⟩ := Classical.choose_spec hK
      have : Module.Free R ((Classical.choose hK).X i) := (hfree i).1
      exact ⟨(hfree i).2, inferInstance⟩
    · obtain ⟨_, _, _, hiso⟩ := Classical.choose_spec hK
      exact hiso
  obtain ⟨P, hbound, hPterms, hPK, ⟨e⟩⟩ :=
    AlgebraicGeometry.complex_lift_class_projective R I Pclass K E hproj
      (fun M N T h ↦ finite_stablyFree_class_closed M N T h) hsurj hEbound hterms hmodel
  refine ⟨P, hbound, hPterms, hPK, ⟨e⟩, ?_⟩
  intro i hfree
  have : Module.Free (R ⧸ I) (E.X i) := hfree
  have : Module.Finite R (P.X i) := (hPterms i).1
  have : Module.IsStablyFree R (P.X i) := (hPterms i).2
  let ei : (ModuleCat.extendScalars (Ideal.Quotient.mk I)).obj (P.X i) ≅ E.X i :=
    (HomologicalComplex.eval _ _ i).mapIso e
  have : Module.Free (R ⧸ I)
      ((ModuleCat.extendScalars (Ideal.Quotient.mk I)).obj (P.X i)) :=
    Module.Free.of_equiv ei.symm.toLinearEquiv
  exact ModuleCat.free_of_free_extendScalars_mod_ideal I hunits (P.X i)

end DerivedCategory
