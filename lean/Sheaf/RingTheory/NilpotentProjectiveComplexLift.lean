/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NF
-/
module

public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.Algebra.Module.Projective
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import Mathlib.CategoryTheory.Adjunction.Additive
import Sheaf.AlgebraicGeometry.ComplexLiftClassProjective
import Sheaf.Algebra.Homology.BoundedAboveProjectiveModel
import Sheaf.Algebra.Homology.NilpotentModuleDerivedUpperBound
import Sheaf.RingTheory.NilpotentProjectiveModuleLift
import Mathlib.LinearAlgebra.TensorProduct.Quotient
import WeilConjectures.RingTheory.NakayamaNilpotent
import Mathlib.Algebra.Homology.DerivedCategory.KProjective
import Sheaf.Algebra.Homology.LargeFilteredFreeResolution
import Sheaf.Algebra.Homology.FilteredFreeKProjective
import Sheaf.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass

/-!
# Lifting a prescribed projective complex through a nilpotent quotient

Source: Stacks Project, More on Algebra, Tag 09AR, lemma-lift-complex-projectives
(blueprint: lem-weil-pbc-nilpotent-projective-complex-lift).
-/

@[expose] public section

set_option autoImplicit false

universe u v w w'

open CategoryTheory

namespace CochainComplex

private noncomputable def reductionEquiv
    (A : Type u) [CommRing A] (I : Ideal A) (P : ModuleCat.{max u v} A) :
    (ModuleCat.extendScalars (Ideal.Quotient.mk I)).obj P ≃ₗ[A ⧸ I]
      P ⧸ (I • (⊤ : Submodule A P)) := by
  let e := TensorProduct.quotTensorEquivQuotSMul P I
  refine
    { e.toAddEquiv with
      map_smul' := ?_ }
  intro a x
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  exact e.map_smul a x

private theorem projective_class_closed
    (A : Type u) [CommRing A] (P₁ P₂ P₁₂ : ModuleCat.{max u v} A)
    (he : Nonempty (P₁₂ ≅ ModuleCat.of A (P₁ × P₂))) :
    (Module.Projective A P₁ ∧ Module.Projective A P₁₂ ↔
      Module.Projective A P₁ ∧ Module.Projective A P₂) := by
  obtain ⟨e⟩ := he
  constructor
  · rintro ⟨h₁, h₁₂⟩
    have := Module.Projective.of_equiv e.toLinearEquiv
    exact ⟨h₁, Module.Projective.of_split (LinearMap.inr A P₁ P₂)
      (LinearMap.snd A P₁ P₂) (by ext; rfl)⟩
  · rintro ⟨h₁, h₂⟩
    exact ⟨h₁, Module.Projective.of_equiv e.toLinearEquiv.symm⟩

private theorem surjective_of_reduction_surjective
    (A : Type u) [CommRing A] (I : Ideal A)
    (hI : ∃ N : ℕ, 1 ≤ N ∧ I ^ N = ⊥)
    (P₁ P₂ : ModuleCat.{max u v} A) (f : P₁ ⟶ P₂)
    (hf : Function.Surjective ((ModuleCat.extendScalars (Ideal.Quotient.mk I)).map f)) :
    Function.Surjective f := by
  apply RingTheory.surjective_of_surjective_mod_nilpotent A P₁ P₂ I f.hom
    (by simpa only [Nat.one_le_iff_ne_zero, Nat.pos_iff_ne_zero] using hI)
  intro y
  obtain ⟨x, hx⟩ := hf ((reductionEquiv A I P₂).symm y)
  refine ⟨reductionEquiv A I P₁ x, ?_⟩
  have hn : ∀ x : (ModuleCat.extendScalars (Ideal.Quotient.mk I)).obj P₁,
      ((I • ⊤ : Submodule A P₁).mapQ (I • ⊤ : Submodule A P₂) f.hom
        (Submodule.smul_top_le_comap_smul_top I f.hom)) (reductionEquiv A I P₁ x) =
      reductionEquiv A I P₂ ((ModuleCat.extendScalars (Ideal.Quotient.mk I)).map f x) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a m =>
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
      change ((I • ⊤ : Submodule A P₁).mapQ (I • ⊤ : Submodule A P₂) f.hom _)
        (TensorProduct.quotTensorEquivQuotSMul P₁ I
          (Ideal.Quotient.mk I a ⊗ₜ[A] m)) =
        TensorProduct.quotTensorEquivQuotSMul P₂ I
          (Ideal.Quotient.mk I a ⊗ₜ[A] f m)
      simp only [TensorProduct.quotTensorEquivQuotSMul_mk_tmul,
        Submodule.mapQ_apply, map_smul]
    | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy
  rw [hn, hx, LinearEquiv.apply_symm_apply]

/-- A bounded-above projective model of derived reduction lifts as a complex, not merely
as a derived object. Source: Stacks Project, More on Algebra, Tag 09AR
(blueprint: lem-weil-pbc-nilpotent-projective-complex-lift).

The functor `L`, with its universal counit `ε`, is the total left derived functor of
termwise extension of scalars, as in `lem-pur-derived-change-of-rings` on the one-object
site. Thus `L.obj C` is `C ⊗ᴸ A/I`; no boundedness of `C` is assumed.
Extension of scalars along the quotient map is canonically the termwise quotient by `I`.

Proof:
1. Take the class of all projective A-modules. The lifting property of
   `def-weil-pbc-projective-module` gives closure under sums and summands. If T/IT = 0,
   then T = IT = ... = I^N T = 0. Apply this to a cokernel to see that a map which is
   surjective modulo I is surjective. These verify conditions (1), (2), (3) of Tag 0BCA.
2. By `lem-weil-pbc-nilpotent-projective-module-lift`, lift every E^i to a projective
   A-module. Together with the upper bound on E, this verifies condition (4).
3. Choose an upper bound b on E. Its cohomology vanishes above b, hence so does that
   of the derived reduction of C. By `lem-weil-pbc-nilpotent-module-derived-upper-bound`, the
   cohomology of C vanishes above b as well.
4. Apply `lem-weil-pbc-bounded-above-projective-model` to obtain a bounded-above
   projective representative of C, verifying condition (5), without assuming
   pseudo-coherence or finite Tor amplitude.
5. The representative is K-projective by bounded-above projectivity. Filtered free
   resolutions are K-projective and resolve every complex. Quasi-isomorphisms between
   K-projectives are homotopy equivalences, so scalar extension sends them to isomorphisms
   in the derived category. The generic resolving-class theorem computes a universal
   derived scalar-extension functor on this representative. Uniqueness identifies it
   with L, giving the derived comparison needed in hypothesis (5) of Tag 0BCA.
6. Apply `lem-sc-complex-lift-class-projective`. It supplies P representing C and a
   complex isomorphism between its termwise reduction and the prescribed E. -/
theorem exists_projective_lift_of_nilpotent
    (A : Type u) [CommRing A] (I : Ideal A)
    (hI : ∃ N : ℕ, 1 ≤ N ∧ I ^ N = ⊥)
    [HasDerivedCategory.{w} (ModuleCat.{max u v} A)]
    [HasDerivedCategory.{w'} (ModuleCat.{max u v} (A ⧸ I))]
    (L : DerivedCategory (ModuleCat.{max u v} A) ⥤
      DerivedCategory (ModuleCat.{max u v} (A ⧸ I)))
    (ε : DerivedCategory.Qh ⋙ L ⟶
      @Functor.mapHomotopyCategory _ _ _ _ _ _ _
        (ModuleCat.extendScalars (Ideal.Quotient.mk I))
        (ModuleCat.extendRestrictScalarsAdj (Ideal.Quotient.mk I)).left_adjoint_additive
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
    [L.IsLeftDerivedFunctor ε
      (HomotopyCategory.quasiIso (ModuleCat.{max u v} A) (ComplexShape.up ℤ))]
    (C : DerivedCategory (ModuleCat.{max u v} A))
    (E : CochainComplex (ModuleCat.{max u v} (A ⧸ I)) ℤ)
    (hEbound : ∃ b : ℤ, E.IsStrictlyLE b)
    (hEproj : ∀ i : ℤ, Module.Projective (A ⧸ I) (E.X i))
    (hReduction : Nonempty (L.obj C ≅ DerivedCategory.Q.obj E)) :
    ∃ P : CochainComplex (ModuleCat.{max u v} A) ℤ,
      (∃ b : ℤ, P.IsStrictlyLE b) ∧
      (∀ i : ℤ, Module.Projective A (P.X i)) ∧
      Nonempty (DerivedCategory.Q.obj P ≅ C) ∧
      Nonempty (((ModuleCat.extendScalars (Ideal.Quotient.mk I)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj P ≅ E) := by
  obtain ⟨N, hN, hnil⟩ := hI
  obtain ⟨b, hb⟩ := hEbound
  have : E.IsStrictlyLE b := hb
  obtain ⟨eReduction⟩ := hReduction
  have hC : ∀ i : ℤ, b < i → CategoryTheory.Limits.IsZero
      ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) i).obj C) := by
    apply DerivedCategory.isZero_homology_of_nilpotent_module_reduction
      A I N hN hnil L ε C b
    intro i hi
    have hEi : CategoryTheory.Limits.IsZero (E.homology i) :=
      E.isZero_of_isLE b i hi
    exact hEi.of_iso
      ((DerivedCategory.homologyFunctor _ i).mapIso eReduction ≪≫
        (DerivedCategory.homologyFunctorFactors _ i).app E)
  obtain ⟨K₀, hKproj, hKzero, ⟨eK⟩⟩ :=
    DerivedCategory.exists_boundedAbove_projective_model A C b hC
  have hKbound : K₀.IsStrictlyLE b := (isStrictlyLE_iff K₀ b).2 hKzero
  have hcompute : Nonempty (L.obj (DerivedCategory.Q.obj K₀) ≅
      DerivedCategory.Q.obj
        (((ModuleCat.extendScalars (Ideal.Quotient.mk I)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj K₀)) := by
    classical
    let : (ModuleCat.extendScalars (Ideal.Quotient.mk I)).Additive :=
      (ModuleCat.extendRestrictScalarsAdj (Ideal.Quotient.mk I)).left_adjoint_additive
    have : K₀.IsStrictlyLE b := hKbound
    have (i : ℤ) : CategoryTheory.Projective (K₀.X i) := by
      have := hKproj i
      infer_instance
    have hK : K₀.IsKProjective := isKProjective_of_projective K₀ b
    let H := HomotopyCategory.quotient (ModuleCat.{max u v} A) (.up ℤ)
    let G := (ModuleCat.extendScalars (Ideal.Quotient.mk I)).mapHomotopyCategory (.up ℤ) ⋙
      (DerivedCategory.Qh : HomotopyCategory (ModuleCat.{max u v} (A ⧸ I)) (.up ℤ) ⥤ _)
    let S : Set (HomotopyCategory (ModuleCat.{max u v} A) (.up ℤ)) :=
      {X | ∃ K : CochainComplex (ModuleCat.{max u v} A) ℤ,
        K.IsKProjective ∧ H.obj K = X}
    have hres (X : HomotopyCategory (ModuleCat.{max u v} A) (.up ℤ)) :
        ∃ (X' : HomotopyCategory (ModuleCat.{max u v} A) (.up ℤ)) (s : X' ⟶ X),
          X' ∈ S ∧ HomotopyCategory.quasiIso _ (.up ℤ) s := by
      obtain ⟨T, rfl⟩ := X.quotient_obj_surjective
      obtain ⟨K, s, hs, F, ι, step, hz, hm, hc, he, hsp, hq⟩ :=
        exists_large_filtered_free_resolution.{u, v} T
      have hK := isKProjective_of_filtered_free K F ι step hz hm hc he hsp hq
      refine ⟨H.obj K, H.map s, ⟨K, hK, rfl⟩, ?_⟩
      exact (HomotopyCategory.quotient_map_mem_quasiIso_iff s).2 hs
    have hinv (X Y : HomotopyCategory (ModuleCat.{max u v} A) (.up ℤ)) (s : X ⟶ Y)
        (hX : X ∈ S) (hY : Y ∈ S)
        (hs : HomotopyCategory.quasiIso _ (.up ℤ) s) : IsIso (G.map s) := by
      obtain ⟨K, hK, rfl⟩ := hX
      obtain ⟨K', hK', rfl⟩ := hY
      have : K.IsKProjective := hK
      have : K'.IsKProjective := hK'
      obtain ⟨a, rfl⟩ := H.map_surjective s
      have ha := (IsKProjective.quasiIso_iff a).1
        ((HomotopyCategory.quotient_map_mem_quasiIso_iff a).1 hs)
      have : IsIso (H.map a) :=
        (HomologicalComplex.isIso_quotient_map_iff_homotopyEquivalences a).2 ha
      exact G.map_isIso (H.map a)
    obtain ⟨_, L', ε', hL', _, hcompute'⟩ :=
      Functor.leftDerived_from_resolvingClass (ModuleCat.{max u v} A)
        (DerivedCategory (ModuleCat.{max u v} (A ⧸ I))) G S hres hinv
    have : L'.IsLeftDerivedFunctor ε' (HomotopyCategory.quasiIso _ (.up ℤ)) := hL'
    have : IsIso (ε'.app (H.obj K₀)) := hcompute' (H.obj K₀) ⟨K₀, hK, rfl⟩
    let e := Functor.leftDerivedUnique L' L ε ε'
      (HomotopyCategory.quasiIso (ModuleCat.{max u v} A) (.up ℤ))
    exact ⟨L.mapIso ((DerivedCategory.quotientCompQhIso _).app K₀).symm ≪≫
      e.app (DerivedCategory.Qh.obj (H.obj K₀)) ≪≫ asIso (ε'.app (H.obj K₀))⟩
  obtain ⟨eCompute⟩ := hcompute
  apply AlgebraicGeometry.complex_lift_class_projective A I
    {P | Module.Projective A P} C E
  · intro P hP
    have : Module.Projective A P := hP
    infer_instance
  · exact projective_class_closed A
  · intro P₁ P₂ f _ _ hf
    exact surjective_of_reduction_surjective A I ⟨N, hN, hnil⟩ P₁ P₂ f hf
  · exact ⟨b, hb⟩
  · intro i
    have : Module.Projective (A ⧸ I) (E.X i) := hEproj i
    obtain ⟨P, hP, ⟨eP⟩⟩ :=
      Module.exists_projective_lift_of_nilpotent_ideal A I N hN hnil (E.X i)
    exact ⟨P, hP, ⟨eP.symm.toModuleIso ≪≫ (reductionEquiv A I P).symm.toModuleIso⟩⟩
  · exact ⟨K₀, ⟨b, hKbound⟩, hKproj, ⟨eK⟩,
      ⟨eCompute.symm ≪≫ L.mapIso eK ≪≫ eReduction⟩⟩

end CochainComplex
