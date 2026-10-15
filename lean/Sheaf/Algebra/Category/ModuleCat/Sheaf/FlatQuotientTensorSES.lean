/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NO
-/
module

public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.Flat
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalFree
import Sheaf.Algebra.Homology.FlatCoverFunctor
import Mathlib.CategoryTheory.Abelian.Refinements
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor

/-!
# Tensor exactness for a flat quotient of module sheaves

Source: Stacks Project, Modules on Sites, Tags 03EX (2) and 03EY (2)
(blueprint: lem-weil-pbc-site-flat-quotient-tensor-ses).
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

/-- The left-injectivity chase for three tensor rows, carried out after epic refinements. -/
private theorem mono_bottom_of_tensor_rows
    {A : Type*} [Category* A] [Abelian A]
    {L M N : ShortComplex A} (φ : L ⟶ M) (ψ : M ⟶ N)
    (hL : L.Exact) [Mono M.f] [Mono φ.τ₃] [Epi ψ.τ₁]
    (w : φ.τ₁ ≫ ψ.τ₁ = 0) (w₂ : φ.τ₂ ≫ ψ.τ₂ = 0)
    (hcol : (ShortComplex.mk φ.τ₂ ψ.τ₂ w₂).Exact) : Mono N.f := by
  rw [Preadditive.mono_iff_cancel_zero]
  intro Z x hx
  obtain ⟨Z₁, π₁, hπ₁, a, ha⟩ := surjective_up_to_refinements_of_epi ψ.τ₁ x
  have haz : (a ≫ M.f) ≫ ψ.τ₂ = 0 := by
    rw [Category.assoc, ← ψ.comm₁₂, ← Category.assoc, ← ha, Category.assoc, hx,
      Limits.comp_zero]
  obtain ⟨Z₂, π₂, hπ₂, b, hb⟩ := hcol.exact_up_to_refinements (a ≫ M.f) haz
  have hbz : b ≫ L.g = 0 := by
    rw [← cancel_mono φ.τ₃, Limits.zero_comp, Category.assoc, ← φ.comm₂₃,
      ← Category.assoc, ← hb]
    simp only [Category.assoc, M.zero, Limits.comp_zero]
  obtain ⟨Z₃, π₃, hπ₃, c, hc⟩ := hL.exact_up_to_refinements b hbz
  have heq : π₃ ≫ π₂ ≫ a = c ≫ φ.τ₁ := by
    rw [← cancel_mono M.f]
    calc
      (π₃ ≫ π₂ ≫ a) ≫ M.f = π₃ ≫ (π₂ ≫ (a ≫ M.f)) := by
        simp only [Category.assoc]
      _ = π₃ ≫ (b ≫ φ.τ₂) := by rw [hb]
      _ = c ≫ L.f ≫ φ.τ₂ := by rw [← Category.assoc, hc, Category.assoc]
      _ = (c ≫ φ.τ₁) ≫ M.f := by rw [Category.assoc, φ.comm₁₂]
  rw [← cancel_epi π₁, Limits.comp_zero, ← cancel_epi π₂, Limits.comp_zero,
    ← cancel_epi π₃, Limits.comp_zero]
  calc
    π₃ ≫ π₂ ≫ π₁ ≫ x = (π₃ ≫ π₂ ≫ a) ≫ ψ.τ₁ := by
      rw [ha]
      simp only [Category.assoc]
    _ = (c ≫ φ.τ₁) ≫ ψ.τ₁ := by rw [heq]
    _ = 0 := by rw [Category.assoc, w, Limits.comp_zero]

namespace SheafOfModules

/-- A short exact sequence with flat quotient remains short exact after tensoring with
any module sheaf. If its middle term is flat, its first term is flat as well.
Source: Stacks Project, Modules on Sites, Tags 03EX (2) and 03EY (2)
(blueprint: lem-weil-pbc-site-flat-quotient-tensor-ses).

Proof: The tensor-Hom adjunction and additivity of
`lem-pc-sheaf-modules-tensor-closed` make tensoring right exact; its natural symmetry
allows either tensor orientation. Choose the functorial flat cover P → N from
`lem-pc-sites-modules-functorial-flat-cover`, and write Q for its kernel. Form the tensor
rows with Q, P and N. The middle row is short exact because P is flat; the others and
all columns are right exact. Flatness of the quotient makes H ⊗ Q → H ⊗ P monic.
For an element in the kernel of F ⊗ N → G ⊗ N, lift to F ⊗ P; its image lifts from
G ⊗ Q, whose image in H ⊗ Q vanishes by that monomorphism. Lift again from F ⊗ Q
and subtract; the middle-row monomorphism makes the difference zero. These are
categorical lifts after epic pullback refinements, so the argument needs no points
or sectionwise surjectivity. This proves the first assertion with right exactness.
If G is flat, apply the first assertion with both ends U and V of an arbitrary mono
U → V. The composite F ⊗ U → G ⊗ U → G ⊗ V is monic and factors through
F ⊗ V. Thus F ⊗ U → F ⊗ V is monic. Together with right exactness and symmetry,
this says the tensor functor defining `IsFlat F` is exact. -/
theorem flat_quotient_tensor_shortExact
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u})
    (S : ShortComplex (CategoryTheory.ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)))
    (hS : S.ShortExact) (hH : IsFlat S.X₃) :
    (∀ N : CategoryTheory.ringedSiteModules.{u}
        ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R),
      (S.map (@tensorRight _ _ (monoidalCategory R) N)).ShortExact) ∧
      (IsFlat S.X₂ → IsFlat S.X₁) := by
  let := monoidalCategory R
  let := symmetricCategory R
  let := monoidalClosed (R := R)
  let A := CategoryTheory.ringedSiteModules.{u}
    ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)
  have hright (N : A) : Limits.PreservesFiniteColimits (tensorRight N) :=
    Limits.preservesFiniteColimits_of_natIso (BraidedCategory.tensorLeftIsoTensorRight N)
  have hrex (T : ShortComplex A) (hT : T.ShortExact) (N : A) :
      (T.map (tensorRight N)).Exact ∧ Epi ((tensorRight N).map T.g) := by
    have := hright N
    exact (Functor.preservesFiniteColimits_iff_forall_exact_map_and_epi
      (tensorRight N)).1 inferInstance T hT
  have hlex (N : A) (hN : IsFlat N) : Limits.PreservesFiniteLimits (tensorLeft N) := by
    have : Limits.PreservesFiniteLimits (tensorRight N) := hN.1
    exact Limits.preservesFiniteLimits_of_natIso (BraidedCategory.tensorLeftIsoTensorRight N).symm
  have hleftrex (T : ShortComplex A) (hT : T.ShortExact) (N : A) :
      (T.map (tensorLeft N)).Exact ∧ Epi ((tensorLeft N).map T.g) :=
    (Functor.preservesFiniteColimits_iff_forall_exact_map_and_epi
      (tensorLeft N)).1 inferInstance T hT
  have hseq (N : A) : (S.map (tensorRight N)).ShortExact := by
    obtain ⟨F, π, hπ⟩ := exists_functorial_flat_cover J R
    have hP := (hπ N).1
    have : Epi (π.app N) := (hπ N).2
    let T := ShortComplex.kernelSequence (π.app N)
    have : Epi T.g := (hπ N).2
    have hT : T.ShortExact := ⟨ShortComplex.kernelSequence_exact _⟩
    have : Limits.PreservesFiniteLimits (tensorRight T.X₂) := hP.1
    have := hright T.X₂
    have hmiddle := hS.map_of_exact (tensorRight T.X₂)
    have := hmiddle.mono_f
    let φ := S.mapNatTrans ((curriedTensor A).flip.map T.f)
    let ψ := S.mapNatTrans ((curriedTensor A).flip.map T.g)
    have : Mono φ.τ₃ := by
      change Mono ((tensorLeft S.X₃).map T.f)
      have := hlex S.X₃ hH
      have := hT.mono_f
      infer_instance
    have : Epi ψ.τ₁ := (hleftrex T hT S.X₁).2
    have hw₁ : φ.τ₁ ≫ ψ.τ₁ = 0 := by
      change (tensorLeft S.X₁).map T.f ≫ (tensorLeft S.X₁).map T.g = 0
      rw [← Functor.map_comp, T.zero, Functor.map_zero]
    have hw₂ : φ.τ₂ ≫ ψ.τ₂ = 0 := by
      change (tensorLeft S.X₂).map T.f ≫ (tensorLeft S.X₂).map T.g = 0
      rw [← Functor.map_comp, T.zero, Functor.map_zero]
    have hcol : (ShortComplex.mk φ.τ₂ ψ.τ₂ hw₂).Exact :=
      (hleftrex T hT S.X₂).1
    have : Mono (S.map (tensorRight N)).f :=
      mono_bottom_of_tensor_rows φ ψ (hrex S hS T.X₁).1 hw₁ hw₂ hcol
    exact ShortComplex.ShortExact.mk' (hrex S hS N).1 this (hrex S hS N).2
  refine ⟨hseq, ?_⟩
  intro hG
  have hmono (U V : A) (f : U ⟶ V) [Mono f] : Mono ((tensorLeft S.X₁).map f) := by
    have : Mono (S.f ▷ U) := (hseq U).mono_f
    have := hlex S.X₂ hG
    have : Mono (S.X₂ ◁ f) := (tensorLeft S.X₂).map_mono f
    have hcomp : Mono ((S.f ▷ U) ≫ (S.X₂ ◁ f)) := mono_comp _ _
    have hfac : (S.X₁ ◁ f) ≫ (S.f ▷ V) = (S.f ▷ U) ≫ (S.X₂ ◁ f) :=
      whisker_exchange S.f f
    exact mono_of_mono_fac hfac
  have : (tensorLeft S.X₁).PreservesMonomorphisms := ⟨fun f _ ↦ hmono _ _ f⟩
  have : Limits.PreservesFiniteLimits (tensorLeft S.X₁) := by
    apply (Functor.preservesFiniteLimits_iff_forall_exact_map_and_mono
      (tensorLeft S.X₁)).2
    intro T hT
    have := hT.mono_f
    exact ⟨(hleftrex T hT S.X₁).1, inferInstance⟩
  exact ⟨Limits.preservesFiniteLimits_of_natIso (BraidedCategory.tensorLeftIsoTensorRight S.X₁),
    hright S.X₁⟩

end SheafOfModules
