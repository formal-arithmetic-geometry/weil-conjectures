/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q48, SHEAF group G4
-/
module

public import WeilConjectures.DeligneLaumon.Reduction.Weights
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import WeilConjectures.WeilSheaf.Triangle
public import WeilConjectures.WeilSheaf.HomologyShift
public import WeilConjectures.WeilSheaf.Category
public import Sheaf.Paper.SfWeilSheafComplex
public import Sheaf.Paper.SfConstructibleHeart
public import Sheaf.LinearAlgebra.FrobeniusModuleWeights
import Sheaf.LinearAlgebra.FrobeniusModuleMixedSubquotient
import Sheaf.LinearAlgebra.FrobeniusModuleExtensionBounds
import Mathlib.LinearAlgebra.Isomorphisms

/-! # Stability of mixed upper weight bounds

Source: Weil-conjectures blueprint, sec-deligne-laumon-general/sk-d-dl-general-weights,
main-20261015, lemma lem-a1-mixed-direct-summand, order 3155
(blueprint: lem-a1-mixed-direct-summand).

## Main statements

- The imported sheaf `of_mono`, `of_epi`, `of_shortExact`, and `of_retract` give
  subobjects, quotients, extensions, and direct summands.
- `FrobeniusModule.mixedOfWeightsAtMost_stability`: the analogous assertions for the
  recorded finite stable-filtration definition of mixed Frobenius modules.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section

universe u₁ u₂ u₃ v

namespace FrobeniusModule

-- Mixedness is invariant under equivariant linear equivalences. The extension
-- theorem applied to 0 → A → B supplies this without unfolding a filtration.
private theorem mixed_of_equiv
    (p a ell : ℕ) [Fact p.Prime] (ha : 1 ≤ a)
    [Fact ell.Prime] (hellp : ell ≠ p) (Qlb : Type v) [Field Qlb]
    [Algebra ℚ_[ell] Qlb] (hQ : IsAlgClosure ℚ_[ell] Qlb)
    (iota : Qlb ≃+* ℂ) (w : ℝ)
    (A : FrobeniusModule.{u₁, v} Qlb) (B : FrobeniusModule.{u₂, v} Qlb)
    (e : A.carrier ≃ₗ[Qlb] B.carrier)
    (he : ∀ x, e (A.frobenius x) = B.frobenius (e x))
    (hB : IsMixedOfWeightsAtMost p a ell ha hellp Qlb hQ iota B w) :
    IsMixedOfWeightsAtMost p a ell ha hellp Qlb hQ iota A w := by
  let Z : FrobeniusModule Qlb :=
    { carrier := (⊥ : Submodule Qlb A.carrier)
      frobenius := LinearEquiv.refl Qlb _ }
  have hZ : IsMixedOfWeightsAtMost p a ell ha hellp Qlb hQ iota Z w := by
    refine ⟨0, (fun _ => ⊥), rfl, ?_, ?_, ?_, ?_⟩
    · exact Subsingleton.elim _ _
    · intro r
      exact r.elim0
    · intro r
      exact Submodule.map_bot _
    · intro r
      exact r.elim0
  apply IsMixedOfWeightsAtMost.of_shortExact p a ell ha hellp Qlb hQ iota
    Z A B 0 e.toLinearMap (by intro x; simp) he
    (fun x y _ => Subsingleton.elim x y) ?_ e.surjective w hZ hB
  intro x
  constructor
  · intro hx
    exact ⟨0, (e.injective (hx.trans (map_zero e).symm)).symm⟩
  · rintro ⟨z, rfl⟩
    simp

private theorem stable_range
    {K : Type v} [Field K]
    (A : FrobeniusModule.{u₁, v} K) (B : FrobeniusModule.{u₂, v} K)
    (f : A.carrier →ₗ[K] B.carrier)
    (hf : ∀ x, f (A.frobenius x) = B.frobenius (f x)) :
    (LinearMap.range f).map B.frobenius.toLinearMap = LinearMap.range f := by
  apply le_antisymm
  · rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
    exact ⟨A.frobenius x, hf x⟩
  · rintro _ ⟨x, rfl⟩
    refine ⟨f (A.frobenius.symm x), ⟨_, rfl⟩, ?_⟩
    change B.frobenius (f (A.frobenius.symm x)) = f x
    rw [← hf, A.frobenius.apply_symm_apply]

private theorem stable_ker
    {K : Type v} [Field K]
    (A : FrobeniusModule.{u₁, v} K) (B : FrobeniusModule.{u₂, v} K)
    (g : A.carrier →ₗ[K] B.carrier)
    (hg : ∀ x, g (A.frobenius x) = B.frobenius (g x)) :
    (LinearMap.ker g).map A.frobenius.toLinearMap = LinearMap.ker g := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    change g (A.frobenius x) = 0
    rw [hg, (LinearMap.mem_ker.mp hx), map_zero]
  · intro x hx
    refine ⟨A.frobenius.symm x, ?_, A.frobenius.apply_symm_apply x⟩
    change g (A.frobenius.symm x) = 0
    apply B.frobenius.injective
    rw [← hg, A.frobenius.apply_symm_apply, LinearMap.mem_ker.mp hx, map_zero]

private theorem mixed_of_injective
    (p a ell : ℕ) [Fact p.Prime] (ha : 1 ≤ a)
    [Fact ell.Prime] (hellp : ell ≠ p) (Qlb : Type v) [Field Qlb]
    [Algebra ℚ_[ell] Qlb] (hQ : IsAlgClosure ℚ_[ell] Qlb)
    (iota : Qlb ≃+* ℂ) (w : ℝ)
    (A : FrobeniusModule.{u₁, v} Qlb) (B : FrobeniusModule.{u₂, v} Qlb)
    (f : A.carrier →ₗ[Qlb] B.carrier)
    (hf : ∀ x, f (A.frobenius x) = B.frobenius (f x))
    (hinj : Function.Injective f)
    (hB : IsMixedOfWeightsAtMost p a ell ha hellp Qlb hQ iota B w) :
    IsMixedOfWeightsAtMost p a ell ha hellp Qlb hQ iota A w := by
  let S := LinearMap.range f
  have hS := stable_range A B f hf
  let U : Submodule Qlb S := ⊥
  have hU : U.map (B.frobenius.ofSubmodules S S hS).toLinearMap = U :=
    Submodule.map_bot _
  let C : FrobeniusModule Qlb :=
    { carrier := S ⧸ U
      frobenius := Submodule.Quotient.equiv U U (B.frobenius.ofSubmodules S S hS) hU }
  have hC := IsMixedOfWeightsAtMost.subquotient p a ell ha hellp Qlb hQ iota B w hB
    S hS U hU
  let e : A.carrier ≃ₗ[Qlb] C.carrier :=
    (LinearEquiv.ofInjective f hinj).trans (U.quotEquivOfEqBot rfl).symm
  apply mixed_of_equiv p a ell ha hellp Qlb hQ iota w A C e ?_ hC
  intro x
  change Submodule.Quotient.mk (LinearEquiv.ofInjective f hinj (A.frobenius x)) =
    Submodule.Quotient.mk
      ((B.frobenius.ofSubmodules S S hS) (LinearEquiv.ofInjective f hinj x))
  congr 1
  exact Subtype.ext (hf x)

/-- The same four stability assertions for finite-dimensional Frobenius modules,
using mixedness defined by a finite stable filtration, with no semisimplicity assumption.
An equivariant split inclusion and projection express a direct summand.

Source: blueprint main-20261015, sec-deligne-laumon-general/sk-d-dl-general-weights,
lemma lem-a1-mixed-direct-summand, final paragraph
(blueprint: lem-a1-mixed-direct-summand).

Proof: for an injective equivariant map identify its source with the stable image,
and use lem-a1-subquotient-extension-bounds. For a surjective equivariant map identify
its target with the quotient by the stable kernel, and apply the same lemma. Given
an exact sequence, concatenate the image of a mixed filtration of the first term
with inverse images of a mixed filtration of the last term; exactness identifies
the successive quotients. This is lem-a1-extension-bounds. Finally a split inclusion
is injective, so the subobject assertion applies. In the Lean proof, invariance under
equivariant linear equivalence follows from the extension theorem for an exact
sequence starting at zero, whose mixed filtration has length zero. The concrete
subquotients are the stable image modulo zero and the whole space modulo the
stable kernel. These arguments cover zero modules and nonsemisimple Frobenius.
-/
theorem mixedOfWeightsAtMost_stability
    (p a ell : ℕ) [Fact p.Prime] (ha : 1 ≤ a)
    [Fact ell.Prime] (hellp : ell ≠ p) (Qlb : Type v) [Field Qlb]
    [Algebra ℚ_[ell] Qlb] (hQ : IsAlgClosure ℚ_[ell] Qlb)
    (iota : Qlb ≃+* ℂ) (w : ℝ) :
    (∀ (A : FrobeniusModule.{u₁, v} Qlb) (B : FrobeniusModule.{u₂, v} Qlb)
      (f : A.carrier →ₗ[Qlb] B.carrier),
      (∀ x : A.carrier, f (A.frobenius x) = B.frobenius (f x)) →
      Function.Injective f →
      IsMixedOfWeightsAtMost p a ell ha hellp Qlb hQ iota B w →
      IsMixedOfWeightsAtMost p a ell ha hellp Qlb hQ iota A w) ∧
    (∀ (A : FrobeniusModule.{u₁, v} Qlb) (B : FrobeniusModule.{u₂, v} Qlb)
      (g : A.carrier →ₗ[Qlb] B.carrier),
      (∀ x : A.carrier, g (A.frobenius x) = B.frobenius (g x)) →
      Function.Surjective g →
      IsMixedOfWeightsAtMost p a ell ha hellp Qlb hQ iota A w →
      IsMixedOfWeightsAtMost p a ell ha hellp Qlb hQ iota B w) ∧
    (∀ (A : FrobeniusModule.{u₁, v} Qlb) (B : FrobeniusModule.{u₂, v} Qlb)
      (C : FrobeniusModule.{u₃, v} Qlb)
      (f : A.carrier →ₗ[Qlb] B.carrier) (g : B.carrier →ₗ[Qlb] C.carrier),
      (∀ x : A.carrier, f (A.frobenius x) = B.frobenius (f x)) →
      (∀ x : B.carrier, g (B.frobenius x) = C.frobenius (g x)) →
      Function.Injective f → Function.Exact f g → Function.Surjective g →
      IsMixedOfWeightsAtMost p a ell ha hellp Qlb hQ iota A w →
      IsMixedOfWeightsAtMost p a ell ha hellp Qlb hQ iota C w →
      IsMixedOfWeightsAtMost p a ell ha hellp Qlb hQ iota B w) ∧
    (∀ (A : FrobeniusModule.{u₁, v} Qlb) (B : FrobeniusModule.{u₂, v} Qlb)
      (i : A.carrier →ₗ[Qlb] B.carrier) (r : B.carrier →ₗ[Qlb] A.carrier),
      (∀ x : A.carrier, i (A.frobenius x) = B.frobenius (i x)) →
      (∀ x : B.carrier, r (B.frobenius x) = A.frobenius (r x)) →
      r.comp i = LinearMap.id →
      IsMixedOfWeightsAtMost p a ell ha hellp Qlb hQ iota B w →
      IsMixedOfWeightsAtMost p a ell ha hellp Qlb hQ iota A w) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact mixed_of_injective p a ell ha hellp Qlb hQ iota w
  · intro A B g hg hsurj hA
    let S : Submodule Qlb A.carrier := ⊤
    have hS : S.map A.frobenius.toLinearMap = S := by
      rw [Submodule.map_top]
      exact LinearMap.range_eq_top.mpr A.frobenius.surjective
    let T : FrobeniusModule Qlb :=
      { carrier := S
        frobenius := A.frobenius.ofSubmodules S S hS }
    let g' : T.carrier →ₗ[Qlb] B.carrier := g.comp S.subtype
    have hg' : ∀ x, g' (T.frobenius x) = B.frobenius (g' x) := fun x => hg x
    have hsurj' : Function.Surjective g' := by
      intro y
      obtain ⟨x, rfl⟩ := hsurj y
      exact ⟨⟨x, Submodule.mem_top⟩, rfl⟩
    let U := LinearMap.ker g'
    have hU := stable_ker T B g' hg'
    let C : FrobeniusModule Qlb :=
      { carrier := S ⧸ U
        frobenius := Submodule.Quotient.equiv U U T.frobenius hU }
    have hC := IsMixedOfWeightsAtMost.subquotient p a ell ha hellp Qlb hQ iota A w hA
      S hS U hU
    let e : C.carrier ≃ₗ[Qlb] B.carrier := g'.quotKerEquivOfSurjective hsurj'
    have he : ∀ x, e (C.frobenius x) = B.frobenius (e x) := by
      intro x
      obtain ⟨x, rfl⟩ := U.mkQ_surjective x
      exact hg' x
    apply mixed_of_equiv p a ell ha hellp Qlb hQ iota w B C e.symm ?_ hC
    intro x
    apply e.injective
    rw [e.apply_symm_apply, he, e.apply_symm_apply]
  · intro A B C f g hf hg hinj hexact hsurj hA hC
    exact IsMixedOfWeightsAtMost.of_shortExact p a ell ha hellp Qlb hQ iota
      A B C f g hf hg hinj hexact hsurj w hA hC
  · intro A B i r hi _ hri hB
    apply mixed_of_injective p a ell ha hellp Qlb hQ iota w A B i hi ?_ hB
    have hleft : Function.LeftInverse r i := fun x =>
      congrArg (fun f : A.carrier →ₗ[Qlb] A.carrier => f x) hri
    exact hleft.injective

end FrobeniusModule
