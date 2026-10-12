/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.ConstructibleSheaf.Restriction

/-!
# Rigidity of morphisms of finite locally constant sheaves

Let `L` and `M` be finite locally constant sheaves of `Λ`-modules on the small étale site of a
scheme `T`. A morphism `φ : L ⟶ M` whose stalk vanishes at one geometric point of every
connected component of `T` is zero (blueprint `lem-pur-lisse-morphism-rigidity`, clause (2)):
the image of `φ` is locally constant, so the set of points at which its stalks vanish is open
and closed (`AlgebraicGeometry.Etale.isClopen_stalkZeroLocus`); it meets every connected
component, hence is everything.

## Main statements

- `AlgebraicGeometry.Etale.mem_stalkZeroLocus_of_isZero`: for a locally constant sheaf, the
  vanishing of the stalk at one geometric point over `x` gives the vanishing at all of them.
- `AlgebraicGeometry.Etale.eq_zero_of_sheafFiber_map_eq_zero`: rigidity of morphisms.
- `AlgebraicGeometry.Etale.eq_of_sheafFiber_map_eq`: two morphisms agreeing at one geometric
  point of every connected component agree.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable {Λ : Type (u + 1)} [Ring Λ] {X : Scheme.{u}}

/-- For a locally constant sheaf `I`, the vanishing of the stalk of `I` at a single geometric
point lying over `x` implies its vanishing at every geometric point over `x`: over a member of a
trivialising cover through `x` all these stalks are the value of a constant sheaf. -/
lemma mem_stalkZeroLocus_of_isZero (I : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [IsLocallyConstantSheaf I] {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ X)
    (hs : IsZero ((pointSmallEtale s).sheafFiber.obj I)) :
    s.base (IsLocalRing.closedPoint Ω) ∈ stalkZeroLocus I := by
  obtain ⟨⟨𝒰, hc⟩⟩ := IsLocallyConstantSheaf.nonempty_locallyConstantDatum (F := I)
  obtain ⟨i, v, hv⟩ := 𝒰.exists_eq (s.base (IsLocalRing.closedPoint Ω))
  have : Etale (𝒰.f i) := 𝒰.map_prop i
  obtain ⟨N, ⟨e⟩⟩ := ((isConstant_over_iff_upperStar _ (𝒰.etalePrecoverageToEtale i) I).1
    (hc i)).mem_essImage
  have hN : IsZero N := (isZero_sheafFiber_iff_of_iso I (𝒰.f i) e.symm s ⟨v, hv⟩).1 hs
  intro Ω' _ _ s' hs'
  exact (isZero_sheafFiber_iff_of_iso I (𝒰.f i) e.symm s' ⟨v, hv.trans hs'.symm⟩).2 hN

variable {L M : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)}

/-- The stalk of the image of `χ` vanishes wherever the stalk of `χ` does: taking stalks is
exact. -/
lemma isZero_sheafFiber_image_of_map_eq_zero (χ : L ⟶ M) {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (s : Spec (.of Ω) ⟶ X) (h₀ : (pointSmallEtale s).sheafFiber.map χ = 0) :
    IsZero ((pointSmallEtale s).sheafFiber.obj (kernel (cokernel.π χ))) := by
  set F := (pointSmallEtale s).sheafFiber (A := ModuleCat.{u + 1} Λ)
  have : IsIso (F.map (cokernel.π χ)) := by
    have h₁ := PreservesCokernel.π_iso_hom F χ
    have : IsIso (cokernel.π (F.map χ)) := cokernel.π_of_zero h₀
    rw [← h₁] at this
    exact IsIso.of_isIso_comp_right _ (PreservesCokernel.iso F χ).hom
  exact (isZero_kernel_of_mono _).of_iso (PreservesKernel.iso F (cokernel.π χ))

/-- A sheaf of `Λ`-modules on `X_ét` all of whose stalks vanish is zero. -/
lemma isZero_of_forall_mem_stalkZeroLocus (I : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (hall : ∀ x : X, x ∈ stalkZeroLocus I) : IsZero I := by
  have : IsIso (0 : I ⟶ I) := isIso_of_isIso_sheafFiber_map _ fun x ↦ by
    have hx : IsZero ((X.uliftPointSmallEtale x).sheafFiber.obj I) :=
      (hall x _ (X.algClosurePoint x) (X.algClosurePoint_base x _)).of_iso
        (((pointSmallEtale (X.algClosurePoint x)).uliftSheafFiberIso _).app I)
    exact ⟨0, hx.eq_of_src _ _, hx.eq_of_src _ _⟩
  rw [IsZero.iff_id_eq_zero, ← IsIso.hom_inv_id (0 : I ⟶ I), zero_comp]

/-- Blueprint `lem-pur-lisse-morphism-rigidity`: Rigidity of morphisms of finite locally
constant sheaves

*Rigidity of sections*, clause (2). Let `φ : L ⟶ M` be a morphism of finite locally constant
sheaves of `Λ`-modules on `X_ét`. If every connected component of `X` contains the image of a
geometric point at which the stalk of `φ` vanishes, then `φ = 0`. The image of `φ` is locally
constant, its stalks vanish on an open and closed set, which meets every connected component. -/
theorem eq_zero_of_sheafFiber_map_eq_zero
    [IsFiniteLocallyConstantSheaf (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
      (CA := fun M : ModuleCat.{u + 1} Λ ↦ M) L]
    [IsFiniteLocallyConstantSheaf (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
      (CA := fun M : ModuleCat.{u + 1} Λ ↦ M) M] (φ : L ⟶ M)
    (h : ∀ x : X, ∃ (Ω : Type u) (_ : Field Ω) (_ : IsSepClosed Ω) (s : Spec (.of Ω) ⟶ X),
      s.base (IsLocalRing.closedPoint Ω) ∈ connectedComponent x ∧
        (pointSmallEtale s).sheafFiber.map φ = 0) :
    φ = 0 := by
  have := (IsLocallyConstantSheaf.kernel_and_cokernel φ).2
  have := (IsLocallyConstantSheaf.kernel_and_cokernel (cokernel.π φ)).1
  set I := kernel (cokernel.π φ)
  have hall : ∀ x : X, x ∈ stalkZeroLocus I := by
    intro x
    obtain ⟨Ω, _, _, s, hs, hφ⟩ := h x
    have hmem := mem_stalkZeroLocus_of_isZero I s (isZero_sheafFiber_image_of_map_eq_zero φ s hφ)
    exact isPreconnected_connectedComponent.subset_isClopen (isClopen_stalkZeroLocus I)
      ⟨_, hs, hmem⟩ (mem_connectedComponent)
  have hI : IsZero I := isZero_of_forall_mem_stalkZeroLocus I hall
  rw [← kernel.lift_ι (cokernel.π φ) φ (cokernel.condition φ),
    hI.eq_of_tgt (kernel.lift _ φ _) 0, zero_comp]

/-- Blueprint `lem-pur-lisse-morphism-rigidity`: Rigidity of morphisms of finite locally
constant sheaves

The final assertion of clause (2): two morphisms of finite locally constant sheaves which agree
at one geometric point of every connected component agree; in particular, on a connected
scheme, two morphisms agreeing at one geometric point agree. -/
theorem eq_of_sheafFiber_map_eq
    [IsFiniteLocallyConstantSheaf (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
      (CA := fun M : ModuleCat.{u + 1} Λ ↦ M) L]
    [IsFiniteLocallyConstantSheaf (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
      (CA := fun M : ModuleCat.{u + 1} Λ ↦ M) M] (φ ψ : L ⟶ M)
    (h : ∀ x : X, ∃ (Ω : Type u) (_ : Field Ω) (_ : IsSepClosed Ω) (s : Spec (.of Ω) ⟶ X),
      s.base (IsLocalRing.closedPoint Ω) ∈ connectedComponent x ∧
        (pointSmallEtale s).sheafFiber.map φ = (pointSmallEtale s).sheafFiber.map ψ) :
    φ = ψ := by
  rw [← sub_eq_zero]
  refine eq_zero_of_sheafFiber_map_eq_zero (φ - ψ) fun x ↦ ?_
  obtain ⟨Ω, _, _, s, hs, hφ⟩ := h x
  have : PreservesBinaryBiproducts ((pointSmallEtale s).sheafFiber (A := ModuleCat.{u + 1} Λ)) :=
    preservesBinaryBiproducts_of_preservesBinaryProducts _
  have : ((pointSmallEtale s).sheafFiber (A := ModuleCat.{u + 1} Λ)).Additive :=
    Functor.additive_of_preservesBinaryBiproducts _
  exact ⟨Ω, inferInstance, inferInstance, s, hs, by rw [Functor.map_sub, hφ, sub_self]⟩

end Etale

end AlgebraicGeometry
