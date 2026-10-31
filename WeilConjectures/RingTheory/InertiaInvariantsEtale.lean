/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Algebra.Subalgebra.Operations
public import Mathlib.RingTheory.Ideal.Pointwise
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
import WeilConjectures.RingTheory.InertiaOrbitIdempotents
import WeilConjectures.RingTheory.InvariantOrbitLocalization
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import WeilConjectures.AlgebraicGeometry.EtaleDescentThroughSourceCover
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen

/-!
# Etaleness of finite-group inertia invariants

Source: Stacks Project, `pione.tex`, Tag 0BST, `lemma-inertia-invariants-etale`
(blueprint: lem-dl-a1-inertia-invariants-etale).

The inclusion of the full fixed subring into the inertia fixed subring is etale
on an open neighbourhood of the contraction of the chosen prime.
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

private theorem exists_etale_open_of_pointed_cover
    {X Y Z : Scheme.{u}} (f : X ⟶ Z) (p : Y ⟶ X)
    [Etale p] [Etale (p ≫ f)] (y : Y) :
    ∃ U : X.Opens, p y ∈ U ∧ Etale (U.ι ≫ f) := by
  let U : X.Opens := ⟨Set.range p, p.isOpenMap.isOpen_range⟩
  have hpU : Set.range p ⊆ Set.range U.ι := by
    rw [Scheme.Opens.range_ι]
    exact fun _ hx ↦ hx
  let p' : Y ⟶ U := IsOpenImmersion.lift U.ι p hpU
  have hfac : p' ≫ U.ι = p := IsOpenImmersion.lift_fac U.ι p hpU
  have : Etale (p' ≫ U.ι) := hfac.symm ▸ inferInstance
  have : Etale p' := Etale.of_comp p' U.ι
  have : Surjective p' := ⟨by
    intro x
    obtain ⟨z, hz⟩ := x.2
    refine ⟨z, ?_⟩
    apply Subtype.ext
    exact (congrArg (fun k : Y ⟶ X ↦ k z) hfac).trans hz⟩
  have : Etale (p' ≫ (U.ι ≫ f)) := by
    simpa only [← Category.assoc, hfac] using (inferInstance : Etale (p ≫ f))
  exact ⟨U, ⟨y, rfl⟩, Etale.of_comp_of_surjective_etale (U.ι ≫ f) p'⟩

namespace Ideal

/-- The spectrum of the inertia fixed subring is etale over the full fixed subring
near the contraction of `q`. The action need not be faithful and neither invariant
ring nor the original ring is assumed Noetherian.
Source: Stacks Project, `pione.tex`, Tag 0BST, `lemma-inertia-invariants-etale`
(blueprint: lem-dl-a1-inertia-invariants-etale).

The subgroup `q.inertia G` consists of the elements with `g • r - r ∈ q` for every `r`.
Such an element preserves `q` (Ideal.inertia_le_stabilizer) and acts trivially on
`R / q`, hence on its fraction field. Conversely triviality on that fraction field
implies the displayed congruences. Thus this is exactly the source's inertia group.
The inclusion below sends a full invariant to the same element viewed as an inertia
invariant; the spectrum point is the inverse image of `q` under the subtype map.

Proof:
1. Put C = R^G and B = R^I. Choose an algebraic closure Ω of the residue field at q and
its canonical R-point. The finite stable subalgebra and equivariant idempotent lemmas
give an etale C-algebra A and an inertia-fixed idempotent in A tensor R. Its coset
translates are complete orthogonal and its value at the extended point is one.
2. Flat base change identifies A tensor B with the inertia invariants of A tensor R,
and A with its full invariants. The orbit-sum calculation identifies the localization
of A tensor B at the chosen idempotent with A.
3. This localization L is etale over B, by base change and localization, and over C,
by the preceding isomorphism. Its point obtained by extending the map to Ω contracts
to q in B, since the chosen idempotent evaluates to one.
4. The image of Spec L in Spec B is open and contains the required point. Factor the
etale map through that open image, where it is surjective etale. Source-etale descent
makes the image etale over Spec C. -/
theorem exists_etale_open_inertiaInvariants (R : Type u) [CommRing R]
    (G : Type v) [Group G] [Finite G] [MulSemiringAction G R]
    (q : Ideal R) [q.IsPrime] :
    ∃ U : (Spec (CommRingCat.of (FixedPoints.subring R (q.inertia G)))).Opens,
      PrimeSpectrum.comap (FixedPoints.subring R (q.inertia G)).subtype
        ⟨q, inferInstance⟩ ∈ U ∧
      Etale (U.ι ≫ Spec.map (CommRingCat.ofHom
        (Subring.inclusion (S := FixedPoints.subring R G)
          (T := FixedPoints.subring R (q.inertia G)) (fun _ hx g ↦ hx g.val)))) := by
  classical
  let C := FixedPoints.subring R G
  let B := FixedPoints.subring R (q.inertia G)
  let i : C →+* B := Subring.inclusion (fun _ hx g ↦ hx g.val)
  let : Algebra C B := i.toAlgebra
  let j : B →ₐ[C] R := { B.subtype with commutes' := fun _ ↦ rfl }
  have hInv : Algebra.IsInvariant C R G := ⟨fun x hx ↦ ⟨⟨x, hx⟩, rfl⟩⟩
  let Ω := AlgebraicClosure q.ResidueField
  let η : R →+* Ω :=
    (algebraMap q.ResidueField Ω).comp (algebraMap R q.ResidueField)
  have hη : RingHom.ker η = q := by
    ext x
    simp [η, RingHom.mem_ker, Ideal.algebraMap_residueField_eq_zero]
  obtain ⟨A, _, _, hA, θ, hθ, e, n, r, he, hθe, hH, hr, hc⟩ :=
    exists_etale_inertia_orbit_idempotents C R G q Ω η hη
  have hfixed : ∀ x : R, (∀ h : q.inertia G, h • x = x) ↔ ∃ b : B, j b = x := by
    intro x
    constructor
    · intro hx
      exact ⟨⟨x, hx⟩, rfl⟩
    · rintro ⟨b, rfl⟩ h
      exact b.2 h
  obtain ⟨b, hb, hbij⟩ := AlgHom.exists_invariant_orbit_localization
    C R B G Subtype.val_injective (q.inertia G) j Subtype.val_injective hfixed
    A e he hH n r hr hc
  let S := A ⊗[C] B
  let L := Localization.Away b
  let : Algebra B S := Algebra.TensorProduct.rightAlgebra
  let eBA : B ⊗[C] A ≃ₐ[B] S :=
    { (Algebra.TensorProduct.comm C B A).toRingEquiv with
      commutes' := by intro x; rfl }
  have : Algebra.Etale B S := Algebra.Etale.of_equiv eBA
  have : Algebra.Etale B L := Algebra.Etale.comp B S L
  let eAL : A ≃ₐ[A] L := AlgEquiv.ofBijective (Algebra.ofId A L) hbij
  have : Algebra.Etale A L := Algebra.Etale.of_equiv eAL
  have : Algebra.Etale C L := Algebra.Etale.comp C A L
  let f : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of C) :=
    Spec.map (CommRingCat.ofHom i)
  let p : Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of B) :=
    Spec.map (CommRingCat.ofHom (algebraMap B L))
  have : Etale p := (HasRingHomProperty.Spec_iff (P := @Etale)).mpr
    (RingHom.etale_algebraMap.mpr inferInstance)
  have : Etale (p ≫ f) := by
    have h : Etale (Spec.map (CommRingCat.ofHom (algebraMap C L))) :=
      (HasRingHomProperty.Spec_iff (P := @Etale)).mpr
        (RingHom.etale_algebraMap.mpr inferInstance)
    have hi : algebraMap C B = i := rfl
    simpa only [p, f, IsScalarTower.algebraMap_eq C B L, hi,
      CommRingCat.ofHom_comp, Spec.map_comp] using h
  let θB : S →+* Ω := θ.comp (Algebra.TensorProduct.map (AlgHom.id A A) j).toRingHom
  have hθb : θB b = 1 := by
    change θ (Algebra.TensorProduct.map (AlgHom.id A A) j b) = 1
    rw [hb, hθe]
  have hu : IsUnit (θB b) := hθb.symm ▸ isUnit_one
  let θL : L →+* Ω := IsLocalization.Away.lift b hu
  let y : Spec (CommRingCat.of L) := ⟨RingHom.ker θL, inferInstance⟩
  have hy : p y = PrimeSpectrum.comap B.subtype ⟨q, inferInstance⟩ := by
    apply PrimeSpectrum.ext
    ext x
    change θL (algebraMap B L x) = 0 ↔ (x : R) ∈ q
    rw [IsScalarTower.algebraMap_apply B S L, IsLocalization.Away.lift_eq]
    change θ (Algebra.TensorProduct.map (AlgHom.id A A) j (1 ⊗ₜ x)) = 0 ↔ _
    rw [Algebra.TensorProduct.map_tmul, map_one]
    change θ (Algebra.TensorProduct.includeRight (j x)) = 0 ↔ _
    rw [show θ (Algebra.TensorProduct.includeRight (j x)) = η (j x) from
      RingHom.congr_fun hθ (j x)]
    exact Iff.of_eq (congrArg (fun J : Ideal R ↦ (x : R) ∈ J) hη)
  obtain ⟨U, hyU, hU⟩ := exists_etale_open_of_pointed_cover f p y
  exact ⟨U, hy ▸ hyU, hU⟩

end Ideal
