/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import WeilConjectures.RingTheory.RootLiftingEtaleRetraction
import WeilConjectures.RingTheory.HenselianLocalRootLifting

/-!
# Existence of retractions of étale algebras over henselian local rings

Let `S` be a henselian local ring and `B` an étale `S`-algebra. Every prime `q'` of `B` over the
maximal ideal of `S` with trivial residue field extension is the preimage of the maximal ideal
under some `S`-algebra map `B →ₐ[S] S` (`exists_algHom_of_henselianLocalRing_etale`).

## Implementation details

Locally at an element outside `q'`, the étale algebra has a standard étale presentation. The
given residue field point corresponds to a simple root of the defining polynomial, which lifts
to `S` since `S` is henselian; the universal property of the standard étale algebra and
localization then give the map on `B`.

## References

* [Stacks, Tag 04GG]
-/

@[expose] public section

universe u

open AlgebraicGeometry

/-- Over a henselian local ring `S`, an étale `S`-algebra `B` with a prime `q'` over the maximal
ideal having trivial residue field extension admits an `S`-algebra map `B →ₐ[S] S` under which
the preimage of the maximal ideal is `q'`.
-/
theorem exists_algHom_of_henselianLocalRing_etale
    {S B : Type u} [CommRing S] [CommRing B] [HenselianLocalRing S]
    (φ : S →+* B)
    [AlgebraicGeometry.Etale (Scheme.Spec.map (CommRingCat.ofHom φ).op)]
    (q' : Ideal B) [q'.IsPrime]
    (hq : q'.comap φ = IsLocalRing.maximalIdeal S)
    (hres : Function.Bijective
      (Ideal.ResidueField.map (IsLocalRing.maximalIdeal S) q' φ hq.symm)) :
    letI : Algebra S B := φ.toAlgebra
    ∃ σ : B →ₐ[S] S,
      (IsLocalRing.maximalIdeal S).comap σ.toRingHom = q' := by
  open CategoryTheory in
  exact by
    let : Algebra S B := φ.toAlgebra
    let x : PrimeSpectrum B := ⟨q', inferInstance⟩
    let f := Spec.map (CommRingCat.ofHom φ)
    let y : PrimeSpectrum S := f x
    let β : B →+* (Spec (.of B)).residueField x :=
      (Scheme.Spec.residueFieldIso (.of B) x).inv.hom.comp (algebraMap B q'.ResidueField)
    let α : S →+* (Spec (.of S)).residueField y :=
      (Scheme.Spec.residueFieldIso (.of S) y).inv.hom.comp
        (algebraMap S y.asIdeal.ResidueField)
    have hnat : β.comp φ = (f.residueFieldMap x).hom.comp α := by
      have hn : CommRingCat.ofHom φ ≫
          (CommRingCat.ofHom (algebraMap B q'.ResidueField) ≫
            (Scheme.Spec.residueFieldIso (.of B) x).inv) =
          (CommRingCat.ofHom (algebraMap S y.asIdeal.ResidueField) ≫
            (Scheme.Spec.residueFieldIso (.of S) y).inv) ≫ f.residueFieldMap x := by
        erw [Scheme.Spec.algebraMap_residueFieldIso_inv,
          Scheme.Spec.algebraMap_residueFieldIso_inv]
        change CommRingCat.ofHom φ ≫
          ((Scheme.ΓSpecIso (.of B)).inv ≫ (Spec (.of B)).Γevaluation x) =
          ((Scheme.ΓSpecIso (.of S)).inv ≫ (Spec (.of S)).Γevaluation y) ≫
            f.residueFieldMap x
        simp only [CategoryTheory.Category.assoc, Scheme.ΓSpecIso_inv_naturality_assoc]
        erw [Scheme.Γevaluation_naturality f x]
      exact congrArg (fun h : CommRingCat.of S ⟶ (Spec (.of B)).residueField x ↦ h.hom) hn
    have hsurj : Function.Surjective ((algebraMap B q'.ResidueField).comp φ) := by
      have heq : (algebraMap B q'.ResidueField).comp φ =
          (Ideal.ResidueField.map (IsLocalRing.maximalIdeal S) q' φ hq.symm).comp
            (algebraMap S (IsLocalRing.maximalIdeal S).ResidueField) := by
        ext s
        exact (Ideal.ResidueField.map_algebraMap _ _ _ _ s).symm
      rw [heq]
      exact hres.2.comp (IsLocalRing.maximalIdeal S).algebraMap_residueField_surjective
    have hγ : Function.Surjective (β.comp φ) :=
      (Scheme.Spec.residueFieldIso (.of B) x).commRingCatIsoToRingEquiv.symm.surjective.comp
        hsurj
    have hspec : Function.Bijective (f.residueFieldMap x).hom := by
      refine ⟨RingHom.injective _, ?_⟩
      intro z
      obtain ⟨s, hs⟩ := hγ z
      exact ⟨α s, (DFunLike.congr_fun hnat s).symm.trans hs⟩
    have : Etale (Spec.map (CommRingCat.ofHom (algebraMap S B))) :=
      ‹Etale (Scheme.Spec.map (CommRingCat.ofHom φ).op)›
    exact (IsLocalRing.existsUnique_algHom_of_monic_simple_root_lifting_etale
      (((HenselianLocalRing.TFAE S).out 1 2).mp
        (show HenselianLocalRing S from inferInstance)) q' hq hspec).exists
