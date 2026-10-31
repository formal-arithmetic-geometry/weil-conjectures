/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.RingTheory.RingHom.FaithfullyFlat

/-!
# A finite affine covering family as one fppf algebra

Source: Stacks Project, Tag 02KL, proof of `lemma-flat-finitely-presented-permanence`,
finite disjoint affine source replacement and affine reduction; Tags 00HQ, 01TQ, 01T2.
(blueprint: lem-a1-finite-affine-family-fppf-algebra)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A finite jointly surjective family of flat finitely presented affine maps packages
as a faithfully flat finitely presented product algebra, compatibly with its base map.

Source: Stacks Project, Tag 02KL, proof of `lemma-flat-finitely-presented-permanence`.
(blueprint: lem-a1-finite-affine-family-fppf-algebra)

Proof: (1) The coproduct universal property defines the two maps by `Sigma.desc`.
Functoriality of Spec and coproduct uniqueness give their composition identity and
compatibility with the coordinate maps. The finite `sigmaSpec` is an isomorphism,
and its restriction to each component is the spectrum of the product projection.
(2) A finite product of flat modules is flat, including the empty product. The affine
flatness criterion and transport across `sigmaSpec` give flatness of the coproduct map.
(3) Joint surjectivity supplies a preimage in a component for each target point, hence
surjectivity of the coproduct map and of the map from the product spectrum. Flatness
and surjectivity on spectra give faithful flatness of the product algebra (Tag 00HQ).
(4) Each component is an affine open in the coproduct. At every point its component
witnesses local finite presentation using the assumed finite presentation of its map.
(5) The whole coproduct is affine by `sigmaSpec`; applying the all-affine-pairs finite
presentation criterion gives finite presentation of the coordinate map (Tag 01TQ).
(6) The same component neighbourhoods and the finite type hypotheses over R show the
map to Spec R is locally of finite type. The all-affine-pairs criterion then gives
finite type of the product over R (Tag 01T2).
(7) For an empty index the product is a singleton ring, hence zero. Joint surjectivity
makes Spec A empty, hence A is zero; equivalently use universal injectivity of the
faithfully flat map A to the zero ring. Zero factors simply give empty components.
-/
theorem finiteAffineFamily_fppfAlgebra
    (R A : CommRingCat.{u}) (α : R →+* A) (I : Type u) [Finite I]
    (B : I → CommRingCat.{u}) (β : ∀ i : I, A →+* B i)
    (hflat : ∀ i : I, (β i).Flat)
    (hfp : ∀ i : I, (β i).FinitePresentation)
    (hft : ∀ i : I, ((β i).comp α).FiniteType)
    (hcover : ∀ y : Spec A, ∃ (i : I) (x : Spec (B i)),
      Spec.map (CommRingCat.ofHom (β i)) x = y) :
    IsIso (sigmaSpec B) ∧
    (∀ i : I, Sigma.ι (fun j : I ↦ Spec (B j)) i ≫ sigmaSpec B =
      Spec.map (CommRingCat.ofHom (Pi.evalRingHom (fun j : I ↦ B j) i))) ∧
    Sigma.desc (fun i : I ↦ Spec.map (CommRingCat.ofHom ((β i).comp α))) =
      Sigma.desc (fun i : I ↦ Spec.map (CommRingCat.ofHom (β i))) ≫
        Spec.map (CommRingCat.ofHom α) ∧
    Sigma.desc (fun i : I ↦ Spec.map (CommRingCat.ofHom (β i))) =
      sigmaSpec B ≫ Spec.map (CommRingCat.ofHom (RingHom.pi β)) ∧
    Sigma.desc (fun i : I ↦ Spec.map (CommRingCat.ofHom ((β i).comp α))) =
      sigmaSpec B ≫
        Spec.map (CommRingCat.ofHom (RingHom.pi (fun i : I ↦ (β i).comp α))) ∧
    RingHom.pi (fun i : I ↦ (β i).comp α) = (RingHom.pi β).comp α ∧
    Flat (Sigma.desc (fun i : I ↦ Spec.map (CommRingCat.ofHom (β i)))) ∧
    Surjective (Sigma.desc (fun i : I ↦ Spec.map (CommRingCat.ofHom (β i)))) ∧
    LocallyOfFinitePresentation
      (Sigma.desc (fun i : I ↦ Spec.map (CommRingCat.ofHom (β i)))) ∧
    LocallyOfFiniteType
      (Sigma.desc (fun i : I ↦ Spec.map (CommRingCat.ofHom ((β i).comp α)))) ∧
    (RingHom.pi β).FaithfullyFlat ∧
    (RingHom.pi β).FinitePresentation ∧
    (RingHom.pi (fun i : I ↦ (β i).comp α)).FiniteType ∧
    (IsEmpty I → Subsingleton A ∧ Subsingleton (∀ i : I, B i)) := by
  classical
  have hdesc (C : CommRingCat.{u}) (δ : ∀ i : I, C →+* B i) :
      Sigma.desc (fun i ↦ Spec.map (CommRingCat.ofHom (δ i))) =
        sigmaSpec B ≫ Spec.map (CommRingCat.ofHom (RingHom.pi δ)) := by
    apply Sigma.hom_ext
    intro i
    rw [Sigma.ι_desc, ← Category.assoc]
    erw [ι_sigmaSpec, ← Spec.map_comp]
    rfl
  have hq := hdesc A β
  have hp := hdesc R (fun i ↦ (β i).comp α)
  have hcomp :
      Sigma.desc (fun i ↦ Spec.map (CommRingCat.ofHom ((β i).comp α))) =
        Sigma.desc (fun i ↦ Spec.map (CommRingCat.ofHom (β i))) ≫
          Spec.map (CommRingCat.ofHom α) := by
    apply Sigma.hom_ext
    intro i
    simp only [Sigma.ι_desc_assoc, Sigma.ι_desc, ← Spec.map_comp]
    rfl
  have hpi : RingHom.pi (fun i ↦ (β i).comp α) = (RingHom.pi β).comp α := rfl
  have : ∀ i, Flat (Spec.map (CommRingCat.ofHom (β i))) :=
    fun i ↦ Flat.SpecMap_iff.mpr (hflat i)
  have hf : Flat (Sigma.desc (fun i ↦ Spec.map (CommRingCat.ofHom (β i)))) :=
    inferInstance
  have hs : Surjective (Sigma.desc (fun i ↦ Spec.map (CommRingCat.ofHom (β i)))) := by
    constructor
    intro y
    obtain ⟨i, x, hx⟩ := hcover y
    refine ⟨Sigma.ι (fun i ↦ Spec (B i)) i x, ?_⟩
    exact (congrArg (fun f : Spec (B i) ⟶ Spec A ↦ f x)
      (Sigma.ι_desc (fun i ↦ Spec.map (CommRingCat.ofHom (β i))) i)).trans hx
  have hlfp : LocallyOfFinitePresentation
      (Sigma.desc (fun i ↦ Spec.map (CommRingCat.ofHom (β i)))) :=
    IsZariskiLocalAtSource.sigmaDesc
      (fun i ↦ (LocallyOfFinitePresentation.SpecMap_iff _).mpr (hfp i))
  have hlft : LocallyOfFiniteType
      (Sigma.desc (fun i ↦ Spec.map (CommRingCat.ofHom ((β i).comp α)))) :=
    IsZariskiLocalAtSource.sigmaDesc
      (fun i ↦ (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mpr (hft i))
  have hfaith : (RingHom.pi β).FaithfullyFlat := by
    apply (flat_and_surjective_SpecMap_iff (CommRingCat.ofHom (RingHom.pi β))).mp
    constructor
    · exact (MorphismProperty.cancel_left_of_respectsIso @Flat (sigmaSpec B) _).mp
        (hq ▸ hf)
    · exact (MorphismProperty.cancel_left_of_respectsIso @Surjective (sigmaSpec B) _).mp
        (hq ▸ hs)
  have hpres : (RingHom.pi β).FinitePresentation := by
    apply (LocallyOfFinitePresentation.SpecMap_iff
      (CommRingCat.ofHom (RingHom.pi β))).mp
    exact (MorphismProperty.cancel_left_of_respectsIso
      @LocallyOfFinitePresentation (sigmaSpec B) _).mp (hq ▸ hlfp)
  have htype : (RingHom.pi (fun i ↦ (β i).comp α)).FiniteType := by
    apply (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)
      (φ := CommRingCat.ofHom (RingHom.pi (fun i ↦ (β i).comp α)))).mp
    exact (MorphismProperty.cancel_left_of_respectsIso
      @LocallyOfFiniteType (sigmaSpec B) _).mp (hp ▸ hlft)
  refine ⟨inferInstance, ι_sigmaSpec B, hcomp, hq, hp, hpi, hf, hs, hlfp, hlft,
    hfaith, hpres, htype, ?_⟩
  intro he
  let : IsEmpty I := he
  have : Subsingleton (∀ i : I, B i) := inferInstance
  exact ⟨Function.Injective.subsingleton hfaith.injective, inferInstance⟩

end AlgebraicGeometry
