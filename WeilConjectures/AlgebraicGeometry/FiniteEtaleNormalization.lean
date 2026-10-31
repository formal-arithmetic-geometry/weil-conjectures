/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import WeilConjectures.AlgebraicGeometry.FunctionField
public import WeilConjectures.Mathlib.AlgebraicGeometry.Normalization
import WeilConjectures.AlgebraicGeometry.NormalEtale
import WeilConjectures.AlgebraicGeometry.NormalizationCoverIn
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.RingTheory.Etale.Field

/-!
# Finite étale covers as normalizations of generic field factors

Source: Stacks Project, Tag 0BQL, `lemma-finite-etale-covering-normal-unramified`, statement
and first two proof paragraphs, together with Tag 0BQM, proposition-normal (blueprint:
lem-dl-a1-finite-etale-normalization-components). A finite étale cover of a normal integral
scheme has finitely many clopen normal integral components, whose function fields are finite
separable over the base function field; the cover is the coproduct of the corresponding
normalizations. The empty cover is represented by `n = 0`.
-/

@[expose] public section

universe u

open CategoryTheory Limits AlgebraicGeometry

namespace AlgebraicGeometry

-- Flatness places every component generic point in the finite generic fibre.
private theorem finite_components_of_flat
    {X Z : Scheme.{u}} [IsIntegral X] (p : Z ⟶ X) [Flat p]
    [LocallyQuasiFinite p] [QuasiCompact p] : (irreducibleComponents Z).Finite := by
  classical
  have hη (C : irreducibleComponents Z) :
      p (genericPoints.ofComponent C).1 = genericPoint X := by
    let g := (genericPoints.ofComponent C).1
    have hg : IsGenericPoint g C.1 := genericPoints.isGenericPoint_ofComponent C
    obtain ⟨z, hzg, hz⟩ := Flat.generalizingMap p
      ((genericPoint_spec X).specializes (Set.mem_univ (p g)))
    have hsub : C.1 ⊆ closure ({z} : Set Z) := by
      rw [← hg.def]
      exact specializes_iff_closure_subset.mp hzg
    have heq : closure ({z} : Set Z) = C.1 :=
      (C.2.2 isIrreducible_singleton.closure hsub).antisymm hsub
    have hgz : g = z := hg.eq (show IsGenericPoint z C.1 from heq)
    exact (congrArg p hgz).trans hz
  let k : irreducibleComponents Z → (p ⁻¹' {genericPoint X}) :=
    fun C ↦ ⟨(genericPoints.ofComponent C).1, hη C⟩
  have hk : Function.Injective k := by
    intro C D h
    apply Subtype.ext
    exact (genericPoints.isGenericPoint_ofComponent C).symm.trans
      ((congrArg (fun z ↦ closure ({z} : Set Z)) (congrArg Subtype.val h)).trans
        (genericPoints.isGenericPoint_ofComponent D))
  have : Finite (p ⁻¹' {genericPoint X}) := (p.finite_preimage_singleton _).to_subtype
  exact Set.finite_coe_iff.mp (Finite.of_injective k hk)

-- The spectrum of a domain stalk contains the generic points of all components through its point.
private theorem normal_components_disjoint {Z : Scheme.{u}}
    (hZ : ∀ z : Z, IsDomain (Z.presheaf.stalk z)) :
    (irreducibleComponents Z).Pairwise Disjoint := by
  intro C hC D hD hne
  apply Set.disjoint_left.mpr
  intro x hxC hxD
  let := hZ x
  have hr : IsIrreducible (Set.range (Z.fromSpecStalk x)) := by
    simpa only [Set.image_univ] using
      (IrreducibleSpace.isIrreducible_univ (Spec (Z.presheaf.stalk x))).image
        (Z.fromSpecStalk x) (Z.fromSpecStalk x).continuous.continuousOn
  obtain ⟨E, hE, hrE⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible _ hr
  have hle (C : Set Z) (hC : C ∈ irreducibleComponents Z) (hxC : x ∈ C) : C ⊆ E := by
    have hg := hC.1.isGenericPoint_genericPoint (isClosed_of_mem_irreducibleComponents C hC)
    have hgE : hC.1.genericPoint ∈ E := hrE (by
      rw [Scheme.range_fromSpecStalk]
      exact hg.specializes hxC)
    rw [← hg.def]
    exact closure_minimal (Set.singleton_subset_iff.mpr hgE)
      (isClosed_of_mem_irreducibleComponents E hE)
  exact hne ((Set.Subset.antisymm (hle C hC hxC) (hC.2 hE.1 (hle C hC hxC))).trans
    (Set.Subset.antisymm (hle D hD hxD) (hD.2 hE.1 (hle D hD hxD))).symm)

-- Finitely many disjoint closed components are clopen, and their stalks retain normality.
private theorem finiteEtale_components {X Z : Scheme.{u}} [IsIntegral X]
    (hX : ∀ x : X, IsDomain (X.presheaf.stalk x) ∧
      IsIntegrallyClosed (X.presheaf.stalk x)) (p : Z ⟶ X) [IsFinite p] [Etale p] :
    ∃ (n : ℕ) (U : Fin n → Z.Opens),
      (∀ i, IsClosed (U i : Set Z)) ∧
      (∀ i, ConnectedSpace (U i).toScheme) ∧
      (∀ i j, i ≠ j → Disjoint (U i) (U j)) ∧
      (⨆ i, U i) = ⊤ ∧
      ∃ (_hInt : ∀ i, IsIntegral (U i).toScheme),
        ∀ i, ∀ z : (U i).toScheme,
          IsDomain ((U i).toScheme.presheaf.stalk z) ∧
            IsIntegrallyClosed ((U i).toScheme.presheaf.stalk z) := by
  classical
  have hn := Scheme.isDomain_and_isIntegrallyClosed_stalk_of_etale_of_isDomain p hX
  have hf := finite_components_of_flat p
  have hd := normal_components_disjoint (fun z ↦ (hn z).1)
  have ho (C : Set Z) (hC : C ∈ irreducibleComponents Z) : IsOpen C := by
    have heq : C = (⋃₀ (irreducibleComponents Z \ {C}))ᶜ := by
      ext x
      constructor
      · intro hx hother
        obtain ⟨D, hD, hxD⟩ := hother
        exact Set.disjoint_left.mp (hd hC hD.1
          (fun h ↦ hD.2 (Set.mem_singleton_iff.mpr h.symm))) hx hxD
      · intro hx
        by_contra hxC
        apply hx
        refine ⟨irreducibleComponent x, ⟨irreducibleComponent_mem_irreducibleComponents x,
          ?_⟩, mem_irreducibleComponent⟩
        intro heq
        exact hxC ((Set.mem_singleton_iff.mp heq) ▸ mem_irreducibleComponent)
    rw [heq, Set.sUnion_eq_biUnion]
    exact ((hf.sdiff (t := {C})).isClosed_biUnion
      fun D hD ↦ isClosed_of_mem_irreducibleComponents D hD.1).isOpen_compl
  let : Fintype (irreducibleComponents Z) := hf.fintype
  let e := (Fintype.equivFin (irreducibleComponents Z)).symm
  let U : Fin (Fintype.card (irreducibleComponents Z)) → Z.Opens :=
    fun i ↦ ⟨(e i).1, ho (e i).1 (e i).2⟩
  have hInt (i) : IsIntegral (U i).toScheme := by
    let : IrreducibleSpace (U i).toScheme := Subtype.irreducibleSpace (e i).2.1
    let (z : Z) : IsDomain (Z.presheaf.stalk z) := (hn z).1
    let : IsReduced Z := isReduced_of_isReduced_stalk Z
    exact isIntegral_of_irreducibleSpace_of_isReduced _
  refine ⟨_, U, fun i ↦ isClosed_of_mem_irreducibleComponents _ (e i).2,
    fun i ↦ by have := hInt i; infer_instance, ?_, ?_, hInt, ?_⟩
  · intro i j hij
    apply TopologicalSpace.Opens.coe_disjoint.mp
    exact hd (e i).2 (e j).2 (fun h ↦ hij (e.injective (Subtype.ext h)))
  · apply top_le_iff.mp
    intro z _
    obtain ⟨i, hi⟩ := e.surjective
      ⟨irreducibleComponent z, irreducibleComponent_mem_irreducibleComponents z⟩
    apply TopologicalSpace.Opens.mem_iSup.mpr
    refine ⟨i, ?_⟩
    change z ∈ (e i).1
    rw [hi]
    exact mem_irreducibleComponent
  · intro i z
    obtain ⟨hd, hi⟩ := hn ((U i).ι z)
    let := hd
    let := hi
    let e := (asIso ((U i).ι.stalkMap z)).commRingCatIsoToRingEquiv
    exact ⟨e.symm.toMulEquiv.isDomain, IsIntegrallyClosed.of_equiv e⟩

-- Lift the base generic point and use the maximality of the source generic point.
private theorem generic_image {X Z : Scheme.{u}} [IsIntegral X] [IsIntegral Z]
    (p : Z ⟶ X) [Flat p] : p (genericPoint Z) = genericPoint X := by
  obtain ⟨z, hz, hpz⟩ := Flat.generalizingMap p
    (genericPoint_specializes (p (genericPoint Z)))
  obtain rfl : z = genericPoint Z := (hz.antisymm (genericPoint_specializes z)).eq
  exact hpz

-- The generic fibre is a reduced one-point scheme; its generic-point preimmersion is an
-- isomorphism.
private theorem integral_generic_pullback {X Z : Scheme.{u}}
    [IsIntegral X] [IsIntegral Z] (p : Z ⟶ X) [Etale p]
    (hg : p (genericPoint Z) = genericPoint X) :
    letI := p.functionFieldAlgebra hg
    IsPullback Z.fromSpecFunctionField
      (Spec.map (CommRingCat.ofHom (algebraMap X.functionField Z.functionField)))
      p X.fromSpecFunctionField := by
  let := p.functionFieldAlgebra hg
  let a := Spec.map (CommRingCat.ofHom (algebraMap X.functionField Z.functionField))
  have hw : Z.fromSpecFunctionField ≫ p = a ≫ X.fromSpecFunctionField :=
    (p.fromSpecOfAlgebraFunctionField_eq hg).symm
  let T := pullback p X.fromSpecFunctionField
  let d : Spec Z.functionField ⟶ T := pullback.lift Z.fromSpecFunctionField a hw
  have hpre : p ⁻¹' {genericPoint X} = {genericPoint Z} := by
    ext z
    constructor
    · intro hz
      have := (p.isDiscrete_preimage_singleton (genericPoint X)).to_subtype
      have hs : (⟨genericPoint Z, hg⟩ : p ⁻¹' {genericPoint X}) ⤳ ⟨z, hz⟩ :=
        Topology.IsInducing.subtypeVal.specializes_iff.1 (genericPoint_specializes z)
      exact congrArg Subtype.val hs.eq.symm
    · rintro rfl
      exact hg
  have hr : Set.range (pullback.fst p X.fromSpecFunctionField) = {genericPoint Z} := by
    rw [Scheme.Pullback.range_fst, Scheme.range_fromSpecStalk, ← hpre]
    congr 1
    ext x
    exact ⟨fun h ↦ (h.antisymm (genericPoint_specializes x)).eq,
      fun h ↦ by rw [Set.mem_singleton_iff.mp h]; exact specializes_rfl⟩
  have : Subsingleton T := ⟨fun x y ↦
    (pullback.fst p X.fromSpecFunctionField).isEmbedding.injective <| by
      have hx := Set.mem_range_self (f := pullback.fst p X.fromSpecFunctionField) x
      have hy := Set.mem_range_self (f := pullback.fst p X.fromSpecFunctionField) y
      rw [hr] at hx hy
      exact hx.trans hy.symm⟩
  have : IsReduced T := isReduced_of_etale (pullback.snd p X.fromSpecFunctionField)
  have : IsPreimmersion (d ≫ pullback.fst p X.fromSpecFunctionField) := by
    dsimp only [d]
    rw [pullback.lift_fst]
    infer_instance
  have : IsPreimmersion d := IsPreimmersion.of_comp d (pullback.fst p X.fromSpecFunctionField)
  have : IsClosedImmersion d := IsClosedImmersion.iff_isPreimmersion.mpr
    ⟨inferInstance, isClosed_discrete _⟩
  have : Surjective d := ⟨fun t ↦ ⟨IsLocalRing.closedPoint Z.functionField,
    Subsingleton.elim _ _⟩⟩
  have : IsIso d := isIso_of_isClosedImmersion_of_surjective d
  exact IsPullback.of_iso_pullback ⟨hw⟩ (asIso d) (by simp [d]) (by simp [d, a])

-- Use the proved comparison and keep both its structural and its generic-point equations.
private theorem integral_normalization {X Z : Scheme.{u}}
    [IsIntegral X] [IsIntegral Z] (p : Z ⟶ X) [IsFinite p]
    (hg : p (genericPoint Z) = genericPoint X)
    (hn : ∀ z : Z, IsIntegrallyClosed (Z.presheaf.stalk z)) :
    letI := p.functionFieldAlgebra hg
    ∃ e : Z ≅ X.normalizationIn Z.functionField,
      e.hom ≫ X.fromNormalizationIn Z.functionField = p ∧
      Z.fromSpecFunctionField ≫ e.hom =
        (X.fromSpecOfAlgebraFunctionField Z.functionField).toNormalization := by
  let := p.functionFieldAlgebra hg
  have := p.isIso_normalizationInToNormalization hg hn
  let e := asIso p.toNormalization ≪≫ (asIso (p.normalizationInToNormalization hg)).symm
  refine ⟨e, ?_, ?_⟩
  · have hi : inv (p.normalizationInToNormalization hg) ≫
        X.fromNormalizationIn Z.functionField = p.fromNormalization := by
      rw [IsIso.inv_comp_eq]
      exact (p.normalizationInToNormalization_fromNormalization hg).symm
    dsimp only [e, Iso.trans_hom, Iso.symm_hom, asIso_hom, asIso_inv]
    rw [Category.assoc, hi, Scheme.Hom.toNormalization_fromNormalization]
  · apply (cancel_mono (p.normalizationInToNormalization hg)).mp
    simp [e]

-- Relative normalization transports along an isomorphism of its source over the base.
private theorem normalization_iso_over {A B X : Scheme.{u}}
    (f : A ⟶ X) (g : B ⟶ X) [QuasiCompact f] [QuasiSeparated f]
    [QuasiCompact g] [QuasiSeparated g] (e : A ≅ B) (he : e.hom ≫ g = f) :
    ∃ E : f.normalization ≅ g.normalization,
      E.hom ≫ g.fromNormalization = f.fromNormalization ∧
      f.toNormalization ≫ E.hom = e.hom ≫ g.toNormalization := by
  have hi : e.inv ≫ f = g := by rw [← he]; simp
  let a := f.normalizationDesc (e.hom ≫ g.toNormalization) g.fromNormalization
    (by simp [he])
  let b := g.normalizationDesc (e.inv ≫ f.toNormalization) f.fromNormalization
    (by simp [hi])
  have hab : a ≫ b = 𝟙 _ := by
    apply Scheme.Hom.normalization.hom_ext _ _ _ f.fromNormalization
    · simp [a, b]
    · simp [a, b]
    · simp
  have hba : b ≫ a = 𝟙 _ := by
    apply Scheme.Hom.normalization.hom_ext _ _ _ g.fromNormalization
    · simp [a, b]
    · simp [a, b]
    · simp
  exact ⟨⟨a, b, hab, hba⟩, by simp [a], by simp [a]⟩

-- A field generic fibre has dense irreducible image, and its specified identification transports.
private theorem field_fibre_normalization {X Z : Scheme.{u}} [IsIntegral X]
    (hX : ∀ x : X, IsDomain (X.presheaf.stalk x) ∧
      IsIntegrallyClosed (X.presheaf.stalk x)) (p : Z ⟶ X) [IsFinite p] [Etale p]
    (L : Type u) [Field L] [Algebra X.functionField L]
    (eL : pullback p X.fromSpecFunctionField ≅ Spec (.of L))
    (heL : eL.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap X.functionField L)) =
      pullback.snd p X.fromSpecFunctionField) :
    ∃ (_ : ConnectedSpace Z), ∃ eZ : Z ≅ X.normalizationIn L,
      eZ.hom ≫ X.fromNormalizationIn L = p ∧
      eL.inv ≫ pullback.fst p X.fromSpecFunctionField ≫ eZ.hom =
        (X.fromSpecOfAlgebraFunctionField L).toNormalization := by
  let T := pullback p X.fromSpecFunctionField
  let k : T ⟶ Z := pullback.fst p X.fromSpecFunctionField
  have : IrreducibleSpace T := eL.inv.surjective.irreducibleSpace eL.inv.continuous
  have : IsSchemeTheoreticallyDominant X.fromSpecFunctionField :=
    .of_isDominant X.fromSpecFunctionField
  have : IsSchemeTheoreticallyDominant k := by
    dsimp only [k]
    rw [← pullbackSymmetry_hom_comp_snd]
    infer_instance
  have : IrreducibleSpace Z := (irreducibleSpace_def Z).mpr <| by
    change IsIrreducible (Set.univ : Set Z)
    have h := ((IrreducibleSpace.isIrreducible_univ T).image k
      k.continuous.continuousOn).closure
    simpa only [Set.image_univ, k.denseRange.closure_range] using h
  have hn := Scheme.isDomain_and_isIntegrallyClosed_stalk_of_etale_of_isDomain p hX
  let (z : Z) : IsDomain (Z.presheaf.stalk z) := (hn z).1
  have : IsReduced Z := isReduced_of_isReduced_stalk Z
  have : IsIntegral Z := isIntegral_of_irreducibleSpace_of_isReduced Z
  have hg := generic_image p
  let aZ := p.functionFieldAlgebra hg
  let : Algebra X.functionField Z.functionField := aZ
  let H := integral_generic_pullback p hg
  let e : Spec Z.functionField ≅ Spec (.of L) := H.isoPullback ≪≫ eL
  have he : e.hom ≫ X.fromSpecOfAlgebraFunctionField L =
      X.fromSpecOfAlgebraFunctionField Z.functionField := by
    dsimp only [e, Iso.trans_hom, Scheme.fromSpecOfAlgebraFunctionField]
    rw [Category.assoc, ← Category.assoc eL.hom, heL,
      H.isoPullback_hom_snd_assoc]
  obtain ⟨E, hE, hEg⟩ := normalization_iso_over
    (X.fromSpecOfAlgebraFunctionField Z.functionField)
    (X.fromSpecOfAlgebraFunctionField L) e he
  obtain ⟨e₀, he₀, hg₀⟩ := integral_normalization p hg (fun z ↦ (hn z).2)
  refine ⟨inferInstance, e₀ ≪≫ E, ?_, ?_⟩
  · simp only [Iso.trans_hom, Category.assoc, hE, he₀]
  · apply (cancel_epi e.hom).mp
    have hek : e.hom ≫ eL.inv ≫ k = Z.fromSpecFunctionField := by
      simp [e, k, H.isoPullback_hom_fst]
    change e.hom ≫ eL.inv ≫ k ≫ (e₀ ≪≫ E).hom = _
    rw [← Category.assoc e.hom, ← Category.assoc (e.hom ≫ eL.inv),
      Category.assoc e.hom eL.inv k, hek]
    simp only [Iso.trans_hom, ← Category.assoc, hg₀, hEg]

-- Keep the original names of the existential witnesses in the public statement.
set_option linter.unusedVariables false in
/-- Finite étale covers of normal integral schemes split into clopen normal integral components,
which are the normalizations in their generic fields. Source: Stacks Project, Tag 0BQL,
`lemma-finite-etale-covering-normal-unramified`, and Tag 0BQM, `proposition-normal` (blueprint:
lem-dl-a1-finite-etale-normalization-components).

The proof steps are: étale ascent gives normal local domains; flatness puts generic points over
the generic point of `X`, and finiteness gives finitely many irreducible components. The normal
components are clopen and integral, and connectedness identifies them with the connected
components. On each affine component, the finite étale generic fibre is a single finite
separable field factor and the affine integral closure is exactly the component ring, giving the
normalization isomorphism. Base change of the clopen coproduct gives the generic-fibre
coproduct. If that fibre is the spectrum of a field, connectedness leaves one component and
transports its normalization along the specified field identification.

The specified generic-field identifications are part of the conclusion: the `i`-th summand
`Spec E_i` of the generic fibre maps to `Z` through the generic point of `Z_i` (this pins the
`F`-algebra structure on `E_i` to the one induced by `p`), each `eᵢ` sends the generic point
`Spec E_i ⟶ Z_i` to the canonical map `Spec E_i ⟶ X^{E_i}` (it induces the identity of `E_i`),
and in the field case `eZ` sends `Spec L ≅ Z ×_X Spec F ⟶ Z` to the canonical map
`Spec L ⟶ X^L`. -/
theorem finiteEtale_normalization_components
    {X Z : Scheme.{u}} [IsIntegral X]
    (hX : ∀ x : X, IsDomain (X.presheaf.stalk x) ∧
      IsIntegrallyClosed (X.presheaf.stalk x))
    (p : Z ⟶ X) [IsFinite p] [Etale p] :
    ∃ (n : ℕ) (U : Fin n → Z.Opens)
      (hclosed : ∀ i, IsClosed (U i : Set Z))
      (hconn : ∀ i, ConnectedSpace (U i).toScheme)
      (hdisj : ∀ i j, i ≠ j → Disjoint (U i) (U j))
      (hcover : (⨆ i, U i) = ⊤)
      (hInt : ∀ i, IsIntegral (U i).toScheme),
      letI : ∀ i, IsIntegral (U i).toScheme := hInt
      (∀ i, ∀ z : (U i).toScheme,
        IsDomain ((U i).toScheme.presheaf.stalk z) ∧
          IsIntegrallyClosed ((U i).toScheme.presheaf.stalk z)) ∧
      ∃ (hAlg : ∀ i, Algebra (↑X.functionField)
          (↑(U i).toScheme.functionField)),
        letI : ∀ i, Algebra (↑X.functionField)
            (↑(U i).toScheme.functionField) := hAlg
        (∀ i, Module.Finite (↑X.functionField)
            (↑(U i).toScheme.functionField) ∧
          Algebra.IsSeparable (↑X.functionField)
            (↑(U i).toScheme.functionField)) ∧
        (∀ i, ∃ eᵢ : (U i).toScheme ≅
            @Scheme.normalizationIn X ‹IsIntegral X›
              (↑(U i).toScheme.functionField) inferInstance (hAlg i),
          eᵢ.hom ≫ @Scheme.fromNormalizationIn X ‹IsIntegral X›
              (↑(U i).toScheme.functionField) inferInstance (hAlg i) =
            (U i).ι ≫ p ∧
          (U i).toScheme.fromSpecFunctionField ≫ eᵢ.hom =
            (@Scheme.fromSpecOfAlgebraFunctionField X ‹IsIntegral X›
              (↑(U i).toScheme.functionField) inferInstance (hAlg i)).toNormalization) ∧
        let E : Fin n → Scheme := fun i ↦ Spec (.of (↑(U i).toScheme.functionField))
        ∃ (e : pullback p X.fromSpecFunctionField ≅ (∐ fun i : Fin n => E i)),
          let q : (∐ fun i : Fin n => E i) ⟶ Spec (.of (↑X.functionField)) :=
            Sigma.desc (fun (i : Fin n) ↦ Spec.map (CommRingCat.ofHom (algebraMap
              (↑X.functionField) (↑(U i).toScheme.functionField))))
          e.hom ≫ q = pullback.snd p X.fromSpecFunctionField ∧
          (∀ i, Sigma.ι E i ≫ e.inv ≫ pullback.fst p X.fromSpecFunctionField =
            (U i).toScheme.fromSpecFunctionField ≫ (U i).ι) ∧
          ∀ (L : Type u) [hL : Field L] [aL : Algebra (↑X.functionField) L]
            (eL : pullback p X.fromSpecFunctionField ≅ Spec (.of L)),
            eL.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap
              (↑X.functionField) L)) = pullback.snd p X.fromSpecFunctionField →
            ∃ (_ : ConnectedSpace Z),
              ∃ eZ : Z ≅ @Scheme.normalizationIn X ‹IsIntegral X› L hL aL,
                eZ.hom ≫ @Scheme.fromNormalizationIn X ‹IsIntegral X› L hL aL = p ∧
                  eL.inv ≫ pullback.fst p X.fromSpecFunctionField ≫ eZ.hom =
                    (@Scheme.fromSpecOfAlgebraFunctionField X ‹IsIntegral X› L hL aL
                      ).toNormalization := by
  classical
  obtain ⟨n, U, hc, hconn, hd, hcov, hInt, hn⟩ := finiteEtale_components hX p
  refine ⟨n, U, hc, hconn, hd, hcov, hInt, hn, ?_⟩
  let : ∀ i, IsIntegral (U i).toScheme := hInt
  have hfinite (i : Fin n) : IsFinite ((U i).ι ≫ p) := by
    have : IsClosedImmersion (U i).ι := IsClosedImmersion.of_isPreimmersion _
      (by simpa only [Scheme.Opens.range_ι] using hc i)
    infer_instance
  let (i : Fin n) : IsFinite ((U i).ι ≫ p) := hfinite i
  have hg (i : Fin n) := generic_image ((U i).ι ≫ p)
  let hAlg (i : Fin n) := ((U i).ι ≫ p).functionFieldAlgebra (hg i)
  refine ⟨hAlg, ?_⟩
  let : ∀ i, Algebra X.functionField (U i).toScheme.functionField := hAlg
  let E : Fin n → Scheme.{u} := fun i ↦ Spec (U i).toScheme.functionField
  let a (i : Fin n) : E i ⟶ Spec X.functionField :=
    Spec.map (CommRingCat.ofHom (algebraMap X.functionField (U i).toScheme.functionField))
  have H (i : Fin n) : IsPullback (U i).toScheme.fromSpecFunctionField (a i)
      ((U i).ι ≫ p) X.fromSpecFunctionField :=
    integral_generic_pullback ((U i).ι ≫ p) (hg i)
  refine ⟨?_, ?_, ?_⟩
  · intro i
    have : IsFinite (a i) := MorphismProperty.of_isPullback (H i) inferInstance
    have : Etale (a i) := MorphismProperty.of_isPullback (H i) inferInstance
    have : Module.Finite X.functionField (U i).toScheme.functionField :=
      (IsFinite.SpecMap_iff _).mp ‹IsFinite (a i)›
    have : Algebra.Etale X.functionField (U i).toScheme.functionField :=
      (RingHom.etale_algebraMap).mp
        ((HasRingHomProperty.Spec_iff (P := @Etale)).mp ‹Etale (a i)›)
    exact ⟨inferInstance, Algebra.FormallyUnramified.isSeparable _ _⟩
  · intro i
    exact integral_normalization ((U i).ι ≫ p) (hg i) (fun z ↦ (hn i z).2)
  · let T := pullback p X.fromSpecFunctionField
    let d (i : Fin n) : E i ⟶ T :=
      pullback.lift ((U i).toScheme.fromSpecFunctionField ≫ (U i).ι) (a i)
        (by simpa only [Category.assoc] using (H i).w)
    let c : Cofan (fun i : Fin n ↦ (U i).toScheme) := Cofan.mk Z (fun i ↦ (U i).ι)
    have hcol : IsColimit c := (nonempty_isColimit_cofanMk_of (fun i ↦ (U i).ι)
      (by simpa only [Scheme.Opens.opensRange_ι] using hcov)
      (by
        intro i j hij
        simpa only [Scheme.Opens.opensRange_ι, Function.onFun_apply] using hd i j hij)).some
    let c' : Cofan E := Cofan.mk T d
    obtain ⟨hcol'⟩ :=
      (FinitaryPreExtensive.isUniversal_finiteCoproducts hcol).nonempty_isColimit_of_isPullback_left
        (fun i ↦ (U i).ι ≫ p) p X.fromSpecFunctionField
        a (fun i ↦ (U i).toScheme.fromSpecFunctionField) (fun i ↦ (H i).flip)
        (IsPullback.of_hasPullback p X.fromSpecFunctionField).flip c' (Iso.refl T)
        (fun _ ↦ rfl) (fun i ↦ by simp [c', d]) (fun i ↦ by simp [c, c', d])
    let e : T ≅ ∐ E := hcol'.coconePointUniqueUpToIso (coproductIsCoproduct E)
    have hi (i : Fin n) : Sigma.ι E i ≫ e.inv = d i :=
      hcol'.comp_coconePointUniqueUpToIso_inv (coproductIsCoproduct E) ⟨i⟩
    refine ⟨e, ?_, ?_, ?_⟩
    · apply (cancel_epi e.inv).mp
      simp only [Iso.inv_hom_id_assoc]
      apply Sigma.hom_ext
      intro i
      rw [Sigma.ι_desc]
      change a i = Sigma.ι E i ≫ e.inv ≫ pullback.snd p X.fromSpecFunctionField
      rw [← Category.assoc, hi]
      simp [d]
    · intro i
      change Sigma.ι E i ≫ e.inv ≫ pullback.fst p X.fromSpecFunctionField = _
      rw [← Category.assoc, hi]
      simp [d]
    · exact field_fibre_normalization hX p

end AlgebraicGeometry
