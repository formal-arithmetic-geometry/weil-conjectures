/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective
public import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme
public import WeilConjectures.Mathlib.AlgebraicGeometry.Normalization
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.Topology.KrullDimension
import WeilConjectures.Mathlib.AlgebraicGeometry.AffineScheme
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Finite
import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Basic
import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.AlgebraicGeometry.FiniteOverProjective

/-!
# Normalizations of the components of a projective scheme

Source: Stacks Project, Varieties, Tags 0BXR and 0GK4; Properties, Tag 033M;
Algebra, Tags 00OK and 00OY
(blueprint: lem-weil-pbc-normalization-projective-components).

The family `Z` presents the reduced irreducible components: integral closed subschemes
whose images enumerate the irreducible components bijectively. The cocone `ι` presents
`N` as the coproduct of their existing integral-scheme normalizations. Thus this statement
applies to any choice of the coproduct, including the empty one.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Componentwise normalization of a projective scheme over a field is finite and surjective,
projective and proper, with finitely many nonempty normal integral clopen summands.
Source: Stacks Project, Varieties, Tags 0BXR and 0GK4; Properties, Tag 033M;
dimension via Algebra, Tags 00OK and 00OY.
(blueprint: lem-weil-pbc-normalization-projective-components)

The structure data `Z`, `a`, `hcomponents`, and `hindex` mean precisely the reduced
irreducible components, not an extra restriction on `C`: an integral closed subscheme
is reduced, and the reduced induced structure on each closed subset is unique.
The data `N`, `ι`, `hN`, `ν`, and `hν` express the componentwise normalization in the node.
The final factorization uses the same component normalizations over the reduction.

Proof:
1. Projective implies proper (lem-pc-projective-proper), hence finite type and
   quasi-compact. Over the Noetherian field, C is Noetherian (pqf-lem-locnoeth-lft,
   pqf-def-locnoeth, def-weil-pbc-quasi-compact-scheme). Its components are finite
   (lem-sc-noetherian-closed-subset-finite-components).
2. Each reduced component is integral, and its closed immersion into C is finite
   (lem-weil-pbc-reduced-induced-closed-subscheme, def-pc-integral-scheme,
   lem-weil-pbc-closed-immersion-finite). Apply lem-fin-finite-over-projective over
   the affine Noetherian base Spec k; it is projective, proper and finite type.
3. Its normalization is finite, surjective and of the same dimension
   (lem-sc-normalization-exists). Composing with its inclusion into C is finite
   (lem-weil-pbc-finite-composition).
4. Affine normalization charts are integral closures in the function field
   (def-fin-normalization-extension, lem-sc-integral-function-field-affine-fraction,
   lem-sc-scheme-sober). They are normal domains
   (lem-weil-pbc-integral-closure-finite-extension-normal). Their stalks are normal
   domains by lem-weil-pbc-spec-domain-stalks-function-field and
   lem-weil-pbc-localization-normal-domain. Their common generic point gives integrality.
5. The coprojections are clopen, disjoint and cover N
   (lem-weil-pbc-scheme-coproduct-family). The induced map is finite by finite
   coproducts (lem-weil-pbc-finite-coproduct), including the empty spectrum of the zero
   ring (def-weil-finite-integral-morphism). Componentwise surjectivity gives surjectivity.
6. Apply lem-fin-finite-over-projective over the affine Noetherian base Spec k to N
   and each summand, and then lem-pc-projective-proper.
7. The component maps factor through the reduction
   (lem-weil-pbc-reduced-source-factors-through-closed-subscheme). The reduced induced
   components of C and its reduction agree; taking the same normalized coproduct gives
   the normalization of the reduction and its factorization (def-weil-pbc-scheme-reduction,
   lem-weil-pbc-reduced-induced-closed-subscheme, lem-weil-pbc-scheme-coproduct-family).
8. A closed component has dimension at most that of C
   (def-kun-topological-krull-dimension). Normalization preserves its dimension
   (lem-sc-normalization-exists), giving the bound by one.
9. Components cover C and are nonempty (def-weil-irreducible-components), so the
   indexing set is empty exactly when C is empty; then the summand assertions are vacuous.
-/
theorem normalization_projective_components
    {k : Type u} [Field k] {C : Scheme.{u}}
    (p : C ⟶ Spec (.of k)) [IsHProjective p]
    {I : Type u} (Z : I → Scheme.{u}) [∀ i : I, IsIntegral (Z i)]
    (a : ∀ i : I, Z i ⟶ C) [∀ i : I, IsClosedImmersion (a i)]
    (hcomponents : ∀ i : I, Set.range (a i) ∈ irreducibleComponents C)
    (hindex : Function.Bijective
      (fun i : I ↦ (⟨Set.range (a i), hcomponents i⟩ : irreducibleComponents C)))
    (N : Scheme.{u}) (ι : ∀ i : I, (Z i).normalization ⟶ N)
    (hN : IsColimit (Cofan.mk N ι)) (ν : N ⟶ C)
    (hν : ∀ i : I, ι i ≫ ν = (Z i).fromNormalization ≫ a i) :
    Finite I ∧ IsFinite ν ∧ Surjective ν ∧
      IsHProjective (ν ≫ p) ∧ IsProper (ν ≫ p) ∧
      (∀ i : I, Nonempty (Z i).normalization ∧
        (∀ x : (Z i).normalization,
          IsDomain ((Z i).normalization.presheaf.stalk x) ∧
            IsIntegrallyClosed ((Z i).normalization.presheaf.stalk x)) ∧
        IsIntegral (Z i).normalization ∧ IsOpenImmersion (ι i) ∧
        IsClosed (Set.range (ι i)) ∧
        IsHProjective ((Z i).fromNormalization ≫ a i ≫ p) ∧
        IsProper ((Z i).fromNormalization ≫ a i ≫ p)) ∧
      (topologicalKrullDim C ≤ 1 →
        ∀ i : I, topologicalKrullDim (Z i).normalization ≤ 1) ∧
      (∃ (b : ∀ i : I, Z i ⟶ C.nilradical.subscheme)
          (νred : N ⟶ C.nilradical.subscheme),
        (∀ i : I, b i ≫ C.nilradical.subschemeι = a i) ∧
          νred ≫ C.nilradical.subschemeι = ν ∧
          ∀ i : I, ι i ≫ νred = (Z i).fromNormalization ≫ b i) ∧
      (IsEmpty I ↔ IsEmpty C) := by
  classical
  let : IsProjective p := IsHProjective.isProjective p
  let : IsLocallyNoetherian C := LocallyOfFiniteType.isLocallyNoetherian p
  let : CompactSpace C := QuasiCompact.compactSpace_of_compactSpace p
  let : IsNoetherian C := ⟨⟩
  let : Finite (irreducibleComponents C) :=
    (finite_irreducibleComponents_of_isNoetherian (X := C)).to_subtype
  let : Finite I := Finite.of_injective _ hindex.injective
  let (i : I) : LocallyOfFiniteType (a i ≫ p) := inferInstance
  let (i : I) : IsFinite (Z i).fromNormalization :=
    (Z i).isFinite_fromNormalization_of_locallyOfFiniteType (a i ≫ p)
  let (i : I) : IsFinite ((Z i).fromNormalization ≫ a i) := inferInstance
  let e : (∐ fun i : I ↦ (Z i).normalization) ≅ N :=
    (coproductIsCoproduct _).coconePointUniqueUpToIso hN
  have he (i : I) : Sigma.ι (fun i : I ↦ (Z i).normalization) i ≫ e.hom = ι i := by
    exact (coproductIsCoproduct _).comp_coconePointUniqueUpToIso_hom hN ⟨i⟩
  have hmap : ν = e.inv ≫ Sigma.desc (fun i : I ↦ (Z i).fromNormalization ≫ a i) := by
    apply (cancel_epi e.hom).mp
    apply Sigma.hom_ext
    intro i
    simp only [Iso.hom_inv_id_assoc, Sigma.ι_desc]
    rw [← Category.assoc, he, hν]
  let : IsFinite ν := by rw [hmap]; infer_instance
  let : IsProjective (ν ≫ p) :=
    (finite_over_projective_affineLocally p ν).2 inferInstance
  let (i : I) : IsProjective ((Z i).fromNormalization ≫ a i ≫ p) := by
    simpa only [Category.assoc] using
      (finite_over_projective_affineLocally p ((Z i).fromNormalization ≫ a i)).2 inferInstance
  have hcover (x : C) : ∃ i : I, ∃ z : Z i, a i z = x := by
    obtain ⟨i, hi⟩ := hindex.surjective
      ⟨irreducibleComponent x, irreducibleComponent_mem_irreducibleComponents x⟩
    have hi' : Set.range (a i) = irreducibleComponent x := congrArg Subtype.val hi
    have hx : x ∈ Set.range (a i) := by
      rw [hi']
      exact mem_irreducibleComponent
    exact ⟨i, hx⟩
  have hsurj : Surjective ν := by
    constructor
    intro x
    obtain ⟨i, z, rfl⟩ := hcover x
    obtain ⟨w, rfl⟩ := (Z i).fromNormalization.surjective z
    refine ⟨ι i w, ?_⟩
    change (ι i ≫ ν) w = _
    rw [hν]
    rfl
  refine ⟨inferInstance, inferInstance, hsurj, inferInstance, inferInstance, ?_, ?_, ?_, ?_⟩
  · intro i
    refine ⟨inferInstance, ?_, inferInstance, ?_, ?_, inferInstance, inferInstance⟩
    · intro x
      refine ⟨inferInstance, ?_⟩
      exact ((Z i).fromSpecFunctionField).isIntegrallyClosed_stalk_normalization
        (fun x ↦ Scheme.isIntegrallyClosed_stalk_Spec (Z i).functionField x) x
    · have hi : ι i = Sigma.ι (fun i : I ↦ (Z i).normalization) i ≫ e.hom := (he i).symm
      rw [hi]
      infer_instance
    · let en : (Σ i : I, (Z i).normalization) ≃ₜ N :=
        (sigmaMk (fun i : I ↦ (Z i).normalization)).trans
          (TopCat.homeoOfIso (asIso e.hom.base))
      have hh := en.isClosedEmbedding.comp
        (Topology.IsClosedEmbedding.sigmaMk (i := i) (σ := fun i : I ↦ (Z i).normalization))
      have heq : en ∘ Sigma.mk i = ι i := by
        funext x
        change e.hom (sigmaMk (fun i : I ↦ (Z i).normalization) ⟨i, x⟩) = ι i x
        rw [sigmaMk_mk, ← Scheme.Hom.comp_apply, he]
      rw [heq] at hh
      exact hh.isClosed_range
  · intro hdim i
    rw [(Z i).topologicalKrullDim_normalization (a i ≫ p)]
    exact ((a i).isClosedEmbedding.isInducing.topologicalKrullDim_le).trans hdim
  · have hker (i : I) : C.nilradical.subschemeι.ker ≤ (a i).ker := by
      rw [Scheme.IdealSheafData.ker_subschemeι]
      exact (C.nilradical.le_ker_iff_range_subset_support (a i)).2 (by simp)
    let b (i : I) : Z i ⟶ C.nilradical.subscheme :=
      IsClosedImmersion.lift C.nilradical.subschemeι (a i) (hker i)
    have hb (i : I) : b i ≫ C.nilradical.subschemeι = a i :=
      IsClosedImmersion.lift_fac _ _ _
    let νred : N ⟶ C.nilradical.subscheme :=
      hN.desc (Cofan.mk _ fun i : I ↦ (Z i).fromNormalization ≫ b i)
    have hred (i : I) : ι i ≫ νred = (Z i).fromNormalization ≫ b i :=
      hN.fac _ ⟨i⟩
    refine ⟨b, νred, hb, ?_, hred⟩
    apply Cofan.IsColimit.hom_ext hN
    intro i
    dsimp only [Cofan.mk_pt, cofan_mk_inj]
    rw [← Category.assoc, hred, Category.assoc, hb, hν]
  · constructor
    · intro hI
      exact ⟨fun x ↦ by obtain ⟨i, _, _⟩ := hcover x; exact hI.false i⟩
    · intro hC
      exact ⟨fun i ↦ by
        obtain ⟨z⟩ := (inferInstance : Nonempty (Z i))
        exact hC.false (a i z)⟩

end AlgebraicGeometry
