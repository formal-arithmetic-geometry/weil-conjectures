/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NQ
-/
module

public import Sheaf.Paper.LocalizingAdmissibleCoefficients
public import Sheaf.Paper.CondensedModuleDerivedPushpull
public import Sheaf.Paper.CondensedQcqsPushforwardContinuity
public import Sheaf.Paper.CondensedConstantConstructibility
public import Sheaf.Paper.QcqsOpenClosedTree
public import Sheaf.AlgebraicGeometry.ModuleDerivedCohomologyPullback
public import WeilConjectures.AlgebraicGeometry.TorsionEtaleSheaf
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExactPullback
public import Mathlib.CategoryTheory.Limits.Shapes.Images
import Sheaf.Paper.ClosedRestrictionDerivedOperations
import Sheaf.Paper.SupportedImageBoundedDerivedGeneration
import WeilConjectures.FromJoel.CategoryTheory.Abelian.GrothendieckAxioms.Colim
import Mathlib.Algebra.Category.Grp.AB

/-! # Image rigidity from all supported finite-model comparisons

Source: blueprint latest, sec-six-functors-basics/sk-prop-sf-comp-coherence,
det-sf-comp-coherence-refinement.proof.md, (2), first paragraph;
agent-formulated conditional image comparison, exact full-generality reference WANTED.
(blueprint: lem-sfb-supported-image-rigidity-from-model-comparisons).

A tree path records a finite support chain, including the root path for the identity
chain. Complementary siblings can be added to any chain in the node, and every such
path gives one of those chains. No condition on the complement of the closed pair
is imposed. The comparison is a natural transformation on all modules on the source,
so applying its naturality to image maps gives naturality for squares of module maps.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj ZeroObject

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- The actual ordinary module-derived restriction on a fixed support chain, natural
in every source module. It is the right-derived descent of the module adjunction unit
followed by restriction from the pullback of the terminal object to the terminal object.
Source: blueprint latest, det-sf-comp-coherence-refinement.proof.md, (2), first paragraph,
the displayed arrow rho in the conditional image-comparison obligation
(blueprint: lem-sfb-supported-image-rigidity-from-model-comparisons). -/
def supportedModelDerivedRestriction
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {T₀ T S : Scheme.{u}} (t : T₀ ⟶ T)
    {tree : QcqsOpenClosedTree T} (p : tree.Path S) :
    p.extension Λ ⋙ DerivedCategory.singleFunctor _ 0 ⋙
        (condensedModuleSections Λ T).rightDerivedFunctor ⟶
      p.extension Λ ⋙ DerivedCategory.singleFunctor _ 0 ⋙
        (upperStar Λ t).mapDerivedCategory ⋙
          (condensedModuleSections Λ T₀).rightDerivedFunctor :=
  Functor.whiskerLeft (p.extension Λ ⋙ DerivedCategory.singleFunctor _ 0)
    (Functor.rightDerivedPullback (upperStar Λ t)
      ((Functor.whiskerRight (upperStarLowerStarAdjunction Λ t).unit
          (condensedModuleSections Λ T) ≫
        Functor.whiskerLeft (upperStar Λ t)
          (Functor.whiskerLeft (Mod.forget (condensedRingObj Λ T₀))
            ((sheafSections (Scheme.ProEt.topology T₀) Ab.{u + 1}).map
              (MorphismProperty.Over.homMk
                (pullback.lift t (𝟙 T₀)
                  ((Category.comp_id t).trans (Category.id_comp t).symm))
                (pullback.lift_snd _ _ _)).op))) :
        condensedModuleSections Λ T ⟶ upperStar Λ t ⋙ condensedModuleSections Λ T₀))

private theorem restriction_iso_of_iso
    {C D : Type*} [Category C] [Category D] {F G : C ⥤ D} (ρ : F ⟶ G)
    {X Y : C} (e : X ≅ Y) [IsIso (ρ.app X)] : IsIso (ρ.app Y) := by
  have h : ρ.app Y = F.map e.inv ≫ ρ.app X ≫ G.map e.hom := by
    rw [← ρ.naturality e.hom, ← Category.assoc, ← F.map_comp, e.inv_hom_id,
      F.map_id, Category.id_comp]
  rw [h]
  infer_instance

private theorem restriction_iso_of_retract
    {C D : Type*} [Category C] [Category D] {F G : C ⥤ D} (ρ : F ⟶ G)
    {X Y : C} (i : X ⟶ Y) (p : Y ⟶ X) (hip : i ≫ p = 𝟙 X)
    [IsIso (ρ.app Y)] : IsIso (ρ.app X) := by
  refine ⟨⟨G.map i ≫ inv (ρ.app Y) ≫ F.map p, ?_, ?_⟩⟩
  · rw [← ρ.naturality_assoc]
    simp [← F.map_comp, hip]
  · simp only [Category.assoc, ρ.naturality]
    simp [← G.map_comp, hip]

private theorem restriction_iso_of_limit
    {C D J : Type*} [Category C] [Category D] [Category J]
    {F G : C ⥤ D} (ρ : F ⟶ G) (K : J ⥤ C) (c : Cone K)
    (hF : IsLimit (F.mapCone c)) (hG : IsLimit (G.mapCone c))
    (hK : ∀ j, IsIso (ρ.app (K.obj j))) : IsIso (ρ.app c.pt) := by
  let η := Functor.whiskerLeft K ρ
  have : ∀ j, IsIso (η.app j) := hK
  have : IsIso η := NatIso.isIso_of_isIso_app η
  have hpost := (IsLimit.postcomposeHomEquiv (asIso η) (F.mapCone c)).symm hF
  have h : hG.lift ((Cone.postcompose η).obj (F.mapCone c)) = ρ.app c.pt := by
    apply hG.hom_ext
    intro j
    calc
      _ = F.map (c.π.app j) ≫ ρ.app (K.obj j) := hG.fac _ j
      _ = _ := ρ.naturality (c.π.app j)
  rw [← h]
  exact (hG.nonempty_isLimit_iff_isIso_lift).mp ⟨hpost⟩

private theorem restriction_iso_of_filtered
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {T₀ T : Scheme.{u}} (t : T₀ ⟶ T)
    (h : ClosedRestrictionFilteredRepresentatives Λ t)
    (J : Type (u + 1)) [SmallCategory J] [IsFiltered J]
    (D : J ⥤ CochainComplex
      (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ T)) ℤ)
    (a : ℤ) (ha : ∀ j, (D.obj j).IsStrictlyGE a)
    (hD : ∀ j, IsIso ((closedRestrictionRho Λ t).app (DerivedCategory.Q.obj (D.obj j)))) :
    IsIso ((closedRestrictionRho Λ t).app (DerivedCategory.Q.obj (colimit D))) := by
  obtain ⟨hmodel, hcomp⟩ := h J D a ha
  obtain ⟨P, R, L, M, eF, eG, εF, εG, α, γ, η, m,
    _, _, _, hα, hγ, hη, hm, hsq⟩ := hmodel
  have hηiso (j : J) : IsIso (DerivedCategory.Q.map (η.app j)) := by
    have := hD j
    have hi : IsIso (eF.hom.app j ≫ DerivedCategory.Q.map (η.app j)) := by
      rw [hη j]
      infer_instance
    exact (isIso_comp_left_iff _ _).mp hi
  have hq : QuasiIso (colimMap η) :=
    (HomologicalComplex.quasiIso Ab.{u + 1} (.up ℤ)).colimMap η (fun j ↦
      (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).mp (hηiso j))
  obtain ⟨hαiso, hγiso⟩ := hcomp P R L M eF eG εF εG α γ hα hγ
  have heq : colimMap η ≫ colimit.desc R (Cocone.mk M γ) =
      colimit.desc P (Cocone.mk L α) ≫ m := by
    apply colimit.hom_ext
    intro j
    simpa using hsq j
  have hmis : IsIso (DerivedCategory.Q.map m) := by
    have hi : IsIso (DerivedCategory.Q.map (colimit.desc P (Cocone.mk L α)) ≫
        DerivedCategory.Q.map m) := by
      rw [← Functor.map_comp, ← heq, Functor.map_comp]
      infer_instance
    exact (isIso_comp_left_iff _ _).mp hi
  have hi : IsIso ((closedRestrictionRho Λ t).app (DerivedCategory.Q.obj (colimit D)) ≫
      εG.hom) := by
    rw [← hm]
    infer_instance
  exact (isIso_comp_right_iff _ _).mp hi

/-- Comparison for all supported finite scalar models implies comparison for the
actual image of any map between two such models. Neither the map nor its image is
assumed constant, constructible, complete, or to have closed image.

Source: blueprint latest, det-sf-comp-coherence-refinement.proof.md, (2), first paragraph;
agent-formulated conditional image comparison, exact full-generality reference WANTED.
(blueprint: lem-sfb-supported-image-rigidity-from-model-comparisons).

Proof plan:
1. Apply lem-sfb-closed-restriction-derived-operations to the closed pair. Its functors
are the actual module-derived global sections before and after exact inverse image;
its transformation is the restriction used here. Let E be the replete class of objects
where this transformation is invertible. The operations lemma supplies a morphism of
distinguished triangles, including the connecting square, without asserting that
inverse image preserves injectives.
2. E contains zero and is closed under integer shifts and triangles, using
lem-sf-triangle-morphism-iso. It is closed under retracts: for i : K -> L and
p : L -> K with i followed by p equal to the identity and restriction invertible on L,
an inverse on K is Phi(p) rho_L^{-1} Psi(i). Naturality verifies both inverse identities.
3. The operations lemma identifies restriction on a derived product with the product
of the restrictions. It also identifies restriction on a strict small filtered diagram
of complexes with common termwise lower bound with the filtered colimit of the
restrictions. Inverses are natural by inverting the naturality squares. Thus E has the
two infinite-operation closure properties in the definition of G_T in
lem-sfb-supported-image-bounded-derived-generation. Both members of the pair are qcqs;
no quasi-compactness of the complement of t is used.
4. hmodels is exactly the supplied property B_Lambda(t): every supported finite scalar
model in every chain belongs to E. Hence G_T is contained in E by its intersection
definition. The generation lemma applied to the actual u gives J(image u)[0] in G_T.
Its restriction is therefore invertible. The torsion comparison remains a hypothesis;
B_Lambda(t) is supplied independently, never deduced by the identity-map case.
5. A commutative square induces its canonical image map by image factorization.
Apply the naturality of supportedModelDerivedRestriction to that image map. This gives
the required naturality square and is compatible with composition of squares. For a
zero map the image is zero; for an identity it is the local model. The root path,
empty schemes and zero coefficient rings are permitted by all the constructions.
-/
theorem supported_image_rigidity_from_model_comparisons
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (ℓ : ℕ) [Fact ℓ.Prime]
    (hΛ :
      (∃ (A : Type) (_ : CommRing A) (_ : TopologicalSpace A)
          (_ : DiscreteTopology A) (_ : IsTopologicalRing A),
        Finite A ∧ (∃ n : ℕ, ∀ a : A, (ℓ ^ n) • a = 0) ∧
          Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj A))) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj ℤ_[ℓ])) ∨
      (∃ E : PadicAlgCl.FiniteIntermediateField ℓ,
        Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicIntegersRingObj ℓ E))) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj ℚ_[ℓ])) ∨
      (∃ E : PadicAlgCl.FiniteIntermediateField ℓ,
        Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj E))))
    {T₀ T S : Scheme.{u}} [CompactSpace T] [QuasiSeparatedSpace T]
    [CompactSpace T₀] [QuasiSeparatedSpace T₀]
    (t : T₀ ⟶ T) [IsClosedImmersion t]
    (ht : ∀ (F : Sheaf T.smallEtaleTopology Ab.{u + 1}),
      Scheme.IsTorsionAbelianSheaf F → ∀ q : ℕ,
        Function.Bijective (Etale.cohomologyMap t F q))
    (hmodels : ∀ (tree' : QcqsOpenClosedTree T) (S' : Scheme.{u})
      (p' : tree'.Path S')
      (N : Mod (Sheaf (Scheme.ProEt.topology S') Ab.{u + 1}) (condensedRingObj Λ S')),
      HasFiniteConstantLocalModel Λ S' N →
        IsIso ((supportedModelDerivedRestriction Λ t p').app N))
    (tree : QcqsOpenClosedTree T) (p : tree.Path S)
    (L M : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1}) (condensedRingObj Λ S))
    (hL : HasFiniteConstantLocalModel Λ S L)
    (hM : HasFiniteConstantLocalModel Λ S M) (u : L ⟶ M) :
    IsIso ((supportedModelDerivedRestriction Λ t p).app (image u)) := by
  have _ht := ht
  let ρ := closedRestrictionRho Λ t
  let E : ObjectProperty (DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ T))) :=
    fun K ↦ IsIso (ρ.app K)
  obtain ⟨hFadd, hGadd, hFtri, hGtri, hshift, _, htriangle, hproducts, hfiltered⟩ :=
    closed_restriction_derived_operations Λ t
  let := hFadd
  let := hGadd
  let := hFtri
  let := hGtri
  let := hshift
  have hEiso : E.IsClosedUnderIsomorphisms :=
    ⟨fun e hK ↦ @restriction_iso_of_iso _ _ _ _ _ _ ρ _ _ e hK⟩
  let := hEiso
  have hEtri : E.IsTriangulated := by
    refine
      { exists_zero := ⟨0, isZero_zero _, ?_⟩
        isStableUnderShiftBy := fun n ↦ ⟨fun K hK ↦ ?_⟩
        ext₂' := ?_ }
    · exact ((closedRestrictionPhi Λ T).map_isZero (isZero_zero _)).isIso
        ((closedRestrictionPsi Λ t).map_isZero (isZero_zero _)) _
    · change IsIso (ρ.app (K⟦n⟧))
      have : IsIso (ρ.app K) := hK
      rw [NatTrans.app_shift ρ n K]
      infer_instance
    · intro Δ hΔ h₁ h₃
      obtain ⟨r, hr₁, hr₂, hr₃⟩ := htriangle Δ hΔ
      have hi₁ : IsIso r.hom₁ := hr₁.symm ▸ h₁
      have hi₃ : IsIso r.hom₃ := hr₃.symm ▸ h₃
      have hi₂ := CategoryTheory.Pretriangulated.isIso₂_of_isIso₁₃ r
        ((closedRestrictionPhi Λ T).map_distinguished Δ hΔ)
        ((closedRestrictionPsi Λ t).map_distinguished Δ hΔ) hi₁ hi₃
      refine ⟨Δ.obj₂, ?_, ⟨Iso.refl _⟩⟩
      change IsIso ((closedRestrictionRho Λ t).app Δ.obj₂)
      rw [← hr₂]
      exact hi₂
  have hclass : IsSupportedImageGenerationClass Λ T E := by
    refine ⟨hEtri, hEiso, ?_, ?_, ?_, ?_⟩
    · intro K N i r hir hN
      exact @restriction_iso_of_retract _ _ _ _ _ _ ρ _ _ i r hir hN
    · intro I K c hc hK
      obtain ⟨c₀, ⟨hc₀⟩, ⟨hF⟩, ⟨hG⟩, _⟩ := hproducts I K
      have hi := restriction_iso_of_limit ρ (Discrete.functor K) c₀ hF hG
        (fun j ↦ hK j.as)
      exact @restriction_iso_of_iso _ _ _ _ _ _ ρ _ _
        (hc₀.conePointUniqueUpToIso hc) hi
    · intro tree' S' p' N hN
      exact hmodels tree' S' p' N hN
    · intro I _ _ D a c hc ha hD
      have hi := restriction_iso_of_filtered Λ t hfiltered I D a ha hD
      exact @restriction_iso_of_iso _ _ _ _ _ _ ρ _ _
        (DerivedCategory.Q.mapIso ((colimit.isColimit D).coconePointUniqueUpToIso hc)) hi
  exact supported_image_mem_bounded_derived_generation Λ ℓ hΛ tree p L M hL hM u E hclass

end AlgebraicGeometry.ProEtale.CondensedRing
