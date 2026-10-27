/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q08
-/
module

public import Sheaf.Paper.LocalizingAdmissibleCoefficients
public import Sheaf.Paper.CondensedModuleDerivedPushpull
public import Sheaf.Paper.CondensedConstantConstructibility
public import Sheaf.Paper.CondensedQcqsPushforwardContinuity
public import Sheaf.AlgebraicGeometry.ModuleDerivedCohomologyPullback
public import WeilConjectures.AlgebraicGeometry.TorsionEtaleSheaf
public import WeilConjectures.Mathlib.CategoryTheory.ObjectProperty.WeakSerreCoproductClosure
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExactPullback
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
import Sheaf.AlgebraicGeometry.CondensedModulePullbackExact

import WeilConjectures.FromJoel.CategoryTheory.Abelian.GrothendieckAxioms.Colim
import Mathlib.Algebra.Category.Grp.AB
import Sheaf.Paper.ClosedRestrictionDerivedOperations
import Sheaf.Paper.SupportedFiniteModelScalarRigidity
import Sheaf.Paper.WeakSerreSupportedDerivedGeneration

/-!
# Closed torsion rigidity on the topological weak Serre hull

Source: blueprint latest, det-sf-comp-coherence-refinement.proof.md, (2), first paragraph;
the agent-formulated coefficient-transfer obligation, exact reference WANTED
(blueprint: lem-sfb-closed-torsion-rigidity-serre-transfer).

The two helper maps are ordinary section restriction and its total right-derived descent.
They use uncompleted internal modules and the original condensed coefficient ring.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj ZeroObject

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- Pull sections back by the module adjunction unit, then restrict from the pullback of
`id_T` to `id_T₀`. Source: the canonical restriction in the coefficient-transfer obligation,
blueprint latest, det-sf-comp-coherence-refinement.proof.md, (2), first paragraph
(blueprint: lem-sfb-closed-torsion-rigidity-serre-transfer). -/
def torsionRigiditySectionsRestriction {T₀ T : Scheme.{u}} (t : T₀ ⟶ T) :
    condensedModuleSections Λ T ⟶ upperStar Λ t ⋙ condensedModuleSections Λ T₀ :=
  Functor.whiskerRight (upperStarLowerStarAdjunction Λ t).unit
      (condensedModuleSections Λ T) ≫
    Functor.whiskerLeft (upperStar Λ t)
      (Functor.whiskerLeft (Mod.forget (condensedRingObj Λ T₀))
        ((sheafSections (Scheme.ProEt.topology T₀) Ab.{u + 1}).map
          (MorphismProperty.Over.homMk
            (pullback.lift t (𝟙 T₀)
              ((Category.comp_id t).trans (Category.id_comp t).symm))
            (pullback.lift_snd _ _ _)).op))

/-- The canonical ordinary unbounded derived restriction. On a K-injective resolution it
pulls back sections and then compares the pulled-back complex with a target resolution.
Source: blueprint latest, det-sf-comp-coherence-refinement.proof.md, (2), first paragraph,
coefficient-transfer obligation (blueprint: lem-sfb-closed-torsion-rigidity-serre-transfer). -/
def torsionRigidityDerivedRestriction {T₀ T : Scheme.{u}} (t : T₀ ⟶ T) :
    (condensedModuleSections Λ T).rightDerivedFunctor ⟶
      (upperStar Λ t).mapDerivedCategory ⋙
        (condensedModuleSections Λ T₀).rightDerivedFunctor :=
  Functor.rightDerivedPullback (upperStar Λ t) (torsionRigiditySectionsRestriction Λ t)

-- Keep module pullback and its adjunction behind their public interfaces in this proof.
attribute [local irreducible] upperStar upperStarLowerStarAdjunction

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


/-- The canonical derived restriction is invertible on the weak Serre coproduct hull
of finite constant scalar-model constructible modules.

Source: blueprint latest, det-sf-comp-coherence-refinement.proof.md, (2), first paragraph.
Agent-formulated coefficient-transfer obligation; exact full-generality reference WANTED.
(blueprint: lem-sfb-closed-torsion-rigidity-serre-transfer).

Proof:

Let E be the class of derived objects on which the actual restriction is invertible.
The closed-restriction operations theorem supplies triangulated section functors,
shift compatibility and a morphism of distinguished triangles with the given components.
Consequently E contains zero and is closed under isomorphisms, shifts and triangles.
For a retract, apply naturality to the inclusion and retraction: an inverse is obtained
by composing the retraction, the inverse comparison on the larger object and the inclusion.

The normalized product comparisons make E closed under ordinary derived products.
For a strict filtered diagram with a common termwise lower bound, use the normalized
complex representatives from the operations theorem. Every component comparison is a
quasi-isomorphism. Exact filtered colimits in abelian groups make its colimit a
quasi-isomorphism. The comparison cocone equations identify this with the actual
restriction on the colimit, up to the supplied isomorphisms.

The supported finite-model comparison theorem puts every supported scalar local model
in E. Thus E is an admissible class in the definition of supportedImageGenerationHull.
Apply the separate structural weak-Serre generation obligation to M and evaluate its
universal hull membership at E. No finite-complex-heart presentation of M is asserted.
The structural obligation is independent of t and of the torsion comparison hypothesis;
it is the remaining new hole, rather than a claim of net sorry closure.
-/
theorem closed_torsion_rigidity_serre_transfer
    (ℓ : ℕ) [Fact ℓ.Prime]
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
    {T₀ T : Scheme.{u}} [CompactSpace T] [QuasiSeparatedSpace T]
    [CompactSpace T₀] [QuasiSeparatedSpace T₀]
    (t : T₀ ⟶ T) [IsClosedImmersion t]
    (ht : ∀ (F : Sheaf T.smallEtaleTopology Ab.{u + 1}),
      Scheme.IsTorsionAbelianSheaf F → ∀ q : ℕ,
        Function.Bijective (Etale.cohomologyMap t F q))
    (M : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ T))
    (hM : ObjectProperty.weakSerreCoproductClosure.{u + 1}
      (IsConstantModelConstructible Λ T) M) :
    IsIso ((torsionRigidityDerivedRestriction Λ t).app
      ((DerivedCategory.singleFunctor _ 0).obj M)) := by
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
      exact supported_finite_model_scalar_rigidity Λ ℓ hΛ t ht tree' p' N hN
    · intro I _ _ D a c hc ha hD
      have hi := restriction_iso_of_filtered Λ t hfiltered I D a ha hD
      exact @restriction_iso_of_iso _ _ _ _ _ _ ρ _ _
        (DerivedCategory.Q.mapIso ((colimit.isColimit D).coconePointUniqueUpToIso hc)) hi
  exact weakSerre_mem_supported_derived_generation Λ ℓ hΛ T M hM E hclass

end AlgebraicGeometry.ProEtale.CondensedRing
