/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q19
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
public import Mathlib.Algebra.Homology.ShortComplex.Abelian
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Sheaf.Paper.SupportedFiniteModelScalarRigidity
import Sheaf.Paper.SupportedImageRigidityFromModelComparisons
import Sheaf.Paper.ClosedRestrictionDerivedOperations
import Sheaf.AlgebraicGeometry.CondensedClosedSupportAdjunction
import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import Mathlib.Algebra.Homology.HomologicalComplexLimits

/-! # Closed-pair rigidity for supported three-term scalar local models

Source: blueprint latest, sec-six-functors-basics/sk-prop-sf-comp-coherence,
det-sf-comp-coherence-refinement.proof.md, (2), first paragraph.
Agent-extracted full-generality obligation; exact reference WANTED.
(blueprint: lem-sfb-supported-three-term-scalar-rigidity).

A path in a finite qcqs open-closed tree records precisely the support chain. Any
chain in the node embeds in such a tree by adjoining its complementary siblings as
leaves. The path need not end at a leaf. The root path gives the empty chain.
The comparison below is the canonical derived descent of ordinary section pullback,
so its naturality includes every morphism of short complexes.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

attribute [local irreducible] upperStar upperStarLowerStarAdjunction

universe v u' v' w w'

section
variable {C : Type u} [Category.{v} C] [Abelian C]
  {D : Type u'} [Category.{v'} D] [Abelian D] [HasDerivedCategory.{w} D]
  (J : C ⥤ D) [J.Additive] [PreservesFiniteLimits J] [PreservesFiniteColimits J]
  [HasDerivedCategory Ab.{w'}]
  (F G : DerivedCategory D ⥤ DerivedCategory Ab.{w'})
  [F.CommShift ℤ] [G.CommShift ℤ] [F.IsTriangulated] [G.IsTriangulated]
  (τ : F ⟶ G) [NatTrans.CommShift τ ℤ]

set_option backward.isDefEq.respectTransparency false in
private theorem iso_ses (S : ShortComplex C) (hS : S.ShortExact) :
    (IsIso (τ.app ((DerivedCategory.singleFunctor D 0).obj (J.obj S.X₂))) →
      IsIso (τ.app ((DerivedCategory.singleFunctor D 0).obj (J.obj S.X₃))) →
      IsIso (τ.app ((DerivedCategory.singleFunctor D 0).obj (J.obj S.X₁)))) ∧
    (IsIso (τ.app ((DerivedCategory.singleFunctor D 0).obj (J.obj S.X₁))) →
      IsIso (τ.app ((DerivedCategory.singleFunctor D 0).obj (J.obj S.X₂))) →
      IsIso (τ.app ((DerivedCategory.singleFunctor D 0).obj (J.obj S.X₃)))) := by
  let S' := (S.map J).map (HomologicalComplex.single D (ComplexShape.up ℤ) 0)
  have hS' : S'.ShortExact := (hS.map_of_exact J).map_of_exact _
  let Δ := DerivedCategory.triangleOfSES hS'
  have hΔ := DerivedCategory.triangleOfSES_distinguished hS'
  let r : F.mapTriangle.obj Δ ⟶ G.mapTriangle.obj Δ :=
    { hom₁ := τ.app Δ.obj₁
      hom₂ := τ.app Δ.obj₂
      hom₃ := τ.app Δ.obj₃
      comm₁ := τ.naturality Δ.mor₁
      comm₂ := τ.naturality Δ.mor₂
      comm₃ := by
        change (F.map Δ.mor₃ ≫ (F.commShiftIso (1 : ℤ)).hom.app Δ.obj₁) ≫
            (shiftFunctor _ (1 : ℤ)).map (τ.app Δ.obj₁) =
          τ.app Δ.obj₃ ≫ G.map Δ.mor₃ ≫ (G.commShiftIso (1 : ℤ)).hom.app Δ.obj₁
        simp only [Category.assoc, NatTrans.shift_app_comm τ (1 : ℤ) Δ.obj₁,
          NatTrans.naturality_assoc] }
  have hr₁ : r.hom₁ =
      τ.app ((DerivedCategory.singleFunctor D 0).obj (J.obj S.X₁)) := rfl
  have hr₂ : r.hom₂ =
      τ.app ((DerivedCategory.singleFunctor D 0).obj (J.obj S.X₂)) := rfl
  have hr₃ : r.hom₃ =
      τ.app ((DerivedCategory.singleFunctor D 0).obj (J.obj S.X₃)) := rfl
  constructor
  · intro h₂ h₃
    rw [← hr₂] at h₂
    rw [← hr₃] at h₃
    rw [← hr₁]
    exact isIso₁_of_isIso₂₃ r (F.map_distinguished _ hΔ) (G.map_distinguished _ hΔ) h₂ h₃
  · intro h₁ h₂
    rw [← hr₁] at h₁
    rw [← hr₂] at h₂
    rw [← hr₃]
    exact isIso₃_of_isIso₁₂ r (F.map_distinguished _ hΔ) (G.map_distinguished _ hΔ) h₁ h₂


private theorem iso_homology (S : ShortComplex C)
    (h₂ : IsIso (τ.app ((DerivedCategory.singleFunctor D 0).obj (J.obj S.X₂))))
    (hf : IsIso (τ.app ((DerivedCategory.singleFunctor D 0).obj (J.obj (image S.f)))))
    (hg : IsIso (τ.app ((DerivedCategory.singleFunctor D 0).obj (J.obj (image S.g))))) :
    IsIso (τ.app ((DerivedCategory.singleFunctor D 0).obj (J.obj S.homology))) := by
  let H := J ⋙ DerivedCategory.singleFunctor D 0
  let A := ShortComplex.mk (kernel.ι S.g) (Abelian.coimage.π S.g)
    (cokernel.condition (kernel.ι S.g))
  have hA : A.ShortExact := { exact := ShortComplex.exact_cokernel _ }
  have hAg : IsIso (τ.app (H.obj A.X₃)) :=
    (NatTrans.isIso_app_iff_of_iso τ
      (H.mapIso (Abelian.coimageIsoImage' S.g))).mpr hg
  have hZ : IsIso (τ.app (H.obj (kernel S.g))) :=
    (iso_ses J F G τ A hA).1 h₂ hAg
  let B := ShortComplex.mk S.abelianImageToKernel (cokernel.π S.abelianImageToKernel)
    (cokernel.condition _)
  have hB : B.ShortExact := { exact := ShortComplex.exact_cokernel _ }
  have hBf : IsIso (τ.app (H.obj B.X₁)) :=
    (NatTrans.isIso_app_iff_of_iso τ
      (H.mapIso (Abelian.imageIsoImage S.f))).mpr hf
  have hQ : IsIso (τ.app (H.obj (cokernel S.abelianImageToKernel))) :=
    (iso_ses J F G τ B hB).2 hBf hZ
  have heq : kernel.lift S.g S.f S.zero =
      Abelian.factorThruImage S.f ≫ S.abelianImageToKernel := by
    apply (cancel_mono (kernel.ι S.g)).1
    simp
  let e : S.homology ≅ cokernel S.abelianImageToKernel :=
    S.homologyIsoCokernelLift ≪≫
      eqToIso (congrArg (fun f : S.X₁ ⟶ kernel S.g => cokernel f) heq) ≪≫
      cokernelEpiComp (Abelian.factorThruImage S.f) S.abelianImageToKernel
  exact (NatTrans.isIso_app_iff_of_iso τ (H.mapIso e)).mpr hQ
end

private theorem path_exact
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {T S : Scheme.{u}} {tree : QcqsOpenClosedTree T}
    (p : tree.Path S) : (p.extension Λ).Additive ∧
    PreservesFiniteLimits (p.extension Λ) ∧ PreservesFiniteColimits (p.extension Λ) := by
  induction p with
  | root tree =>
    change (𝟭 _).Additive ∧ PreservesFiniteLimits (𝟭 _) ∧ PreservesFiniteColimits (𝟭 _)
    exact ⟨inferInstance, inferInstance, inferInstance⟩
  | openBranch j i h a b p ih =>
    have := ih.1
    have := ih.2.1
    have := ih.2.2
    change (p.extension Λ ⋙ openImmersionLowerShriek Λ j).Additive ∧
      PreservesFiniteLimits (p.extension Λ ⋙ openImmersionLowerShriek Λ j) ∧
      PreservesFiniteColimits (p.extension Λ ⋙ openImmersionLowerShriek Λ j)
    exact ⟨inferInstance, inferInstance, inferInstance⟩
  | closedBranch j i h a b p ih =>
    have := ih.1
    have := ih.2.1
    have := ih.2.2
    have hij : Set.range i.base = (Set.range j.base)ᶜ := by rw [h, compl_compl]
    have := closedSupport_lowerStarExact Λ i j hij
    change (p.extension Λ ⋙ lowerStar Λ i).Additive ∧
      PreservesFiniteLimits (p.extension Λ ⋙ lowerStar Λ i) ∧
      PreservesFiniteColimits (p.extension Λ ⋙ lowerStar Λ i)
    exact ⟨inferInstance, inferInstance, inferInstance⟩

/-- The actual derived restriction on the supported kernel modulo image is invertible.
All module maps are arbitrary. No hypothesis is imposed on the homology module.

Source: blueprint latest, det-sf-comp-coherence-refinement.proof.md, (2), first paragraph.
Agent-extracted full-generality obligation; exact reference WANTED.
(blueprint: lem-sfb-supported-three-term-scalar-rigidity).

Proof: The single-model comparison supplies restriction for the middle term and, uniformly
for every support path, the premise of the conditional image theorem. Apply that theorem
to the two actual differentials. The resulting comparisons on their images, together with
the middle comparison, suffice by two short exact sequences. First use
`kernel g → X₂ → coimage g`, identifying coimage with image. Then use
`Abelian.image f → kernel g → cokernel abelianImageToKernel`. The latter cokernel is the
specified homology: `kernel.lift g f` factors through the epimorphism onto `Abelian.image f`,
which does not change its cokernel. The path extension is exact by induction, using exact
open extension and the closed support adjunction for each quasi-compact complement.
After this extension and the single-complex functor, each row gives a distinguished
triangle. The existing closed-restriction operations theorem supplies triangulated section functors
and shift compatibility of restriction; naturality gives the morphism of triangles with
exactly the given restriction components.
Two-out-of-three applied first at the kernel and then at the homology proves the claim.
Naturality along the canonical homology isomorphism identifies the last arrow with the
one displayed below. No new claim of completeness or constructibility of images, kernels
or homology is made. The argument includes identity paths, empty schemes and zero models.
-/
theorem supported_three_term_scalar_rigidity
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
    (tree : QcqsOpenClosedTree T) (p : tree.Path S)
    (L : ShortComplex
      (Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1}) (condensedRingObj Λ S)))
    (hL₁ : HasFiniteConstantLocalModel Λ S L.X₁)
    (hL₂ : HasFiniteConstantLocalModel Λ S L.X₂)
    (hL₃ : HasFiniteConstantLocalModel Λ S L.X₃) :
    IsIso ((Functor.rightDerivedPullback (upperStar Λ t)
      ((Functor.whiskerRight (upperStarLowerStarAdjunction Λ t).unit
          (condensedModuleSections Λ T) ≫
        Functor.whiskerLeft (upperStar Λ t)
          (Functor.whiskerLeft (Mod.forget (condensedRingObj Λ T₀))
            ((sheafSections (Scheme.ProEt.topology T₀) Ab.{u + 1}).map
              (MorphismProperty.Over.homMk
                (pullback.lift t (𝟙 T₀)
                  ((Category.comp_id t).trans (Category.id_comp t).symm))
                (pullback.lift_snd _ _ _)).op))) :
        condensedModuleSections Λ T ⟶ upperStar Λ t ⋙ condensedModuleSections Λ T₀)).app
      ((DerivedCategory.singleFunctor _ 0).obj ((p.extension Λ).obj L.homology))) := by
  have hmodels : ∀ (tree' : QcqsOpenClosedTree T) (S' : Scheme.{u})
      (p' : tree'.Path S')
      (N : Mod (Sheaf (Scheme.ProEt.topology S') Ab.{u + 1}) (condensedRingObj Λ S')),
      HasFiniteConstantLocalModel Λ S' N →
        IsIso ((supportedModelDerivedRestriction Λ t p').app N) := by
    intro tree' S' p' N hN
    exact supported_finite_model_scalar_rigidity Λ ℓ hΛ t ht tree' p' N hN
  have hf := supported_image_rigidity_from_model_comparisons Λ ℓ
    hΛ t ht hmodels
    tree p L.X₁ L.X₂ hL₁ hL₂ L.f
  have hg := supported_image_rigidity_from_model_comparisons Λ ℓ
    hΛ t ht hmodels
    tree p L.X₂ L.X₃ hL₂ hL₃ L.g
  have h₂ := hmodels tree S p L.X₂ hL₂
  obtain ⟨ha, hl, hc⟩ := path_exact Λ p
  have hops := closed_restriction_derived_operations Λ t
  have := hops.2.2.1
  have := hops.2.2.2.1
  have := hops.2.2.2.2.1
  change IsIso ((closedRestrictionRho Λ t).app
    ((DerivedCategory.singleFunctor _ 0).obj ((p.extension Λ).obj L.homology)))
  change IsIso ((closedRestrictionRho Λ t).app
    ((DerivedCategory.singleFunctor _ 0).obj ((p.extension Λ).obj L.X₂))) at h₂
  change IsIso ((closedRestrictionRho Λ t).app
    ((DerivedCategory.singleFunctor _ 0).obj ((p.extension Λ).obj (image L.f)))) at hf
  change IsIso ((closedRestrictionRho Λ t).app
    ((DerivedCategory.singleFunctor _ 0).obj ((p.extension Λ).obj (image L.g)))) at hg
  exact iso_homology (p.extension Λ) (closedRestrictionPhi Λ T)
    (closedRestrictionPsi Λ t) (closedRestrictionRho Λ t) L h₂ hf hg

end AlgebraicGeometry.ProEtale.CondensedRing
