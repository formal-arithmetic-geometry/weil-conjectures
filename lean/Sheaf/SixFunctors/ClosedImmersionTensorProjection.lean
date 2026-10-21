/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G4
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Tensor

import Mathlib.AlgebraicGeometry.Noetherian
import Sheaf.AlgebraicGeometry.CondensedOpenClosedInternalHom
import WeilConjectures.CategoryTheory.Adjunction.ProjectionMap

/-! # closed immersion projection formula

Source: the open and closed immersion paragraphs and the derived version of
`literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-lem-int-tensor/`
`det-lem-int-tensor-projection.proof.md`
(blueprint: lem-sfb-closed-immersion-derived-tensor-projection).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Limits MonoidalCategory MonObj
open scoped CategoryTheory.Obj
open AlgebraicGeometry AlgebraicGeometry.ProEtale Scheme

namespace AlgebraicGeometry.ProEtale.CondensedRing

private noncomputable def supportTensorNatIso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    {S X : Scheme.{u}} (f : S ⟶ X) :
    (Functor.postcompose₂.obj (supportPullback Λ f).mapDerivedCategory).obj
        (derivedTensor Λ X) ≅
      (((Functor.whiskeringLeft₂ _).obj (supportPullback Λ f).mapDerivedCategory).obj
        (supportPullback Λ f).mapDerivedCategory).obj (derivedTensor Λ S) := by
  have hn := (Classical.choose_spec
    (ExistsUnique.exists (existsUnique_supportDerivedTensorComparison Λ f))).1
  refine NatIso.ofComponents (fun A ↦ NatIso.ofComponents
    (fun B ↦ supportDerivedTensorComparison Λ f A B) ?_) ?_
  · intro B B' b
    simpa [supportDerivedTensorComparison] using hn A A B B' (𝟙 A) b
  · intro A A' a
    ext B
    simpa [supportDerivedTensorComparison] using hn A A' B B a (𝟙 B)

/-- The closed immersion case of the relative derived projection formula.
Source: `det-lem-int-tensor-projection.proof.md`, closed immersions and Derived version
(blueprint: lem-sfb-closed-immersion-derived-tensor-projection).

Proof: the standing hypotheses make X Noetherian, hence its open complement of the
closed image is quasi-compact. Apply openClosedInternalHomFormulas to f and this
complement; its first component is the canonical closed projection isomorphism.
Assemble the normalized supportDerivedTensorComparison into a natural isomorphism of
curried bifunctors. Form the rightAdjointProjectionMap of the closed pullback
adjunction with this comparison. Its components equal the normalized closed projection
maps, by the unit formula for homEquiv and functoriality of composition. They are
therefore isomorphisms; pointwise detection twice makes the bifunctor map an
isomorphism. Transport the pullback along supportPullbackIsoUpperStar and the exact
closed direct image along rightDerivedFunctorIsoMapDerivedCategory. These operations
preserve both naturality variables. Empty complements, zero coefficients and unbounded
complexes require no separate argument. -/
theorem closedImmersionTensorProjection
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (k : Type u) [Field k] {S X : Scheme.{u}}
    [S.Over (Spec (.of k))] [X.Over (Spec (.of k))]
    [IsSeparated (S ↘ Spec (.of k))]
    [LocallyOfFiniteType (S ↘ Spec (.of k))]
    [QuasiCompact (S ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))]
    (f : S ⟶ X) [f.IsOver (Spec (.of k))]
    [IsClosedImmersion f] :
    Nonempty (
      (((Functor.whiskeringLeft₂ _).obj
          (lowerStar Λ f).rightDerivedFunctor).obj (𝟭 _)).obj
        (derivedTensor Λ X) ≅
      (Functor.postcompose₂.obj
        (lowerStar Λ f).rightDerivedFunctor).obj
        ((((Functor.whiskeringLeft₂ _).obj (𝟭 _)).obj
          ((f)^*⟦Λ⟧.mapDerivedCategory)).obj (derivedTensor Λ S))) := by
  let V : X.Opens := ⟨(Set.range f)ᶜ, f.isClosedEmbedding.isClosed_range.isOpen_compl⟩
  let j := V.ι
  have : IsLocallyNoetherian X :=
    LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace
    (X ↘ Spec (.of k))
  have : IsNoetherian X := ⟨⟩
  have : QuasiCompact j := inferInstance
  have hij : Set.range f.base = (Set.range j.base)ᶜ := by
    simp [j, V]
  let := closedSupport_lowerStarExact Λ f j hij
  obtain ⟨p, _, _, hp, _⟩ := openClosedInternalHomFormulas Λ f j hij
  let adj := closedPullbackDerivedAdjunction Λ f
  let π := adj.rightAdjointProjectionMap (supportTensorNatIso Λ f).hom
  have hiso (P) (T) : IsIso ((π.app P).app T) := by
    have h : (π.app P).app T = (p P T).hom := by
      rw [hp]
      simp [π, Adjunction.rightAdjointProjectionMap_app_app,
        closedSupportProjection, Adjunction.homEquiv_unit, Functor.map_comp,
        supportTensorNatIso, adj]
    rw [h]
    infer_instance
  have hiso' (P) : IsIso (π.app P) := NatIso.isIso_of_isIso_app _
  have : IsIso π := NatIso.isIso_of_isIso_app _
  let er := Functor.mapDerivedCategoryNatIso (supportPullbackIsoUpperStar Λ f)
  let ee := (lowerStar Λ f).rightDerivedFunctorIsoMapDerivedCategory
  refine ⟨?_⟩
  exact (((Functor.whiskeringLeft₂ _).mapIso ee).app (𝟭 _)).app (derivedTensor Λ X) ≪≫
    asIso π ≪≫
    (Functor.postcompose₂.obj (lowerStar Λ f).mapDerivedCategory).mapIso
      ((((Functor.whiskeringLeft₂ _).obj (𝟭 _)).mapIso er).app (derivedTensor Λ S)) ≪≫
    (Functor.postcompose₂.mapIso ee.symm).app
      ((((Functor.whiskeringLeft₂ _).obj (𝟭 _)).obj
        (upperStar Λ f).mapDerivedCategory).obj (derivedTensor Λ S))

end AlgebraicGeometry.ProEtale.CondensedRing
