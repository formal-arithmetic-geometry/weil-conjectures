/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q1
-/
module

public import Sheaf.AlgebraicGeometry.StrictHenselizationStructuralMap
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.GlobalSections
public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.MorphismDefs
public import WeilConjectures.SixFunctors.Etale.Derived.GlobalSections
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusExact

/-!
# Canonical restriction to a strict henselization

The germ restriction `r_G : G_s ⟶ Γ(S_(s), g⁻¹G)` is characterised by its components at the
representative affine pointed neighbourhoods (the unit of `g⁻¹ ⊣ g_*` followed by restriction
along the section `S_(s) ⟶ V ×_S S_(s)` given by the limit leg); it exists and is unique
(`existsUnique_strictHenselizationStalkRestriction`). The canonical restriction
`ρ^q : (R^q f_* F)_s ⟶ H^q(X ×_S S_(s), p⁻¹F)` is `r ≫ strictHenselizationCohomologyComparison`
for that unique `r`.

Source: Stacks, Tag 03Q9, theorem-higher-direct-images, its restriction construction
(blueprint: def-weil-pbc-strict-henselization-restriction).
-/

@[expose] public section

universe v

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry

namespace AlgebraicGeometry.Etale

variable {S : Scheme.{v}} {Ω : Type v} [Field Ω] [IsAlgClosed Ω]
  (s : Spec (.of Ω) ⟶ S)

/-- The section `S_(s) ⟶ V ×_S S_(s)` of the base change of a representative affine pointed
neighbourhood `V`, with first component the limit leg `S_(s) ⟶ Spec Γ(V, ⊤) ≅ V`.
Source: Stacks, Tag 03Q9, proof of theorem-higher-direct-images
(blueprint: def-weil-pbc-strict-henselization-restriction). -/
noncomputable def strictHenselizationNeighbourhoodSection
    (j : SmallModel.{v} (Scheme.strictHenselizationNeighbourhoods s)) :
    Scheme.Etale.mk (𝟙 (Scheme.strictHenselizationScheme s)) ⟶
      (Scheme.strictHenselizationStructuralMap s).Etale.obj
        ((Scheme.AffineEtale.Spec S).obj
          ((equivSmallModel.{v} (Scheme.strictHenselizationNeighbourhoods s)).inverse.obj j).1) :=
  MorphismProperty.Over.homMk
    (pullback.lift
      ((Scheme.strictHenselizationCone s).π.app (op (op j)) ≫
        Spec.map (Scheme.ΓSpecIso
          ((equivSmallModel.{v} (Scheme.strictHenselizationNeighbourhoods s)).inverse.obj
            j).1.left.unop).inv)
      (𝟙 _)
      (by
        rw [Category.assoc, Category.id_comp]
        exact Classical.choose_spec (Scheme.exists_strictHenselizationStructuralMap s) j))
    (by
      change _ ≫ pullback.snd _ (Scheme.strictHenselizationStructuralMap s) = _
      simp
      rfl) (by trivial)

/-- Restrict a section over a representative affine pointed neighbourhood to the strict
henselization: the unit of `g⁻¹ ⊣ g_*` on sections over `V`, then restriction along
`strictHenselizationNeighbourhoodSection`.
Source: Stacks, Tag 03Q9, proof of theorem-higher-direct-images
(blueprint: def-weil-pbc-strict-henselization-restriction). -/
noncomputable def strictHenselizationSectionRestriction
    (F : Sheaf S.smallEtaleTopology AddCommGrpCat.{v + 1})
    (j : SmallModel.{v} (Scheme.strictHenselizationNeighbourhoods s)) :
    F.obj.obj (op ((Scheme.AffineEtale.Spec S).obj
        ((equivSmallModel.{v} (Scheme.strictHenselizationNeighbourhoods s)).inverse.obj j).1)) ⟶
      (Sheaf.Γ (Scheme.strictHenselizationScheme s).smallEtaleTopology
        AddCommGrpCat.{v + 1}).obj
        ((upperStar AddCommGrpCat.{v + 1}
          (Scheme.strictHenselizationStructuralMap s)).obj F) :=
  ((upperStarLowerStarAdjunction AddCommGrpCat.{v + 1}
      (Scheme.strictHenselizationStructuralMap s)).unit.app F).hom.app
      (op ((Scheme.AffineEtale.Spec S).obj
        ((equivSmallModel.{v} (Scheme.strictHenselizationNeighbourhoods s)).inverse.obj j).1)) ≫
    ((upperStar AddCommGrpCat.{v + 1}
      (Scheme.strictHenselizationStructuralMap s)).obj F).obj.map
      (strictHenselizationNeighbourhoodSection s j).op ≫
    (Sheaf.ΓNatIsoSheafSections _ _
      (IsTerminal.isTerminalOfObj
        (MorphismProperty.Over.forget @AlgebraicGeometry.Etale ⊤
          (Scheme.strictHenselizationScheme s))
        (Scheme.Etale.mk (𝟙 (Scheme.strictHenselizationScheme s))) Over.mkIdTerminal)).inv.app _

/-- The germ restriction `r : F_s ⟶ Γ(S_(s), g⁻¹F)`: its composite with the germ map of every
representative affine pointed neighbourhood is `strictHenselizationSectionRestriction`.
Source: Stacks, Tag 03Q9, proof of theorem-higher-direct-images
(blueprint: def-weil-pbc-strict-henselization-restriction). -/
def IsStrictHenselizationStalkRestriction
    (F : Sheaf S.smallEtaleTopology AddCommGrpCat.{v + 1})
    (r : (Scheme.pointSmallEtale s).sheafFiber.obj F ⟶
      (Sheaf.Γ (Scheme.strictHenselizationScheme s).smallEtaleTopology
        AddCommGrpCat.{v + 1}).obj
        ((upperStar AddCommGrpCat.{v + 1}
          (Scheme.strictHenselizationStructuralMap s)).obj F)) : Prop :=
  ∀ j : SmallModel.{v} (Scheme.strictHenselizationNeighbourhoods s),
    (Scheme.pointSmallEtale s).toPresheafFiber
        ((Scheme.AffineEtale.Spec S).obj
          ((equivSmallModel.{v} (Scheme.strictHenselizationNeighbourhoods s)).inverse.obj j).1)
        ((equivSmallModel.{v} (Scheme.strictHenselizationNeighbourhoods s)).inverse.obj j).2
        F.obj ≫ r =
      strictHenselizationSectionRestriction s F j

/-- The germ restriction exists and is unique.
Source: Stacks, Tag 03Q9, proof of theorem-higher-direct-images
(blueprint: def-weil-pbc-strict-henselization-restriction).
Proof: the representative affine pointed neighbourhoods are initial among all pointed
neighbourhoods (`strictHenselization_properties`), so the stalk is the colimit of `F` over
them and maps out of it are determined by these components. The components are compatible
with pointed maps by naturality of the unit and of the limit legs, so they descend. -/
theorem existsUnique_strictHenselizationStalkRestriction
    (F : Sheaf S.smallEtaleTopology AddCommGrpCat.{v + 1}) :
    ∃! r : (Scheme.pointSmallEtale s).sheafFiber.obj F ⟶
      (Sheaf.Γ (Scheme.strictHenselizationScheme s).smallEtaleTopology
        AddCommGrpCat.{v + 1}).obj
        ((upperStar AddCommGrpCat.{v + 1}
          (Scheme.strictHenselizationStructuralMap s)).obj F),
      IsStrictHenselizationStalkRestriction s F r := by
  sorry

/-- Global sections on the strict henselization are exact.
Source: Stacks, Tag 03QO (strictly henselian local schemes have exact global sections)
(blueprint: def-weil-pbc-strict-henselization-restriction).
Proof: the pointed étale neighbourhood colimit is the strict henselian local ring
(Stacks, lemma-describe-etale-local-ring, used in 03Q9). Every étale covering of its
closed point has a section over this strictly henselian local scheme. Thus a locally
surjective map of sheaves is surjective on global sections.
The global sections functor is already left exact, so it preserves finite colimits. -/
theorem strictHenselization_globalSections_preservesFiniteColimits :
    PreservesFiniteColimits
      (Sheaf.Γ (Scheme.strictHenselizationScheme s).smallEtaleTopology
        AddCommGrpCat.{v + 1}) := by
  sorry

/-- The canonical Leray and exact-global-sections comparison over the strict local base.
Source: Stacks, Tags 03Q9 and 03QO; the derived-functor composition isomorphism
(blueprint: def-weil-pbc-strict-henselization-restriction). -/
noncomputable def strictHenselizationLerayHomologyIso
    {X : Scheme.{v}} (f : X ⟶ S) (q : ℤ)
    (K : DerivedCategory.Plus
      (Sheaf (pullback f (Scheme.strictHenselizationStructuralMap s)).smallEtaleTopology
        AddCommGrpCat.{v + 1})) :
    (Sheaf.Γ (Scheme.strictHenselizationScheme s).smallEtaleTopology
      AddCommGrpCat.{v + 1}).obj
      ((DerivedCategory.Plus.homologyFunctor _ q).obj
        ((rightDerivedLowerStarPlus AddCommGrpCat.{v + 1}
          (pullback.snd f (Scheme.strictHenselizationStructuralMap s))).obj K)) ≅
    (cohomology AddCommGrpCat.{v + 1}
      (pullback f (Scheme.strictHenselizationStructuralMap s)) q).obj
      (DerivedCategory.Plus.ι.obj K) :=
  haveI := strictHenselization_globalSections_preservesFiniteColimits s
  (Functor.mapDerivedCategoryPlusHomologyFunctorIso
      (Sheaf.Γ (Scheme.strictHenselizationScheme s).smallEtaleTopology
        AddCommGrpCat.{v + 1}) q).app
      ((rightDerivedLowerStarPlus AddCommGrpCat.{v + 1}
        (pullback.snd f (Scheme.strictHenselizationStructuralMap s))).obj K) ≪≫
    (DerivedCategory.Plus.homologyFunctor _ q).mapIso
      (((Sheaf.Γ (Scheme.strictHenselizationScheme s).smallEtaleTopology
        AddCommGrpCat.{v + 1}).rightDerivedFunctorPlusIsoMapDerivedCategoryPlus).symm.app _) ≪≫
    (DerivedCategory.homologyFunctor _ q).mapIso
      ((Sheaf.Γ (Scheme.strictHenselizationScheme s).smallEtaleTopology
        AddCommGrpCat.{v + 1}).rightDerivedFunctorPlusCompatibility.app _) ≪≫
    (DerivedCategory.homologyFunctor _ q).mapIso
      ((rightDerivedGlobalSections AddCommGrpCat.{v + 1}
        (Scheme.strictHenselizationScheme s)).mapIso
        ((Functor.rightDerivedFunctorPlusCompatibility
          (lowerStar AddCommGrpCat.{v + 1}
            (pullback.snd f (Scheme.strictHenselizationStructuralMap s)))).app K)) ≪≫
    (DerivedCategory.homologyFunctor _ q).mapIso
      ((rightDerivedLowerStarCompRightDerivedGlobalSectionsIso AddCommGrpCat.{v + 1}
        (pullback.snd f (Scheme.strictHenselizationStructuralMap s))).app
        (DerivedCategory.Plus.ι.obj K))

/-- The comparison `Γ(S_(s), g⁻¹ R^q f_* F) ⟶ H^q(X ×_S S_(s), p⁻¹F)`: commute the exact
inverse image with cohomology, apply the derived base-change mate `g⁻¹ Rf_* ⟶ Rf'_* p⁻¹`
(the mate of the pullback-square comparison under the derived adjunctions), then the exact
global sections and Leray isomorphism. The canonical restriction
`ρ^q : (R^q f_* F)_s ⟶ H^q(X ×_S S_(s), p⁻¹F)` of the node is `r ≫` this map, for the unique
`r` with `IsStrictHenselizationStalkRestriction s (R^q f_* F) r`.
Source: Stacks, Tag 03Q9, proof of theorem-higher-direct-images
(blueprint: def-weil-pbc-strict-henselization-restriction). -/
noncomputable def strictHenselizationCohomologyComparison
    {X : Scheme.{v}} (f : X ⟶ S)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{v + 1}) (q : ℕ) :
    (Sheaf.Γ (Scheme.strictHenselizationScheme s).smallEtaleTopology
        AddCommGrpCat.{v + 1}).obj
      ((upperStar AddCommGrpCat.{v + 1} (Scheme.strictHenselizationStructuralMap s)).obj
        ((DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).obj
          ((rightDerivedLowerStarPlus AddCommGrpCat.{v + 1} f).obj
            ((DerivedCategory.Plus.singleFunctor _ 0).obj F)))) ⟶
    (cohomology AddCommGrpCat.{v + 1}
      (pullback f (Scheme.strictHenselizationStructuralMap s)) (q : ℤ)).obj
      ((DerivedCategory.Plus.ι).obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj
          ((upperStar AddCommGrpCat.{v + 1}
            (pullback.fst f (Scheme.strictHenselizationStructuralMap s))).obj F))) :=
  (Sheaf.Γ (Scheme.strictHenselizationScheme s).smallEtaleTopology
      AddCommGrpCat.{v + 1}).map
      ((Functor.mapDerivedCategoryPlusHomologyFunctorIso
        (upperStar AddCommGrpCat.{v + 1} (Scheme.strictHenselizationStructuralMap s))
        (q : ℤ)).hom.app _) ≫
    (Sheaf.Γ (Scheme.strictHenselizationScheme s).smallEtaleTopology
      AddCommGrpCat.{v + 1}).map
      ((DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).map
        ((mateEquiv (upperStarLowerStarAdjunction AddCommGrpCat.{v + 1} f).derivedPlus
          (upperStarLowerStarAdjunction AddCommGrpCat.{v + 1}
            (pullback.snd f (Scheme.strictHenselizationStructuralMap s))).derivedPlus
          (TwoSquare.mk _ _ _ _ (pullbackSquareComparison AddCommGrpCat.{v + 1}
            (IsPullback.of_hasPullback f
              (Scheme.strictHenselizationStructuralMap s)).toCommSq).hom))
            |>.natTrans.app
          ((DerivedCategory.Plus.singleFunctor _ 0).obj F))) ≫
    (strictHenselizationLerayHomologyIso s f (q : ℤ) _).hom ≫
    (cohomology AddCommGrpCat.{v + 1}
      (pullback f (Scheme.strictHenselizationStructuralMap s)) (q : ℤ)).map
      (DerivedCategory.Plus.ι.map
        ((Functor.mapDerivedCategoryPlusSingleFunctor
          (upperStar AddCommGrpCat.{v + 1}
            (pullback.fst f (Scheme.strictHenselizationStructuralMap s))) 0).hom.app F))

end AlgebraicGeometry.Etale
