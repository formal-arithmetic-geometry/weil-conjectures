/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.LocalizedResidueHomology
public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
import WeilConjectures.AlgebraicGeometry.OpenModuleStalkFreeProjective
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import Mathlib.Algebra.Homology.Additive
import WeilConjectures.Algebra.Homology.KFlatStalkCriterion
import WeilConjectures.Algebra.Homology.BoundedFlatKFlat
import WeilConjectures.Topology.PointModuleEvaluationEquivalence
import WeilConjectures.AlgebraicGeometry.ResiduePullbackGlobalSections

/-! # Natural residue homology comparison for localized strictly perfect complexes

Source: Stacks Project, Tags 06YJ and 0098.
(blueprint: lem-sc-localized-strict-perfect-residue-homology).
-/

@[expose] public section

set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem inverse_naturality_of_isIso_app
    {C D : Type*} [Category C] [Category D] {F G : C ⥤ D}
    (τ : F ⟶ G) {P Q : C} (α : P ⟶ Q) [IsIso (τ.app P)] [IsIso (τ.app Q)] :
    G.map α ≫ inv (τ.app Q) = inv (τ.app P) ≫ F.map α := by
  apply (cancel_epi (τ.app P)).mp
  rw [← Category.assoc, ← τ.naturality α, Category.assoc, IsIso.hom_inv_id,
    Category.comp_id, IsIso.hom_inv_id_assoc]

private theorem strictlyPerfect_overEquiv_isKFlat (S : Scheme.{u}) (U : S.Opens)
    (P : CochainComplex
      (SheafOfModules.{u} ((moduleRings S.toRingedSpace).over U)) ℤ)
    (hP : Scheme.IsStrictlyPerfect S U P) :
    letI : (Scheme.Modules.overEquiv U).functor.Additive :=
      Functor.additive_of_preserves_binary_products _
    CochainComplex.IsAcyclicTensorKFlat (R := U.toScheme.sheaf)
      (((Scheme.Modules.overEquiv U).functor.mapHomologicalComplex (.up ℤ)).obj P) := by
  classical
  let O := (Scheme.Modules.overEquiv U).functor
  have : O.Additive := Functor.additive_of_preserves_binary_products _
  let K := (O.mapHomologicalComplex (.up ℤ)).obj P
  apply (RingedSpace.isKFlat_iff_stalk_isKFlat U.toScheme.toRingedSpace K).2
  intro y B hB
  let T := RingedSpace.moduleStalkFunctor U.toScheme.toRingedSpace y
  let C := (T.mapHomologicalComplex (.up ℤ)).obj K
  have hbounded : ∃ b : ℤ, ∀ i : ℤ, b < i → IsZero (C.X i) := by
    obtain ⟨a, b, hab⟩ := hP.1
    exact ⟨b, fun i hi ↦ T.map_isZero (O.map_isZero (hab i (Or.inr hi)))⟩
  have hflat : ∀ i : ℤ, Module.Flat (U.toScheme.presheaf.stalk y) (C.X i) := by
    intro i
    obtain ⟨m, ι, π, hιπ⟩ := hP.2 i
    let R := ModuleCat.restrictScalars (U.ι.stalkMap y).hom
    let er := (asIso (U.ι.stalkMap y)).commRingCatIsoToRingEquiv
    have : R.IsEquivalence := ModuleCat.restrictScalars_isEquivalence_of_ringEquiv er
    have hfree : Projective (T.obj (O.obj (SheafOfModules.free
        (R := (moduleRings S.toRingedSpace).over U) (ULift.{u} (Fin m))))) := by
      apply R.projective_of_map_projective
      exact openModuleStalk_free_projective S U y m
    have hret : Retract (C.X i) (T.obj (O.obj (SheafOfModules.free
        (R := (moduleRings S.toRingedSpace).over U) (ULift.{u} (Fin m))))) :=
      ⟨T.map (O.map ι), T.map (O.map π), by
        rw [← T.map_comp, ← O.map_comp, hιπ, O.map_id]
        exact T.map_id (O.obj (P.X i))⟩
    have : Projective (C.X i) := hret.projective
    have : Module.Projective (U.toScheme.presheaf.stalk y) (C.X i) := inferInstance
    infer_instance
  exact CochainComplex.acyclic_mapBifunctor_of_boundedAbove_flat C hbounded hflat B hB

set_option maxHeartbeats 600000 in
-- The residue and over-site comparisons involve several chosen derived localizations.
/-- Termwise residue stalk homology of strictly perfect localized complexes agrees
naturally with localized derived residue homology. The comparisons are simultaneous
for all strictly perfect complexes and all their chain maps.
Source: Stacks Project, Tags 06YJ and 0098.
(blueprint: lem-sc-localized-strict-perfect-residue-homology).

Proof: Transport a localized complex to the open subscheme by overEquiv. This exact
module equivalence preserves zero objects and finite free retractions. Stalks take
these retractions to finite projective modules, hence flat modules. Finite support
bounds the stalk complexes above. Bounded-above flat module complexes are K-flat,
and the stalk criterion makes the transported sheaf complex K-flat. The chosen
derived pullback's counit is therefore invertible. The counit is
a natural transformation on the homotopy category; therefore its inverse comparisons
commute with every chain map between these complexes. The exact over-site equivalence
also has a natural comparison with localization Q. Apply degree-zero derived homology
and the exact global-sections functor of the one-point residue scheme. Its homology
comparison identifies this with homology of termwise tensor pullback. Finally the
natural residuePullback_globalSections_iso identifies that complex with residue
extension of the localized stalk complex. Composing gives t; naturality of each
factor gives the displayed equation. Zero complexes, zero maps and shifted complexes
satisfy the same equation. No sign or negative-degree vanishing assumption is used. -/
theorem exists_localizedStrictPerfectResidueHomology_iso (S : Scheme.{u}) (U : S.Opens)
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings S.toRingedSpace).over U))]
    (x : U.toScheme) :
    letI : (Scheme.Modules.overEquiv U).functor.Additive :=
      Functor.additive_of_preserves_binary_products _
    letI : (ModuleCat.extendScalars (IsLocalRing.residue
        (U.toScheme.presheaf.stalk x))).Additive :=
      (ModuleCat.extendRestrictScalarsAdj (IsLocalRing.residue
        (U.toScheme.presheaf.stalk x))).left_adjoint_additive
    letI : (RingedSpace.moduleStalkFunctor U.toScheme.toRingedSpace x).PreservesZeroMorphisms :=
      RingedSpace.moduleStalkFunctor_preservesZeroMorphisms U.toScheme.toRingedSpace x
    letI : ((Scheme.Modules.overEquiv U).functor ⋙
        RingedSpace.moduleStalkFunctor U.toScheme.toRingedSpace x ⋙
        ModuleCat.extendScalars (IsLocalRing.residue
          (U.toScheme.presheaf.stalk x))).PreservesZeroMorphisms :=
      { map_zero := by
          intro M N
          simp only [Functor.comp_map]
          rw [Functor.map_zero, Functor.map_zero, Functor.map_zero] }
    let F := ((Scheme.Modules.overEquiv U).functor ⋙
      RingedSpace.moduleStalkFunctor U.toScheme.toRingedSpace x ⋙
      ModuleCat.extendScalars (IsLocalRing.residue (U.toScheme.presheaf.stalk x)))
    ∃ t : ∀ (P : CochainComplex
        (SheafOfModules.{u} ((moduleRings S.toRingedSpace).over U)) ℤ)
        (_hP : Scheme.IsStrictlyPerfect S U P),
          ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj P).homology 0 ≅
            (localizedResidueHomology S U x).obj (DerivedCategory.Q.obj P),
      ∀ (P Q : CochainComplex
          (SheafOfModules.{u} ((moduleRings S.toRingedSpace).over U)) ℤ)
        (hP : Scheme.IsStrictlyPerfect S U P) (hQ : Scheme.IsStrictlyPerfect S U Q)
        (α : P ⟶ Q),
        HomologicalComplex.homologyMap
            ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map α) 0 ≫ (t Q hQ).hom =
          (t P hP).hom ≫ (localizedResidueHomology S U x).map (DerivedCategory.Q.map α) :=
  by
    classical
    let O := (Scheme.Modules.overEquiv U).functor
    have : O.Additive := Functor.additive_of_preserves_binary_products _
    have : (ModuleCat.extendScalars (IsLocalRing.residue
        (U.toScheme.presheaf.stalk x))).Additive :=
      (ModuleCat.extendRestrictScalarsAdj (IsLocalRing.residue
        (U.toScheme.presheaf.stalk x))).left_adjoint_additive
    have : (RingedSpace.moduleStalkFunctor U.toScheme.toRingedSpace
        x).PreservesZeroMorphisms :=
      RingedSpace.moduleStalkFunctor_preservesZeroMorphisms U.toScheme.toRingedSpace x
    have : (O ⋙ RingedSpace.moduleStalkFunctor U.toScheme.toRingedSpace x ⋙
        ModuleCat.extendScalars (IsLocalRing.residue
          (U.toScheme.presheaf.stalk x))).PreservesZeroMorphisms :=
      { map_zero := by
          intro M N
          simp only [Functor.comp_map]
          rw [Functor.map_zero, Functor.map_zero, Functor.map_zero] }
    let A := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace)
    let B := SheafOfModules.{u}
      (moduleRings (Spec (U.toScheme.residueField x)).toRingedSpace)
    let : HasDerivedCategory.{u + 1} U.toScheme.Modules := HasDerivedCategory.standard _
    let : HasDerivedCategory.{u + 1} A := HasDerivedCategory.standard _
    let : HasDerivedCategory.{u + 1} B := HasDerivedCategory.standard _
    let : HasDerivedCategory.{u + 1} (Spec (U.toScheme.residueField x)).Modules :=
      HasDerivedCategory.standard _
    let f := U.toScheme.fromSpecResidueField x
    obtain ⟨_, _, _, _, _, _, _, F, hF, hmap, hAdd, ε, _, _, hcompute⟩ :=
      (derivedPullback_spec.{u, u + 1} f)
    have hF' : F = Scheme.Modules.tensorPullback f :=
      CategoryTheory.Functor.ext hF (fun M N a ↦ hmap a)
    subst F
    let F := Scheme.Modules.tensorPullback f
    have : F.Additive := hAdd
    let Fc := F.mapHomologicalComplex (.up ℤ)
    let Oc := O.mapHomologicalComplex (.up ℤ)
    let Γ : B ⥤ ModuleCat.{u} (U.toScheme.residueField x) :=
      SheafOfModules.evaluation
        (moduleRings (Spec (U.toScheme.residueField x)).toRingedSpace) (Opposite.op ⊤) ⋙
      ModuleCat.restrictScalars (Scheme.ΓSpecIso (U.toScheme.residueField x)).inv.hom
    have : (RingedSpace.globalSectionsFunctor
        (Spec (U.toScheme.residueField x)).toRingedSpace).IsEquivalence :=
      RingedSpace.globalSectionsFunctor_isEquivalence_of_unique _
    have : PreservesFiniteLimits
        (SheafOfModules.evaluation
          (moduleRings (Spec (U.toScheme.residueField x)).toRingedSpace) (Opposite.op ⊤)) :=
      inferInstanceAs (PreservesFiniteLimits (RingedSpace.globalSectionsFunctor
        (Spec (U.toScheme.residueField x)).toRingedSpace))
    have : PreservesFiniteColimits
        (SheafOfModules.evaluation
          (moduleRings (Spec (U.toScheme.residueField x)).toRingedSpace) (Opposite.op ⊤)) :=
      inferInstanceAs (PreservesFiniteColimits (RingedSpace.globalSectionsFunctor
        (Spec (U.toScheme.residueField x)).toRingedSpace))
    have : PreservesFiniteLimits Γ := comp_preservesFiniteLimits _ _
    have : PreservesFiniteColimits Γ := comp_preservesFiniteColimits _ _
    have : Γ.Additive := Functor.additive_of_preserves_binary_products _
    have : Γ.PreservesHomology := inferInstance
    let H := DerivedCategory.homologyFunctor B 0
    let HM := HomologicalComplex.homologyFunctor
      (ModuleCat.{u} (U.toScheme.residueField x)) (.up ℤ) 0
    let hΓ := (Γ.mapHomologicalComplexHomologyIso (.up ℤ) 0).symm
    obtain ⟨d⟩ := Scheme.nonempty_residuePullback_globalSections_iso U.toScheme x
    let v := NatIso.mapHomologicalComplex (Functor.isoWhiskerLeft O d) (.up ℤ)
    let z := Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft (Oc ⋙ Fc) (DerivedCategory.homologyFunctorFactors B 0)) Γ ≪≫
      Functor.isoWhiskerLeft (Oc ⋙ Fc) hΓ ≪≫ Functor.isoWhiskerRight v HM
    obtain ⟨εc, hεc⟩ : ∃ εc :
        DerivedCategory.Q ⋙ derivedPullback.{u, u + 1} f ⟶ Fc ⋙ DerivedCategory.Q,
        ∀ (P : CochainComplex
            (SheafOfModules.{u} ((moduleRings S.toRingedSpace).over U)) ℤ),
          Scheme.IsStrictlyPerfect S U P → IsIso (εc.app (Oc.obj P)) := by
      refine ⟨(Functor.isoWhiskerRight (DerivedCategory.quotientCompQhIso A).symm
          (derivedPullback f)).hom ≫
        Functor.whiskerLeft (HomotopyCategory.quotient A (.up ℤ)) ε ≫
        (Functor.isoWhiskerRight (F.mapHomotopyCategoryFactors (.up ℤ))
          DerivedCategory.Qh).hom ≫
        (Functor.isoWhiskerLeft Fc (DerivedCategory.quotientCompQhIso B)).hom, ?_⟩
      intro P hP
      have hε : IsIso (ε.app ((HomotopyCategory.quotient A (.up ℤ)).obj (Oc.obj P))) :=
        hcompute _ (strictlyPerfect_overEquiv_isKFlat S U P hP)
      change IsIso
        (((Functor.isoWhiskerRight (DerivedCategory.quotientCompQhIso A).symm
          (derivedPullback f)).app (Oc.obj P)).hom ≫
        ε.app ((HomotopyCategory.quotient A (.up ℤ)).obj (Oc.obj P)) ≫
        ((Functor.isoWhiskerRight (F.mapHomotopyCategoryFactors (.up ℤ))
          DerivedCategory.Qh).app (Oc.obj P)).hom ≫
        ((Functor.isoWhiskerLeft Fc (DerivedCategory.quotientCompQhIso B)).app
          (Oc.obj P)).hom)
      exact IsIso.comp_isIso'
        ((Functor.isoWhiskerRight (DerivedCategory.quotientCompQhIso A).symm
          (derivedPullback f)).app (Oc.obj P)).isIso_hom
        (IsIso.comp_isIso' hε (IsIso.comp_isIso'
          ((Functor.isoWhiskerRight (F.mapHomotopyCategoryFactors (.up ℤ))
            DerivedCategory.Qh).app (Oc.obj P)).isIso_hom
          ((Functor.isoWhiskerLeft Fc (DerivedCategory.quotientCompQhIso B)).app
            (Oc.obj P)).isIso_hom))
    obtain ⟨η, hη⟩ : ∃ η :
        DerivedCategory.Q ⋙ O.mapDerivedCategory.{w, u + 1} ⋙ derivedPullback f ⟶
          Oc ⋙ Fc ⋙ DerivedCategory.Q,
        ∀ (P : CochainComplex
            (SheafOfModules.{u} ((moduleRings S.toRingedSpace).over U)) ℤ),
          Scheme.IsStrictlyPerfect S U P → IsIso (η.app P) := by
      refine ⟨(Functor.isoWhiskerRight O.mapDerivedCategoryFactors
        (derivedPullback f)).hom ≫ Functor.whiskerLeft Oc εc, ?_⟩
      intro P hP
      change IsIso
        (((Functor.isoWhiskerRight O.mapDerivedCategoryFactors
          (derivedPullback f)).app P).hom ≫ εc.app (Oc.obj P))
      exact IsIso.comp_isIso'
        ((Functor.isoWhiskerRight O.mapDerivedCategoryFactors
          (derivedPullback f)).app P).isIso_hom (hεc P hP)
    obtain ⟨τ, hτ⟩ : ∃ τ :
        DerivedCategory.Q ⋙ localizedResidueHomology S U x ⟶
          ((O ⋙ RingedSpace.moduleStalkFunctor U.toScheme.toRingedSpace x ⋙
            ModuleCat.extendScalars (IsLocalRing.residue
              (U.toScheme.presheaf.stalk x))).mapHomologicalComplex (.up ℤ)) ⋙ HM,
        ∀ (P : CochainComplex
            (SheafOfModules.{u} ((moduleRings S.toRingedSpace).over U)) ℤ),
          Scheme.IsStrictlyPerfect S U P → IsIso (τ.app P) := by
      refine ⟨Functor.whiskerRight η (H ⋙ Γ) ≫ z.hom, ?_⟩
      intro P hP
      have : IsIso (η.app P) := hη P hP
      change IsIso ((H ⋙ Γ).map (η.app P) ≫ (z.app P).hom)
      exact IsIso.comp_isIso' ((H ⋙ Γ).map_isIso (η.app P)) (z.app P).isIso_hom
    let t := fun P hP ↦ by
      have : IsIso (τ.app P) := hτ P hP
      exact (asIso (τ.app P)).symm
    refine ⟨t, ?_⟩
    intro P Q hP hQ α
    have : IsIso (τ.app P) := hτ P hP
    have : IsIso (τ.app Q) := hτ Q hQ
    dsimp only [t, Iso.symm_hom, asIso_inv]
    simpa only [Functor.comp_map, HM, HomologicalComplex.homologyFunctor_map] using
      inverse_naturality_of_isIso_app τ α

end AlgebraicGeometry
