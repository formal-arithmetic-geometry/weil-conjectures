/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Submission.WeilConjectures.AlgebraicGeometry.StrictLocalCohomologyGerms
public import Submission.WeilConjectures.AlgebraicGeometry.Strict.Local.StrictLocalSectionCone
import Submission.WeilConjectures.AlgebraicGeometry.PointedEtaleSectionCone.PointedEtaleSectionConeStalkIso
import Submission.WeilConjectures.AlgebraicGeometry.StrictHenselizationFunctoriality
import Submission.WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMap
import Submission.WeilConjectures.AlgebraicGeometry.StrictHenselizationExtension
import Submission.WeilConjectures.Mathlib.RingTheory.Henselian
import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.FieldTheory.IsSepClosed
import Submission.WeilConjectures.AlgebraicGeometry.StrictHenselizationLocalStructure
import Submission.WeilConjectures.AlgebraicGeometry.Sites.StrictHenselizationLocal
import Submission.WeilConjectures.AlgebraicGeometry.StrictHenselizationPointedMap
import Submission.WeilConjectures.AlgebraicGeometry.StrictHenselizationPointEvaluationPointed
import Submission.WeilConjectures.AlgebraicGeometry.StrictHenselizationPointEvaluation
import Submission.WeilConjectures.AlgebraicGeometry.StrictHenselizationPointEvaluationProperties
import Submission.WeilConjectures.AlgebraicGeometry.StrictHenselizationPointEvaluationImage
import Submission.WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
import Submission.WeilConjectures.AlgebraicGeometry.StrictHenselizationPointEvaluationComparison
import Submission.WeilConjectures.AlgebraicGeometry.EtaleResidueTriples
import Submission.WeilConjectures.AlgebraicGeometry.EtaleLocalRingTriples
import Submission.WeilConjectures.RingTheory.StrictHenselizationTriples
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Submission.WeilConjectures.AlgebraicGeometry.Sites.StrictHenselization
import Submission.WeilConjectures.AlgebraicGeometry.StrictHenselization
import Submission.WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMapExtension
import Submission.WeilConjectures.RingTheory.ProEtale.HenselianLocalRing
import Submission.WeilConjectures.AlgebraicGeometry.StrictHenselizationRingResidue
import Submission.WeilConjectures.AlgebraicGeometry.StrictlyHenselianSectionsStalk

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-! # Cohomology germs on the small coordinate-ring colimit model

The free sheaf, derived-sections presheaf, germ comparison and neighbourhood functor
are the adopted library's constructions. Only their source comparison and source legs
on `strictHenselizationScheme` are defined here. The adopted source comparison instead
has target on `strictLocalization`, so it cannot replace these maps definitionally.

Source: Stacks Project, Tags 03Q8, 03Q9 and 03QO.
-/

@[expose] public section

universe v
open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Etale

/-- The source isomorphism on the small coordinate-ring colimit model, using its unique germ
restriction and commutation of exact inverse image with homology.
Source: Stacks, Tags 03Q9 and 03QO
(blueprint: def-weil-pbc-small-model-cohomology-germs).

Construction: choose the uniquely specified restriction of `strictLocalSectionCone`.
The pointed residue identification supplies a compatible geometric lift to the closed point.
Global sections there compute the geometric stalk, so the general section-cone criterion
proves invertibility of this same restriction. Compose with the global-sections image of
the exact inverse-image/homology comparison. The restriction is uniquely determined;
no arbitrary witness or sheafification isomorphism supplies its data. -/
@[irreducible] noncomputable def smallModel_strictLocalCohomologySourceIso {S : Scheme.{v}}
    {Ω : Type v} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S)
    (L : DerivedCategory.Plus (Sheaf S.smallEtaleTopology AddCommGrpCat.{v + 1}))
    (n : ℤ) :
    (Scheme.pointSmallEtale s).sheafFiber.obj
        ((DerivedCategory.Plus.homologyFunctor _ n).obj L) ≅
      (Sheaf.Γ (Scheme.strictHenselizationScheme s).smallEtaleTopology
        AddCommGrpCat.{v + 1}).obj
        ((DerivedCategory.Plus.homologyFunctor _ n).obj
          ((upperStar AddCommGrpCat.{v + 1}
            (Scheme.strictHenselizationStructuralMap s)).mapDerivedCategoryPlus.obj L)) := by
  classical
  let G := (DerivedCategory.Plus.homologyFunctor _ n).obj L
  let r := Classical.choose ((strictLocalSectionCone s).existsUnique_restriction G)
  have hr := (Classical.choose_spec ((strictLocalSectionCone s).existsUnique_restriction G)).1
  letI : IsIso r := by
    let : Algebra (S.residueField (s (IsLocalRing.closedPoint Ω))) Ω :=
      (Scheme.descResidueField (Scheme.stalkClosedPointTo s)).hom.toAlgebra
    obtain ⟨hlocal, hstrict, _, _, σ, ⟨hpoint, hbase⟩, _⟩ :=
      strictHenselizationRingResidue s rfl
    let := hlocal
    let y := Spec.map (CommRingCat.ofHom
      (((IntermediateField.val
        (separableClosure (S.residueField (s (IsLocalRing.closedPoint Ω))) Ω)).toRingHom.comp
          σ.toRingHom).comp (IsLocalRing.residue (Scheme.strictHenselizationRing s))))
    have hy : y default = IsLocalRing.closedPoint (Scheme.strictHenselizationRing s) := by
      rw [Subsingleton.elim (default : Spec (.of Ω)) (IsLocalRing.closedPoint Ω)]
      change PrimeSpectrum.comap
        ((((IntermediateField.val
          (separableClosure (S.residueField (s (IsLocalRing.closedPoint Ω))) Ω)).toRingHom).comp
            σ.toRingHom).comp (IsLocalRing.residue (Scheme.strictHenselizationRing s)))
        (IsLocalRing.closedPoint Ω) = _
      rw [PrimeSpectrum.comap_comp]
      exact IsLocalRing.PrimeSpectrum.comap_residue _ _
    refine (strictLocalSectionCone s).isIso_restriction y hbase ?_
      G ((Scheme.strictlyHenselianSections_geometricStalk_isIso hstrict y hy).1 _) r hr
    intro i
    let n := (equivSmallModel.{v}
      (Scheme.strictHenselizationNeighbourhoods s)).inverse.obj i
    change y ≫ (strictLocalNeighbourhoodSection s i).left ≫
      pullback.fst ((Scheme.AffineEtale.Spec S).obj n.1).hom
        (Scheme.strictHenselizationStructuralMap s) = n.2.left
    dsimp only [n]
    simp only [strictLocalNeighbourhoodSection,
      MorphismProperty.Over.homMk, Over.homMk, CostructuredArrow.homMk, pullback.lift_fst]
    simpa only [Scheme.isoSpec_Spec_inv, Category.assoc] using hpoint i
  exact asIso r ≪≫
    (Sheaf.Γ (Scheme.strictHenselizationScheme s).smallEtaleTopology
      AddCommGrpCat.{v + 1}).mapIso
      ((Functor.mapDerivedCategoryPlusHomologyFunctorIso
        (upperStar AddCommGrpCat.{v + 1}
          (Scheme.strictHenselizationStructuralMap s)) n).app L)

/-- Canonical source legs: a presheaf germ, the canonical map to the cohomology-sheaf
stalk, and the unique strict-local germ restriction transported through exact inverse image.
Source: Stacks, Tags 03Q8 and 03Q9
(blueprint: def-weil-pbc-small-model-cohomology-germs).

Construction: use the adopted derived-sections presheaf and its canonical homology germ
map, followed by the source isomorphism for this small model. Naturality is the cocone
identity for presheaf germs on the pointed affine representative diagram. -/
noncomputable def smallModel_strictLocalCohomologySourceLegs {S : Scheme.{v}}
    {Ω : Type v} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S)
    (L : DerivedCategory.Plus (Sheaf S.smallEtaleTopology AddCommGrpCat.{v + 1}))
    (n : ℤ) :
    strictLocalCohomologyNeighbourhoodFunctor s L n ⟶
      (Functor.const _).obj
        ((Sheaf.Γ (Scheme.strictHenselizationScheme s).smallEtaleTopology
          AddCommGrpCat.{v + 1}).obj
          ((DerivedCategory.Plus.homologyFunctor _ n).obj
            ((upperStar AddCommGrpCat.{v + 1}
              (Scheme.strictHenselizationStructuralMap s)).mapDerivedCategoryPlus.obj L))) where
  app i :=
    (Scheme.pointSmallEtale s).toPresheafFiber
      ((strictLocalNeighbourhoods s).obj i.unop)
      ((equivSmallModel.{v} (Scheme.strictHenselizationNeighbourhoods s)).inverse.obj
        i.unop).2 (strictLocalCohomologyPresheaf L n) ≫
      (Scheme.pointSmallEtale s).presheafFiber.map (strictLocalCohomologyGermMap L n) ≫
        (smallModel_strictLocalCohomologySourceIso s L n).hom
  naturality i j a := by
    dsimp [strictLocalCohomologyNeighbourhoodFunctor]
    simp only [Category.comp_id, ← Category.assoc]
    congr 1
    congr 1
    let N := (equivSmallModel.{v} (Scheme.strictHenselizationNeighbourhoods s)).inverse ⋙
      Scheme.strictHenselizationAffineInclusion s ⋙ ObjectProperty.ι
        (fun q : (Scheme.pointSmallEtale s).fiber.Elements ↦ IsAffine q.1.left)
    exact (Scheme.pointSmallEtale s).presheafFiberCocone
      (strictLocalCohomologyPresheaf L n) |>.w (N.map a.unop).op

end AlgebraicGeometry.Etale
