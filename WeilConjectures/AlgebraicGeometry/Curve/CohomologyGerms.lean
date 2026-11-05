/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.StrictLocalCohomologyGerms
public import WeilConjectures.AlgebraicGeometry.Strict.Local.StrictLocalSectionCone
import WeilConjectures.AlgebraicGeometry.PointedEtaleSectionCone.PointedEtaleSectionConeStalkIso
import WeilConjectures.AlgebraicGeometry.StrictHenselizationFunctoriality
import WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMap
import WeilConjectures.AlgebraicGeometry.StrictHenselizationExtension
import WeilConjectures.Mathlib.RingTheory.Henselian
import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.FieldTheory.IsSepClosed
import WeilConjectures.AlgebraicGeometry.StrictHenselizationLocalStructure
import WeilConjectures.AlgebraicGeometry.Sites.StrictHenselizationLocal
import WeilConjectures.AlgebraicGeometry.StrictHenselizationPointedMap
import WeilConjectures.AlgebraicGeometry.StrictHenselizationPointEvaluationPointed
import WeilConjectures.AlgebraicGeometry.StrictHenselizationPointEvaluation
import WeilConjectures.AlgebraicGeometry.StrictHenselizationPointEvaluationProperties
import WeilConjectures.AlgebraicGeometry.StrictHenselizationPointEvaluationImage
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
import WeilConjectures.AlgebraicGeometry.StrictHenselizationPointEvaluationComparison
import WeilConjectures.AlgebraicGeometry.EtaleResidueTriples
import WeilConjectures.AlgebraicGeometry.EtaleLocalRingTriples
import WeilConjectures.RingTheory.StrictHenselizationTriples
import WeilConjectures.AlgebraicGeometry.EtalePointedMapRigidity
import WeilConjectures.AlgebraicGeometry.StrictHenselizationMapExists
import WeilConjectures.AlgebraicGeometry.StrictHenselizationRingResidue
import WeilConjectures.AlgebraicGeometry.StrictlyHenselianSectionsStalk

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

end AlgebraicGeometry.Etale
