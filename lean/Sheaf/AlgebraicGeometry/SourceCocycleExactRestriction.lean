/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V3
-/
module

public import Sheaf.AlgebraicGeometry.SourceLocalizedCocycleHomology

/-! # Restriction of a cocycle through exact strict-local functors

Source: Stacks Project, Tags 03Q9 and 03QO, restriction and exact global sections.
-/

@[expose] public section

universe v
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry CochainComplex CochainComplex.HomComplex

namespace AlgebraicGeometry.Etale

set_option backward.isDefEq.respectTransparency false in
/-- A natural transformation from neighbourhood sections to exact strict-local sections
sends the sections cohomology class of a cocycle to the restriction of its homology section.
No K-injectivity or localization bijectivity is needed for this assertion.

Source: Stacks Project, Tags 03Q9 and 03QO, the restriction of an injective complex
and commutation of exact inverse image and strict-local sections with homology.
(blueprint: lem-weil-pbc-source-cocycle-exact-restriction).

Proof: evaluate the single-source cocycle degreewise using sourceFreeSectionsComplexIso.
Its class in the sections complex is the image of the Hom-complex class under the
homology functor. Apply the natural transformation degreewise. Its naturality with
respect to the cycle inclusion and homology projection identifies the restricted
cycle with the image of the homology section. Exact inverse image and strict-local
global sections preserve kernels and cokernels, hence identify this projection with
the homology projection of the mapped complex. The quotient localization factorization
is natural in the complex map; cancel its inverse with the homology factorization.
The exact-functor homology comparisons are natural in r inverse, so transport along
r gives precisely the displayed composite. Boundaries map to boundaries; thus the
calculation descends to cohomology. Zero cycles and all integer degrees obey the same
calculation. The transformation is arbitrary, so no stalk comparison is used. -/
theorem sourceCocycleExactRestriction {S : Scheme.{v}}
    {Ω : Type v} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S)
    (K : DerivedCategory.Plus (Sheaf S.smallEtaleTopology AddCommGrpCat.{v + 1}))
    (L : CochainComplex (Sheaf S.smallEtaleTopology AddCommGrpCat.{v + 1}) ℤ)
    (r : K.obj ≅ DerivedCategory.Q.obj L) (n : ℤ) (W : S.Etale)
    (τ : (sheafSections S.smallEtaleTopology AddCommGrpCat.{v + 1}).obj (op W) ⟶
      upperStar AddCommGrpCat.{v + 1} (Scheme.strictHenselizationStructuralMap s) ⋙
        Sheaf.Γ (Scheme.strictHenselizationScheme s).smallEtaleTopology
          AddCommGrpCat.{v + 1})
    (f : (strictLocalFreeSheaf S.smallEtaleTopology).obj W ⟶ L.X n)
    (hf : f ≫ L.d n (n + 1) = 0) :
    let U := upperStar AddCommGrpCat.{v + 1} (Scheme.strictHenselizationStructuralMap s)
    let G := Sheaf.Γ (Scheme.strictHenselizationScheme s).smallEtaleTopology
      AddCommGrpCat.{v + 1}
    letI := strictHenselization_globalSections_preservesFiniteColimits s
    let c := CohomologyClass.mk (Cocycle.fromSingleMk f (zero_add n) (n + 1) rfl hf)
    let C := (U.mapHomologicalComplex (.up ℤ)).obj L
    let a := (NatTrans.mapHomologicalComplex τ (.up ℤ)).app L
    let x := ((HomologicalComplex.homologyFunctor AddCommGrpCat.{v + 1} (.up ℤ) n).map
      (sourceFreeSectionsComplexIso W L).hom)
        ((leftHomologyData
          ((CochainComplex.singleFunctor _ 0).obj
            ((strictLocalFreeSheaf S.smallEtaleTopology).obj W)) L n).homologyIso.inv c)
    (((DerivedCategory.homologyFunctorFactors AddCommGrpCat.{v + 1} n).inv.app _ ≫
      (DerivedCategory.homologyFunctor AddCommGrpCat.{v + 1} n).map
        (DerivedCategory.Q.map a ≫ G.mapDerivedCategoryFactors.inv.app C ≫
          G.mapDerivedCategory.map
            (U.mapDerivedCategoryFactors.inv.app L ≫ U.mapDerivedCategory.map r.inv)) ≫
      (G.mapDerivedCategoryHomologyFunctorIso n).inv.app (U.mapDerivedCategory.obj K.obj))
        x : G.obj ((DerivedCategory.Plus.homologyFunctor _ n).obj
          (U.mapDerivedCategoryPlus.obj K))) =
      (G.map ((U.mapDerivedCategoryPlusHomologyFunctorIso n).hom.app K))
        (τ.app ((DerivedCategory.Plus.homologyFunctor _ n).obj K)
          (sourceCocycleHomologySection K L r n W f hf)) := by sorry

end AlgebraicGeometry.Etale
