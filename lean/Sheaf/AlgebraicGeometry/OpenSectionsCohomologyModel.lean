/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H1
-/
module

public import Sheaf.AlgebraicGeometry.PrincipalOpenCechTotal
public import Sheaf.AlgebraicGeometry.DerivedCategory
public import Sheaf.Topology.RingedSpaceModuleCohomology
public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import Sheaf.Algebra.Homology.OpenRestrictionAdjunctionExact

/-! # Ordinary representatives for the open-sections comparison

Source: Stacks Project, Tags 08BS and 079V.
-/

@[expose] public section

universe u w v
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry
noncomputable section
attribute [local instance] Functor.additive_of_preserves_binary_products
  comp_preservesFiniteLimits comp_preservesFiniteColimits
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Restriction to the open subscheme, through the over-site equivalence. -/
abbrev openComparisonRestriction (A : Type u) [CommRing A] (U : (Spec (.of A)).Opens) :=
  (SheafOfModules.overFunctor.{u} (moduleRings (Spec (.of A)).toRingedSpace) U) ⋙
    Equivalence.functor
      (C := SheafOfModules.{u} ((moduleRings (Spec (.of A)).toRingedSpace).over U))
      (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
      (Scheme.Modules.overEquiv U)

/-- Ordinary global sections on the restriction are ordinary sections on the open.
The map is restrictAppIso at the top open composed with overFunctorEquiv. -/
def openComparisonSectionsIso (A : Type u) [CommRing A] (U : (Spec (.of A)).Opens) :
    openComparisonRestriction A U ⋙
        RingedSpace.globalSectionsFunctor U.toScheme.toRingedSpace ⋙
          forget₂ (ModuleCat.{u}
            ((moduleRings U.toScheme.toRingedSpace).obj.obj (op ⊤))) AddCommGrpCat ≅
      affineOpenSections A U ⋙ forget₂ (ModuleCat.{u} A) AddCommGrpCat := by
  let S := RingedSpace.globalSectionsFunctor U.toScheme.toRingedSpace ⋙
    forget₂ (ModuleCat.{u}
      ((moduleRings U.toScheme.toRingedSpace).obj.obj (op ⊤))) AddCommGrpCat
  refine Functor.isoWhiskerRight (Scheme.Modules.overFunctorEquiv U) S ≪≫ ?_
  refine NatIso.ofComponents (fun M ↦ ?_) ?_
  · change Γ(Scheme.Modules.restrict M U.ι, ⊤) ≅ Γ(M, U)
    exact (Scheme.Modules.restrictAppIso U.ι M ⊤) ≪≫
      ((Scheme.Modules.toPresheaf (Spec (.of A))).obj M).mapIso
        (eqToIso (by simp : U = U.ι ''ᵁ ⊤)).op
  · intro M N g
    change ((Scheme.Modules.toPresheaf (Spec (.of A))).map g).app
        (op (U.ι ''ᵁ ⊤)) ≫
          ((Scheme.Modules.toPresheaf (Spec (.of A))).obj N).map
            (eqToHom (by simp : U = U.ι ''ᵁ ⊤)).op =
      ((Scheme.Modules.toPresheaf (Spec (.of A))).obj M).map
          (eqToHom (by simp : U = U.ι ''ᵁ ⊤)).op ≫
        ((Scheme.Modules.toPresheaf (Spec (.of A))).map g).app (op U)
    exact ((Scheme.Modules.toPresheaf (Spec (.of A))).map g).naturality _ |>.symm

variable (A : Type u) [CommRing A] (U : (Spec (.of A)).Opens)
  [HasDerivedCategory.{w}
    (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))]
  [∀ V : (Spec (.of A)).Opens, HasDerivedCategory.{w}
    (SheafOfModules.{u} ((moduleRings (Spec (.of A)).toRingedSpace).over V))]
  [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))]
  [HasDerivedCategory.{v} (ModuleCat.{u} A)]

/-- Zeroth derived global sections on the open, with its scalars forgotten. -/
def openComparisonGlobalCohomology :
    schemeDerivedCategory U.toScheme ⥤ AddCommGrpCat.{u} := by
  letI := HasDerivedCategory.standard
    (ModuleCat.{u} ((moduleRings U.toScheme.toRingedSpace).obj.obj (op ⊤)))
  exact (RingedSpace.globalSectionsFunctor U.toScheme.toRingedSpace).rightDerivedFunctor ⋙
    DerivedCategory.homologyFunctor
      (ModuleCat.{u} ((moduleRings U.toScheme.toRingedSpace).obj.obj (op ⊤))) 0 ⋙
    forget₂ (ModuleCat.{u}
      ((moduleRings U.toScheme.toRingedSpace).obj.obj (op ⊤))) AddCommGrpCat

/-- Zeroth derived sections on the ambient affine scheme, with scalars forgotten. -/
def openComparisonAmbientCohomology : schemeDerivedCategory (Spec (.of A)) ⥤
    AddCommGrpCat.{u} :=
  (affineOpenSections A U).rightDerivedFunctor ⋙
    DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0 ⋙
    forget₂ (ModuleCat.{u} A) AddCommGrpCat

/-- The ordinary-to-derived comparison on complexes, with quotient comparisons inserted. -/
def openComparisonComplexUnit
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    [CategoryTheory.Abelian.HasKInjectiveResolutions C] (T : C ⥤ D) [T.Additive] :
    T.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ T.rightDerivedFunctor :=
  (Functor.isoWhiskerLeft (T.mapHomologicalComplex (.up ℤ))
    (DerivedCategory.quotientCompQhIso D)).inv ≫
  Functor.whiskerLeft (HomotopyCategory.quotient C (.up ℤ)) T.rightDerivedFunctorUnit ≫
  (Functor.isoWhiskerRight (DerivedCategory.quotientCompQhIso C) T.rightDerivedFunctor).hom

/-- Ordinary cohomology of ambient open sections, viewed as an additive group. -/
def openComparisonOrdinaryCohomology
    (K : CochainComplex
      (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace)) ℤ) :
    AddCommGrpCat.{u} :=
  (forget₂ (ModuleCat.{u} A) AddCommGrpCat).obj
    ((((affineOpenSections A U).mapHomologicalComplex (.up ℤ)).obj K).homology 0)

/-- The ambient ordinary-to-derived cohomology map. -/
def openComparisonAmbientUnit
    (K : CochainComplex
      (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace)) ℤ) :
    openComparisonOrdinaryCohomology A U K ⟶
      (openComparisonAmbientCohomology A U).obj (DerivedCategory.Q.obj K) :=
  (forget₂ (ModuleCat.{u} A) AddCommGrpCat).map
    (((DerivedCategory.homologyFunctorFactors (ModuleCat.{u} A) 0).app
      (((affineOpenSections A U).mapHomologicalComplex (.up ℤ)).obj K)).inv ≫
      (DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).map
        ((openComparisonComplexUnit (affineOpenSections A U)).app K))

/-- The sections isomorphism on ordinary cohomology, using exact scalar forgetting. -/
def openComparisonOrdinaryIso
    (K : CochainComplex
      (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace)) ℤ) :
    let J := ((openComparisonRestriction A U).mapHomologicalComplex (.up ℤ)).obj K
    let B := (moduleRings U.toScheme.toRingedSpace).obj.obj (op ⊤)
    (forget₂ (ModuleCat.{u} B) AddCommGrpCat).obj
        ((((RingedSpace.globalSectionsFunctor U.toScheme.toRingedSpace).mapHomologicalComplex
          (.up ℤ)).obj J).homology 0) ≅
      openComparisonOrdinaryCohomology A U K := by
  let J := ((openComparisonRestriction A U).mapHomologicalComplex (.up ℤ)).obj K
  let B := (moduleRings U.toScheme.toRingedSpace).obj.obj (op ⊤)
  let S := ((RingedSpace.globalSectionsFunctor U.toScheme.toRingedSpace).mapHomologicalComplex
    (.up ℤ)).obj J
  let T := ((affineOpenSections A U).mapHomologicalComplex (.up ℤ)).obj K
  let P := forget₂ (ModuleCat.{u} B) AddCommGrpCat
  let Q := forget₂ (ModuleCat.{u} A) AddCommGrpCat
  let e : (P.mapHomologicalComplex (.up ℤ)).obj S ≅
      (Q.mapHomologicalComplex (.up ℤ)).obj T :=
    (NatIso.mapHomologicalComplex (openComparisonSectionsIso A U) (.up ℤ)).app K
  exact ((S.sc 0).mapHomologyIso P).symm ≪≫
    (HomologicalComplex.homologyFunctor AddCommGrpCat (.up ℤ) 0).mapIso e ≪≫
    (T.sc 0).mapHomologyIso Q

/-- The same ordinary class mapped to derived sections of the restricted complex. -/
def openComparisonRestrictedUnit
    (K : CochainComplex
      (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace)) ℤ) :
    openComparisonOrdinaryCohomology A U K ⟶
      (openComparisonGlobalCohomology A U).obj
        ((openComparisonRestriction A U).mapDerivedCategory.obj (DerivedCategory.Q.obj K)) := by
  let B := (moduleRings U.toScheme.toRingedSpace).obj.obj (op ⊤)
  letI := HasDerivedCategory.standard (ModuleCat.{u} B)
  let T := openComparisonRestriction A U
  let S := RingedSpace.globalSectionsFunctor U.toScheme.toRingedSpace
  let J := (T.mapHomologicalComplex (.up ℤ)).obj K
  let V := (S.mapHomologicalComplex (.up ℤ)).obj J
  let H := DerivedCategory.homologyFunctor (ModuleCat.{u} B) 0
  let P := forget₂ (ModuleCat.{u} B) AddCommGrpCat
  exact (openComparisonOrdinaryIso A U K).inv ≫
    P.map (((DerivedCategory.homologyFunctorFactors (ModuleCat.{u} B) 0).app V).inv ≫
      H.map ((openComparisonComplexUnit S).app J)) ≫
    (openComparisonGlobalCohomology A U).map (T.mapDerivedCategoryFactors.inv.app K)

/-- The open-sections comparison is normalized on every ordinary complex class.
Source: Stacks Project, Tags 08BS and 079V.
(blueprint: lem-sc-open-sections-cohomology-model-comparison).

Proof: Let T be restriction through the over-equivalence. Extension by zero is an exact
left adjoint of over-restriction, so the adjunction criterion for preservation of
K-injectives applies. The over-equivalence also preserves K-injectives. Thus T sends
K-injectives to K-injectives. On a K-injective representative J the ordinary-to-derived
units for ambient sections and for global sections on T(J) are isomorphisms.
The exact scalar-forgetting functors commute with homology. Conjugate the ordinary
sections isomorphism openComparisonOrdinaryIso by these two units and by the exact
restriction factorization to obtain the comparison at Q(J). Naturality of all four
maps proves naturality for homotopy classes of chain maps. Localization is fully
faithful on K-injectives, and every derived object has such a representative, so this
comparison descends to a natural isomorphism on the specified ambient derived category.
For an arbitrary complex K choose a quasi-isomorphism K to J. Naturality of both units
and of the sections and homology comparisons proves the displayed square after mapping
to J. Since the induced derived map is invertible, cancel it to obtain the square on K.
No quasi-coherence or boundedness is required; an empty open and the zero ring give
zero groups with the same comparison. The two module-derived categories may have
different universe choices: all conjugations occur through their own units and Q.
-/
theorem exists_openComparison_cohomology_model_iso :
    ∃ e : (openComparisonRestriction A U).mapDerivedCategory ⋙
        openComparisonGlobalCohomology A U ≅ openComparisonAmbientCohomology A U,
      ∀ (K : CochainComplex
        (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace)) ℤ),
        openComparisonRestrictedUnit A U K ≫ e.hom.app (DerivedCategory.Q.obj K) =
          openComparisonAmbientUnit A U K := by sorry

end
end AlgebraicGeometry
