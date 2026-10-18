/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Proetale.Basic
public import WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.Affine
public import Sheaf.AlgebraicGeometry.EtaleComparison
public import Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory
public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.ChangeOfRings
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence

import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
import Mathlib.Algebra.Category.CommAlgCat.Basic
import Mathlib.AlgebraicGeometry.Morphisms.RingHomProperties
import Mathlib.AlgebraicGeometry.GammaSpecAdjunction

/-! # Continuity maps and classical pro-étale sheaves

Source: current blueprint, sec-proetale-coefficients/sk-def-pe-classical-definition,
`sk-def-pe-classical-definition-continuity-map.md`, clauses 1--4 and final paragraph
(blueprint: det-pe-classical-definition-continuity-map).

The index categories and section values live in the common larger universe `u + 1`.
Module coefficients use the intrinsic constant-ring module category of the recorded
small pro-étale site, with the same coefficient lift as `Scheme.proEtaleDerivedCategory`.
-/

@[expose] public section

set_option autoImplicit false

universe u vC uC

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProEtale

/-- An affine étale presentation with an affine vertex in the pro-étale site.
The universal property is taken in all schemes over `X`, not just in the site.
Source: current blueprint, continuity-map detail, clause 1
(blueprint: det-pe-classical-definition-continuity-map). -/
structure AffinePresentation (X : Scheme.{u}) (I : Type (u + 1))
    [SmallCategory I] [IsCofiltered I] where
  diagram : I ⥤ X.ProEt
  affine : ∀ i : I, IsAffine (diagram.obj i).left
  etale : ∀ i : I, Etale (diagram.obj i).hom
  cone : Cone diagram
  affineVertex : IsAffine cone.pt.left
  isLimit : IsLimit ((Scheme.ProEt.forget X).mapCone cone)

/-- Restriction of a presheaf to the stages of a presentation, contravariantly.
Source: current blueprint, continuity-map detail, clause 2
(blueprint: det-pe-classical-definition-continuity-map). -/
def sectionDiagram {X : Scheme.{u}} {I : Type (u + 1)} [SmallCategory I]
    [IsCofiltered I] (P : AffinePresentation X I)
    {C : Type uC} [Category.{vC} C] (F : X.ProEtᵒᵖ ⥤ C) : Iᵒᵖ ⥤ C :=
  P.diagram.op ⋙ F

/-- The restriction cocone, obtained functorially from the projection cone.
Source: current blueprint, continuity-map detail, clause 2
(blueprint: det-pe-classical-definition-continuity-map). -/
def sectionCocone {X : Scheme.{u}} {I : Type (u + 1)} [SmallCategory I]
    [IsCofiltered I] (P : AffinePresentation X I)
    {C : Type uC} [Category.{vC} C] (F : X.ProEtᵒᵖ ⥤ C) :
    Cocone (sectionDiagram P F) :=
  F.mapCocone P.cone.op

/-- The canonical map out of the chosen colimit, retaining the presentation.
Source: current blueprint, continuity-map detail, clause 2; Stacks, Categories, Tag 002F
(blueprint: det-pe-classical-definition-continuity-map). -/
noncomputable def continuityMap {X : Scheme.{u}} {I : Type (u + 1)} [SmallCategory I]
    [IsCofiltered I] (P : AffinePresentation X I)
    {C : Type uC} [Category.{vC} C] (F : X.ProEtᵒᵖ ⥤ C)
    [HasColimit (sectionDiagram P F)] :
    colimit (sectionDiagram P F) ⟶ F.obj (op P.cone.pt) :=
  colimit.desc (sectionDiagram P F) (sectionCocone P F)

/-- The displayed formula on representatives of the colimit.
Source: current blueprint, continuity-map detail, clause 2
(blueprint: det-pe-classical-definition-continuity-map).
Proof: the defining factorization equation of `colimit.desc`, applied to the restriction
cocone, gives the projection restriction on each summand. -/
theorem continuityMap_ι {X : Scheme.{u}} {I : Type (u + 1)} [SmallCategory I]
    [IsCofiltered I] (P : AffinePresentation X I)
    {C : Type uC} [Category.{vC} C] (F : X.ProEtᵒᵖ ⥤ C)
    [HasColimit (sectionDiagram P F)] (i : I) :
    colimit.ι (sectionDiagram P F) (op i) ≫ continuityMap P F =
      F.map (P.cone.π.app i).op := by
  sorry

/-- Naturality of the continuity map in the sheaf (in fact in any presheaf).
Source: current blueprint, continuity-map detail, clause 2
(blueprint: det-pe-classical-definition-continuity-map).
Proof: precompose with every coprojection. Both composites become the restriction map
along `u_i` followed by the component of the sheaf morphism. They agree by naturality;
the colimit universal property gives equality. -/
theorem continuityMap_natural {X : Scheme.{u}} {I : Type (u + 1)} [SmallCategory I]
    [IsCofiltered I] (P : AffinePresentation X I)
    {C : Type uC} [Category.{vC} C] {F G : X.ProEtᵒᵖ ⥤ C} (α : F ⟶ G)
    [HasColimit (sectionDiagram P F)] [HasColimit (sectionDiagram P G)] :
    colimMap (G := sectionDiagram P F) (F := sectionDiagram P G)
      (Functor.whiskerLeft P.diagram.op α) ≫ continuityMap P G =
      continuityMap P F ≫ α.app (op P.cone.pt) := by
  sorry

/-- A set sheaf is classical when every affine presentation gives a bijective map.
Source: current blueprint, continuity-map detail, clause 3
(blueprint: det-pe-classical-definition-continuity-map). -/
def IsClassical {X : Scheme.{u}}
    (F : Sheaf (Scheme.ProEt.topology X) (Type (u + 1))) : Prop :=
  ∀ {I : Type (u + 1)} [SmallCategory I] [IsCofiltered I]
    (P : AffinePresentation X I), Function.Bijective (continuityMap P F.obj)

/-- Set-sheaf classicality is invariant under isomorphism.
Source: current blueprint, continuity-map proof, third paragraph
(blueprint: det-pe-classical-definition-continuity-map).
Proof: naturality identifies the continuity maps through the component bijections of
an isomorphism and the colimit isomorphism induced by its stage components. Apply the
same construction to its inverse to see that these identifications are bijective. -/
theorem isClassical_iso_iff {X : Scheme.{u}}
    {F G : Sheaf (Scheme.ProEt.topology X) (Type (u + 1))} (e : F ≅ G) :
    IsClassical F ↔ IsClassical G := by
  sorry

section Modules

variable {X : Scheme.{u}} (Λ : Type u) [CommRing Λ]

variable (F : ringedSiteModules.{u + 1}
  ((sheafCompose (Scheme.ProEt.topology X)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
      ((constantSheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}).obj
        (CommRingCat.of (ULift.{u + 1, u} Λ)))))

/-- Sections with scalars restricted along the constant-section sheafification unit.
This is a presheaf of modules over the lifted discrete coefficient ring itself.
Source: current blueprint, continuity-map detail, clause 3
(blueprint: det-pe-classical-definition-continuity-map). -/
noncomputable def moduleSectionPresheaf : X.ProEtᵒᵖ ⥤ ModuleCat.{u + 1} (ULift.{u + 1, u} Λ) := by
  let M := PresheafOfModules.restrictScalarsObj F.val
    (Functor.whiskerRight
      (toSheafify (Scheme.ProEt.topology X)
        ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1, u} Λ))))
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}))
  exact
    { obj := M.obj
      map f := M.map f
      map_id U := by ext x; exact congrArg (fun g ↦ g x) (M.map_id U)
      map_comp f g := by ext x; exact congrArg (fun h ↦ h x) (M.map_comp f g) }

/-- The linear continuity map, taking the colimit in coefficient modules.
Its scalar action is restriction along the canonical constant-section maps.
Source: current blueprint, continuity-map detail, clause 3
(blueprint: det-pe-classical-definition-continuity-map). -/
noncomputable def moduleContinuityMap {I : Type (u + 1)} [SmallCategory I]
    [IsCofiltered I] (P : AffinePresentation X I) :
    colimit (sectionDiagram P (moduleSectionPresheaf Λ F)) ⟶
      (moduleSectionPresheaf Λ F).obj (op P.cone.pt) :=
  continuityMap P (moduleSectionPresheaf Λ F)

/-- Classicality of intrinsic constant-ring module sheaves.
Source: current blueprint, continuity-map detail, clause 3
(blueprint: det-pe-classical-definition-continuity-map). -/
def IsClassicalModule : Prop :=
  ∀ {I : Type (u + 1)} [SmallCategory I] [IsCofiltered I]
    (P : AffinePresentation X I), IsIso (moduleContinuityMap Λ F P)

/-- Module classicality agrees with classicality of the underlying set sheaf.
Source: current blueprint, continuity-map detail, clause 3
(blueprint: det-pe-classical-definition-continuity-map).
Proof: filtered module colimits have the corresponding set colimits as underlying sets:
every element comes from a stage and equality is witnessed at a common later stage.
Under this comparison the two continuity maps agree on every coprojection. A linear
map is invertible precisely when its underlying function is bijective. -/
theorem isClassicalModule_iff :
    IsClassicalModule Λ F ↔
      IsClassical ((sheafCompose (Scheme.ProEt.topology X)
        (forget AddCommGrpCat.{u + 1})).obj ((SheafOfModules.toSheaf _).obj F)) := by
  sorry

end Modules

/-- Classical cochain complexes have classical cohomology module sheaves in every degree.
Source: current blueprint, continuity-map detail, clause 4
(blueprint: det-pe-classical-definition-continuity-map). -/
def IsClassicalCochainComplex {X : Scheme.{u}} (Λ : Type u) [CommRing Λ]
    (K : CochainComplex
      (ringedSiteModules.{u + 1}
        ((sheafCompose (Scheme.ProEt.topology X)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
            ((constantSheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}).obj
              (CommRingCat.of (ULift.{u + 1, u} Λ))))) ℤ) : Prop :=
  ∀ q : ℤ, IsClassicalModule Λ (K.homology q)

/-- Classicality of the recorded intrinsic derived category, using its cohomology sheaves.
Source: current blueprint, continuity-map detail, clause 4
(blueprint: det-pe-classical-definition-continuity-map). -/
def IsClassicalComplex {X : Scheme.{u}} (Λ : Type u) [CommRing Λ]
    (K : Scheme.proEtaleDerivedCategory X Λ) : Prop :=
  ∀ q : ℤ, IsClassicalModule Λ
    ((@DerivedCategory.homologyFunctor _ _ _ (HasDerivedCategory.standard _) q).obj K)

/-- The cochain and derived formulations agree under the recorded localization functor.
Source: current blueprint, continuity-map detail, clause 4; Stacks, Tag 05RT
(blueprint: det-pe-classical-definition-continuity-map).
Proof: `DerivedCategory.homologyFunctorFactors` identifies each cohomology sheaf of
`Q.obj K` with the corresponding cochain cohomology sheaf. Apply the underlying-set
comparison and isomorphism invariance to each degree; the resulting equivalences give
the equivalence of the predicates quantified over all integers. -/
theorem isClassicalComplex_Q_iff {X : Scheme.{u}} (Λ : Type u) [CommRing Λ]
    (K : CochainComplex
      (ringedSiteModules.{u + 1}
        ((sheafCompose (Scheme.ProEt.topology X)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
            ((constantSheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}).obj
              (CommRingCat.of (ULift.{u + 1, u} Λ))))) ℤ) :
    IsClassicalComplex Λ
      ((@DerivedCategory.Q _ _ _ (HasDerivedCategory.standard _)).obj K) ↔
        IsClassicalCochainComplex Λ K := by
  sorry

/-- Classicality depends only on the derived isomorphism class.
Source: current blueprint, continuity-map detail, clause 4
(blueprint: det-pe-classical-definition-continuity-map).
Proof: apply each cohomology functor to the given isomorphism. Its components and inverse
identify the restriction diagrams and continuity cocones. The induced colimit maps are
inverse linear isomorphisms, so invertibility of each continuity map is preserved. -/
theorem isClassicalComplex_iso_iff {X : Scheme.{u}} (Λ : Type u) [CommRing Λ]
    {K L : Scheme.proEtaleDerivedCategory X Λ} (e : K ≅ L) :
    IsClassicalComplex Λ K ↔ IsClassicalComplex Λ L := by
  sorry

/-- Presentable affine site objects are exactly the affine ind-étale subsite objects.
Source: current blueprint, continuity-map detail, final paragraph; recorded
`proAffineEtale_Spec_iff` and `Scheme.AffineProEt`
(blueprint: det-pe-classical-definition-continuity-map).
Proof, following steps 7--9 of the node:
1. Write `X = Spec R` and each affine stage as `Spec B_i`, using
   `def-weil-affine-spectrum`. The structure and transition maps give a filtered
   diagram of `R`-algebras. By `lem-weil-pbc-etale-ring-map-iff-etale-affine`, its
   terms are finitely presented étale algebras.
2. Form the ring colimit B by `lem-weil-pbc-commutative-algebras-colimits-exist`.
   Filteredness and nonemptiness make the maps `R → B_i → B` equal, defining `R → B`.
   The universal ring-colimit map to any algebra cocone respects this structure map,
   so B is also the algebra colimit. By `lem-weil-pbc-spec-small-colimit-limit`,
   `Spec B` is the scheme limit. Its factorization maps are over X, as can be checked
   after any projection. Uniqueness of the limit over X identifies its vertex with U.
3. Thus B is ind-étale by `def-weil-pbc-ind-etale-algebra`. To use the recorded
   universe-u presentation, replace the larger diagram by the small category of
   finitely presented étale R-algebras mapping to B: finite presentations and maps
   into the universe-u ring B give a universe-u skeleton, and the original filtered
   presentation makes this category filtered with colimit B. Conversely the recorded
   ind-étale presentation gives affine étale stages and a limit by the same Spec
   argument; lift its index category into `u + 1`. The definition of
   `Scheme.AffineProEt` is precisely `proAffineEtale` of its structure map. -/
theorem affinePresentation_iff {X : Scheme.{u}} [IsAffine X] (U : X.ProEt) :
    (∃ (I : Type (u + 1)) (_ : SmallCategory I) (_ : IsCofiltered I)
      (P : AffinePresentation X I), Nonempty (P.cone.pt ≅ U)) ↔ proAffineEtale U.hom := by
  sorry

end AlgebraicGeometry.ProEtale
