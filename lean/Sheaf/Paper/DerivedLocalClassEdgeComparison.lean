/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q58
-/
module

public import Sheaf.Paper.PurityFiniteSetting
public import Sheaf.AlgebraicGeometry.ProEtaleFiniteModules
public import Sheaf.AlgebraicGeometry.BoundedBelowProEtaleComparison
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafOver
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import WeilConjectures.CategoryTheory.RingedSiteGrothendieckAbelian
import Sheaf.AlgebraicGeometry.InjectiveComplexSliceSectionModel
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import WeilConjectures.Mathlib.CategoryTheory.Preadditive.Injective.Preserves

/-!
# Derived local-class edges and site comparison

Source: Stacks Project, sites-cohomology.tex, Tags 0BKV and 0D6I, and the comparison
unit of sk-prop-sf-comparison (blueprint: lem-pur-derived-local-class-edge-comparison).
-/

@[expose] public section

set_option autoImplicit false

universe u vC vD uC uD wC wD

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite AlgebraicGeometry

namespace CategoryTheory

/-- The canonical cohomology edge of an exact-left-adjoint adjunction: transpose the
cohomology of its derived counit, using the exact-functor cohomology identification.
For sheafification this is the local-class presheaf map; for the constant sheaf
adjunction it is the global local-class edge. Source: Stacks 0BKV, cycle quotient
(blueprint: lem-pur-derived-local-class-edge-comparison). -/
noncomputable def derivedLocalClassMate
    {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
    [Abelian C] [Abelian D] [HasDerivedCategory.{wC} C] [HasDerivedCategory.{wD} D]
    [HasKInjectiveResolutions D] {L : C ⥤ D} {R : D ⥤ C}
    [L.Additive] [R.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    (adj : L ⊣ R) (V : DerivedCategory D) (r : ℤ) :
    (DerivedCategory.homologyFunctor C r).obj (R.rightDerivedFunctor.obj V) ⟶
      R.obj ((DerivedCategory.homologyFunctor D r).obj V) :=
  adj.homEquiv _ _
    ((L.mapDerivedCategoryHomologyFunctorIso r).hom.app (R.rightDerivedFunctor.obj V) ≫
      (DerivedCategory.homologyFunctor D r).map
        (adj.mapDerivedCategoryRightDerivedAdjunction.counit.app V))

end CategoryTheory

namespace CategoryTheory

/-- The standard localization for module-valued presheaves. Its larger morphism universe
is allowed: it does not identify the object and morphism universes of the site.
Source: Stacks 0BKV, its presheaf construction
(blueprint: lem-pur-derived-local-class-edge-comparison). -/
noncomputable instance localClassPresheavesHasDerivedCategory
    {C : Type (u + 1)} [Category.{u} C] (Λ : Type (u + 1)) [CommRing Λ] :
    HasDerivedCategory.{u + 2} (Cᵒᵖ ⥤ ModuleCat.{u + 1} Λ) :=
  HasDerivedCategory.standard _

section Site

variable {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
    (J : GrothendieckTopology C) (Λ : Type (u + 1)) [CommRing Λ]

/-- Derived sections as a presheaf, by deriving the underlying-presheaf functor.
Evaluation is exact, so its degree-r cohomology at W is H^r(W,V).
Source: Stacks 0BKV (blueprint: lem-pur-derived-local-class-edge-comparison). -/
noncomputable def derivedLocalCohomologyPresheaf
    (V : DerivedCategory (Sheaf J (ModuleCat.{u + 1} Λ))) (r : ℤ) :
    Cᵒᵖ ⥤ ModuleCat.{u + 1} Λ :=
  (DerivedCategory.homologyFunctor (Cᵒᵖ ⥤ ModuleCat.{u + 1} Λ) r).obj
    ((sheafToPresheaf J (ModuleCat.{u + 1} Λ)).rightDerivedFunctor.obj V)

/-- The canonical sheafification-to-cohomology map, given by the derived counit.
Source: Stacks 0BKV (blueprint: lem-pur-derived-local-class-edge-comparison). -/
noncomputable def derivedLocalClassSheafification
    (V : DerivedCategory (Sheaf J (ModuleCat.{u + 1} Λ))) (r : ℤ) :
    (presheafToSheaf J (ModuleCat.{u + 1} Λ)).obj
        (derivedLocalCohomologyPresheaf J Λ V r) ⟶
      (DerivedCategory.homologyFunctor (Sheaf J (ModuleCat.{u + 1} Λ)) r).obj V :=
  ((presheafToSheaf J (ModuleCat.{u + 1} Λ)).mapDerivedCategoryHomologyFunctorIso r).hom.app
      ((sheafToPresheaf J (ModuleCat.{u + 1} Λ)).rightDerivedFunctor.obj V) ≫
    (DerivedCategory.homologyFunctor (Sheaf J (ModuleCat.{u + 1} Λ)) r).map
      ((Adjunction.mapDerivedCategoryRightDerivedAdjunction
        (sheafificationAdjunction J (ModuleCat.{u + 1} Λ))).counit.app V)

/-- The local-class presheaf morphism is the sheafification unit followed by the
canonical cohomology identification. Source: Stacks 0BKV
(blueprint: lem-pur-derived-local-class-edge-comparison). -/
noncomputable def derivedLocalClassPresheafMap
    (V : DerivedCategory (Sheaf J (ModuleCat.{u + 1} Λ))) (r : ℤ) :
    derivedLocalCohomologyPresheaf J Λ V r ⟶
      ((DerivedCategory.homologyFunctor (Sheaf J (ModuleCat.{u + 1} Λ)) r).obj V).obj :=
  toSheafify J (derivedLocalCohomologyPresheaf J Λ V r) ≫
    (derivedLocalClassSheafification J Λ V r).hom

/-- Global local-class edge, the transpose of the derived constant-sheaf counit.
Source: Stacks 0BKV (blueprint: lem-pur-derived-local-class-edge-comparison). -/
noncomputable def derivedGlobalLocalClassEdge [HasGlobalSectionsFunctor J (ModuleCat.{u + 1} Λ)]
    (V : DerivedCategory (Sheaf J (ModuleCat.{u + 1} Λ))) (r : ℤ) :
    (DerivedCategory.homologyFunctor (ModuleCat.{u + 1} Λ) r).obj
        ((Sheaf.Γ J (ModuleCat.{u + 1} Λ)).rightDerivedFunctor.obj V) ⟶
      (Sheaf.Γ J (ModuleCat.{u + 1} Λ)).obj
        ((DerivedCategory.homologyFunctor (Sheaf J (ModuleCat.{u + 1} Λ)) r).obj V) :=
  derivedLocalClassMate (constantSheafΓAdj J (ModuleCat.{u + 1} Λ)) V r

end Site

end CategoryTheory

namespace CategoryTheory

/-- Canonical degree-r cohomology identification after a cochain shift by one.
Source: Stacks 0BKV, signed cochain shift
(blueprint: lem-pur-derived-local-class-edge-comparison). -/
noncomputable def localClassCohomologyShift
    {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
    [Abelian C] [Abelian D] [HasDerivedCategory.{wC} C] [HasDerivedCategory.{wD} D]
    (F : DerivedCategory C ⥤ DerivedCategory D) [F.CommShift ℤ]
    (V : DerivedCategory C) (r : ℤ) :
    (DerivedCategory.homologyFunctor D r).obj (F.obj (V⟦(1 : ℤ)⟧)) ≅
      (DerivedCategory.homologyFunctor D (r + 1)).obj (F.obj V) :=
  (DerivedCategory.homologyFunctor D r).mapIso ((F.commShiftIso (1 : ℤ)).app V) ≪≫
    ((DerivedCategory.homologyFunctor D 0).shiftIso 1 r (r + 1) (add_comm 1 r)).app
      (F.obj V)

/-- The same shift comparison on a bounded-below object, including the canonical
shift comparison for the full-subcategory inclusion into the ambient derived category.
Source: Stacks 0BKV (blueprint: lem-pur-derived-local-class-edge-comparison). -/
noncomputable def localClassPlusCohomologyShift
    {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
    [Abelian C] [Abelian D] [HasDerivedCategory.{wC} C] [HasDerivedCategory.{wD} D]
    (F : DerivedCategory C ⥤ DerivedCategory D) [F.CommShift ℤ]
    (V : DerivedCategory.Plus C) (r : ℤ) :
    (DerivedCategory.homologyFunctor D r).obj (F.obj ((V⟦(1 : ℤ)⟧).obj)) ≅
      (DerivedCategory.homologyFunctor D (r + 1)).obj (F.obj V.obj) :=
  (DerivedCategory.homologyFunctor D r).mapIso
      (F.mapIso ((DerivedCategory.Plus.ι.commShiftIso (1 : ℤ)).app V)) ≪≫
    localClassCohomologyShift F V.obj r

section SiteLaws

variable {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
    (J : GrothendieckTopology C) (Λ : Type (u + 1)) [CommRing Λ] [HasTerminal C]

/-- At any site object, the presheaf value is canonically the cohomology of derived
literal evaluation; exact evaluation commutes with right derivation and cohomology.
Source: Stacks 0BKV (blueprint: lem-pur-derived-local-class-edge-comparison). -/
noncomputable def localClassObjectCohomologyIso (W : C)
    (V : DerivedCategory (Sheaf J (ModuleCat.{u + 1} Λ))) (r : ℤ) :
    (derivedLocalCohomologyPresheaf J Λ V r).obj (op W) ≅
      (DerivedCategory.homologyFunctor (ModuleCat.{u + 1} Λ) r).obj
        ((sheafToPresheaf J (ModuleCat.{u + 1} Λ) ⋙
          (evaluation Cᵒᵖ (ModuleCat.{u + 1} Λ)).obj (op W)).rightDerivedFunctor.obj V) :=
  (Functor.mapDerivedCategoryHomologyFunctorIso
      ((evaluation Cᵒᵖ (ModuleCat.{u + 1} Λ)).obj (op W)) r).app
        ((sheafToPresheaf J (ModuleCat.{u + 1} Λ)).rightDerivedFunctor.obj V) ≪≫
    (DerivedCategory.homologyFunctor (ModuleCat.{u + 1} Λ) r).mapIso
      ((Functor.rightDerivedFunctorCompMapDerivedCategoryIso
        (sheafToPresheaf J (ModuleCat.{u + 1} Λ))
        ((evaluation Cᵒᵖ (ModuleCat.{u + 1} Λ)).obj (op W))).symm.app V)

/-- Derived global sections evaluated at a terminal site object, using the canonical
right-derived comparison for composition with exact evaluation.
Source: Stacks 0BKV, final-object evaluation
(blueprint: lem-pur-derived-local-class-edge-comparison). -/
noncomputable def localClassTerminalCohomologyIso (W : C) (hW : IsTerminal W)
    (V : DerivedCategory (Sheaf J (ModuleCat.{u + 1} Λ))) (r : ℤ) :
    (DerivedCategory.homologyFunctor (ModuleCat.{u + 1} Λ) r).obj
        ((Sheaf.Γ J (ModuleCat.{u + 1} Λ)).rightDerivedFunctor.obj V) ≅
      (derivedLocalCohomologyPresheaf J Λ V r).obj (op W) :=
  (DerivedCategory.homologyFunctor (ModuleCat.{u + 1} Λ) r).mapIso
      ((Functor.rightDerivedFunctorNatIso
          (Sheaf.ΓNatIsoSheafSections J (ModuleCat.{u + 1} Λ) hW ≪≫
            sheafSectionsNatIsoEvaluation J (ModuleCat.{u + 1} Λ))).app V ≪≫
        (Functor.rightDerivedFunctorCompMapDerivedCategoryIso
          (sheafToPresheaf J (ModuleCat.{u + 1} Λ))
          ((evaluation Cᵒᵖ (ModuleCat.{u + 1} Λ)).obj (op W))).app V) ≪≫
    (Functor.mapDerivedCategoryHomologyFunctorIso
      ((evaluation Cᵒᵖ (ModuleCat.{u + 1} Λ)).obj (op W)) r).symm.app
        ((sheafToPresheaf J (ModuleCat.{u + 1} Λ)).rightDerivedFunctor.obj V)

/-- The four local-class assertions on one site: sheafification, evaluation at the final
object, naturality for all derived morphisms, and compatibility with the cochain shift.
Only cohomological boundedness below is imposed on the objects.
Source: Stacks 0BKV (blueprint: lem-pur-derived-local-class-edge-comparison). -/
def DerivedLocalClassEdgeLaws : Prop :=
  (∀ (V : DerivedCategory.Plus (Sheaf J (ModuleCat.{u + 1} Λ))) (r : ℤ),
    IsIso (derivedLocalClassSheafification J Λ V.obj r)) ∧
  (∀ (V : DerivedCategory.Plus (Sheaf J (ModuleCat.{u + 1} Λ))) (r : ℤ)
      (W : C) (hW : IsTerminal W),
    derivedGlobalLocalClassEdge J Λ V.obj r ≫
        (Sheaf.ΓNatIsoSheafSections J (ModuleCat.{u + 1} Λ) hW).hom.app
          ((DerivedCategory.homologyFunctor (Sheaf J (ModuleCat.{u + 1} Λ)) r).obj V.obj) =
      (localClassTerminalCohomologyIso J Λ W hW V.obj r).hom ≫
        (derivedLocalClassPresheafMap J Λ V.obj r).app (op W)) ∧
  (∀ (V V' : DerivedCategory.Plus (Sheaf J (ModuleCat.{u + 1} Λ)))
      (f : V ⟶ V') (r : ℤ),
    (DerivedCategory.homologyFunctor (ModuleCat.{u + 1} Λ) r).map
        ((Sheaf.Γ J (ModuleCat.{u + 1} Λ)).rightDerivedFunctor.map f.hom) ≫
          derivedGlobalLocalClassEdge J Λ V'.obj r =
      derivedGlobalLocalClassEdge J Λ V.obj r ≫
        (Sheaf.Γ J (ModuleCat.{u + 1} Λ)).map
          ((DerivedCategory.homologyFunctor (Sheaf J (ModuleCat.{u + 1} Λ)) r).map f.hom)) ∧
  (∀ (V : DerivedCategory.Plus (Sheaf J (ModuleCat.{u + 1} Λ))) (r : ℤ),
    derivedGlobalLocalClassEdge J Λ (V.obj⟦(1 : ℤ)⟧) r ≫
        (Sheaf.Γ J (ModuleCat.{u + 1} Λ)).map
          ((Functor.shiftIso
            (DerivedCategory.homologyFunctor (Sheaf J (ModuleCat.{u + 1} Λ)) 0)
            1 r (r + 1) (add_comm 1 r)).hom.app V.obj) =
      (localClassCohomologyShift
        (Sheaf.Γ J (ModuleCat.{u + 1} Λ)).rightDerivedFunctor V.obj r).hom ≫
          derivedGlobalLocalClassEdge J Λ V.obj (r + 1))

end SiteLaws

end CategoryTheory

namespace AlgebraicGeometry.ProEtale

/-- The cohomology comparison specified by the derived comparison unit, with the
canonical Leray identification; this is exactly the map of sk-prop-sf-comparison.
Source: Stacks 099V and 099W (blueprint: lem-pur-derived-local-class-edge-comparison). -/
noncomputable def localClassSiteComparison (P : WeilConjectures.PurityFiniteSetting.{u})
    (T : Scheme.{u})
    (V : DerivedCategory.Plus (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient)))
    (r : ℤ) :
    (DerivedCategory.homologyFunctor (ModuleCat.{u + 1} P.Coefficient) r).obj
        ((Etale.rightDerivedGlobalSections (ModuleCat.{u + 1} P.Coefficient) T).obj V.obj) ⟶
      (DerivedCategory.homologyFunctor (ModuleCat.{u + 1} P.Coefficient) r).obj
        ((rightDerivedGlobalSections (ModuleCat.{u + 1} P.Coefficient) T).obj
          ((Functor.mapDerivedCategory
            (comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) T)).obj V.obj)) :=
  (DerivedCategory.homologyFunctor (ModuleCat.{u + 1} P.Coefficient) r).map
    ((boundedBelowComparisonGlobalSections T P.Coefficient).app V)

/-- Pullback of a section of the cohomology sheaf: apply the ordinary comparison unit,
identify final-object sections, and use the canonical exact-inverse-image cohomology iso.
Source: Stacks 07A6 and 0BKV (blueprint: lem-pur-derived-local-class-edge-comparison). -/
noncomputable def localClassSectionPullback (P : WeilConjectures.PurityFiniteSetting.{u})
    (T : Scheme.{u})
    (V : DerivedCategory.Plus (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient)))
    (r : ℤ) :
    (Sheaf.Γ T.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient)).obj
        ((DerivedCategory.homologyFunctor
          (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient)) r).obj V.obj) ⟶
      (Sheaf.Γ (Scheme.ProEt.topology T) (ModuleCat.{u + 1} P.Coefficient)).obj
        ((DerivedCategory.homologyFunctor
          (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} P.Coefficient)) r).obj
            ((Functor.mapDerivedCategory
            (comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) T)).obj V.obj)) :=
  (Sheaf.Γ T.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient)).map
      ((comparisonAdjunction (ModuleCat.{u + 1} P.Coefficient) T).unit.app
        ((DerivedCategory.homologyFunctor
          (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient)) r).obj V.obj)) ≫
    (comparisonLowerStarCompGlobalSectionsIso (ModuleCat.{u + 1} P.Coefficient) T).hom.app
      ((comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) T).obj
        ((DerivedCategory.homologyFunctor
          (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient)) r).obj V.obj)) ≫
    (Sheaf.Γ (Scheme.ProEt.topology T) (ModuleCat.{u + 1} P.Coefficient)).map
      ((Functor.mapDerivedCategoryHomologyFunctorIso
        (comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) T) r).hom.app V.obj)

end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.ProEtale

/-- The comparison square, its derived-morphism naturality, and its shift compatibility.
All arrows are the previously constructed canonical arrows, rather than arbitrary maps.
Source: Stacks 0BKV and the unit of sk-prop-sf-comparison
(blueprint: lem-pur-derived-local-class-edge-comparison). -/
def DerivedLocalClassSiteLaws (P : WeilConjectures.PurityFiniteSetting.{u})
    (T : Scheme.{u}) : Prop :=
  (∀ (V : DerivedCategory.Plus
      (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient))) (r : ℤ),
    IsIso (localClassSiteComparison P T V r) ∧
    localClassSiteComparison P T V r ≫
        derivedGlobalLocalClassEdge (Scheme.ProEt.topology T) P.Coefficient
          ((Functor.mapDerivedCategory
            (comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) T)).obj V.obj) r =
      derivedGlobalLocalClassEdge T.smallEtaleTopology P.Coefficient V.obj r ≫
        localClassSectionPullback P T V r) ∧
  (∀ (V V' : DerivedCategory.Plus
      (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient)))
      (f : V ⟶ V') (r : ℤ),
    (DerivedCategory.homologyFunctor (ModuleCat.{u + 1} P.Coefficient) r).map
        ((Etale.rightDerivedGlobalSections (ModuleCat.{u + 1} P.Coefficient) T).map f.hom) ≫
          localClassSiteComparison P T V' r =
      localClassSiteComparison P T V r ≫
        (DerivedCategory.homologyFunctor (ModuleCat.{u + 1} P.Coefficient) r).map
          ((rightDerivedGlobalSections (ModuleCat.{u + 1} P.Coefficient) T).map
            ((Functor.mapDerivedCategory
              (comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) T)).map f.hom))) ∧
  (∀ (V : DerivedCategory.Plus
      (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient))) (r : ℤ),
    localClassSiteComparison P T (V⟦(1 : ℤ)⟧) r ≫
        (localClassPlusCohomologyShift
          ((comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) T).mapDerivedCategory ⋙
            (Sheaf.Γ (Scheme.ProEt.topology T)
              (ModuleCat.{u + 1} P.Coefficient)).rightDerivedFunctor) V r).hom =
      (localClassPlusCohomologyShift
        (Sheaf.Γ T.smallEtaleTopology
          (ModuleCat.{u + 1} P.Coefficient)).rightDerivedFunctor V r).hom ≫
          localClassSiteComparison P T V (r + 1))

/-- On either small site, sheafified derived section cohomology is the cohomology
sheaf. The canonical local-class edges are natural for arbitrary derived maps, commute
with cochain shifts, and commute with the specified etale/pro-etale comparison.
Source: Stacks, sites-cohomology.tex, 0BKV and 0D6I; sk-prop-sf-comparison
(blueprint: lem-pur-derived-local-class-edge-comparison).

Proof:
1. The ringed-site category is Grothendieck abelian
(lem-pur-ringed-site-grothendieck-abelian), hence has enough injectives
(lem-sp-grothendieck-enough-injectives). Represent each D+ object by a bounded-below
complex I of injective sheaves (lem-weil-pbc-dplus-injective-representative).
The slice-section model (lem-pe-injective-complex-slice-section-model) identifies
H^r(W,V) with the cohomology of I(W), with literal restriction maps.
2. Objectwise cohomology and exact sheafification
(lem-weil-pbc-site-module-presheaf-sheafification-exact) identify the sheafified
presheaf with H^r(I). The derived sheafification counit gives this identification:
its transpose is the sheafification unit followed by the cycle quotient. At the
terminal object the constant-sheaf adjunction gives the same cycle quotient.
3. Represent every derived map between injective models by a chain map, uniquely
up to homotopy (lem-weil-pbc-kinjective-hom-derived). The edge sends a cycle to its
cohomology-sheaf class; both naturality composites send z to the class of f(z).
A homotopy changes the value by a boundary, proving independence of the model.
4. For I[1], the differential is -d_I (def-weil-abstract-derived-category).
Its kernels and images are unchanged, so the same quotient gives the shift law.
5. Exact inverse image commutes with cohomology and cycle quotients
(lem-weil-pbc-exact-functor-complex-cohomology). Resolve its image LI by an
injective complex J and a quasi-isomorphism a:LI -> J.
6. The bounded-below derived adjunction unit is represented by eta_I followed by
R(a) (lem-trf-bounded-below-derived-adjunction and
lem-weil-pbc-right-derived-plus-injective). Direct image preserves injectives
(lem-sp-right-adjoint-preserves-injectives), and sections of RJ at the final
object are sections of J. The canonical Leray isomorphism
(lem-weil-pbc-derived-sections-pushforward) therefore identifies the specified
comparison with z -> a(Lz). It is invertible by sk-prop-sf-comparison.
7. Both sides of the site square send a cycle z to the quotient class of a(Lz),
using the exact-inverse-image cohomology identification from step 5.
8. For derived maps, chain representatives of the two comparison composites are
homotopic, so their cohomology maps agree. For shifts use I[1], J[1], a[1];
additivity of inverse image and the kernel/image calculation of step 4 give
the comparison shift equation. The edge naturality and shift equations then
make the site square compatible with these operations. No concentration or
constructibility was used. -/
theorem derivedLocalClassEdgeComparison (P : WeilConjectures.PurityFiniteSetting.{u})
    (T : Scheme.{u}) :
    DerivedLocalClassEdgeLaws T.smallEtaleTopology P.Coefficient ∧
      DerivedLocalClassEdgeLaws (Scheme.ProEt.topology T) P.Coefficient ∧
      DerivedLocalClassSiteLaws P T := by
  sorry

end AlgebraicGeometry.ProEtale
