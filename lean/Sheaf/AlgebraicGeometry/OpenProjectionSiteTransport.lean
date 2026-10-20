/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q21
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekProjection
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.OpenLowerShriekProj
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.FlatModuleCat
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FiniteEtaleFlat
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Comparison
public import Sheaf.AlgebraicGeometry.ComparisonDerivedPullbackFixed
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import Sheaf.AlgebraicGeometry.ProEtaleFiniteModules
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ComparisonMonoidal
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekComparison
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
import Sheaf.AlgebraicGeometry.OpenProjectionComparisonSquare
import Sheaf.AlgebraicGeometry.OpenProjectionSourcePlus

/-!
# Site transport of the open projection formula

Source: Stacks Project, `proetale.tex`, Tag 09AF, `lemma-jshriek-comparison`,
combined with `sites-cohomology.tex`, Tag 0GL1, `lemma-j-shriek-and-tensor`.
The derived statement and its K-flat normalization follow the blueprint item
`lem-pur-open-projection-site-transport` (blueprint: lem-pur-open-projection-site-transport).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

/-- The derived, adjoint-normalized extension comparison, obtained by descending
`openImmersionLowerShriekComparisonUpperStarIso` termwise, with the canonical
composition identifications. Source: Stacks Project, Tag 09AF
(blueprint: lem-pur-open-projection-site-transport). -/
noncomputable def openProjectionExtensionComparison (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    (Etale.openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j).mapDerivedCategory ⋙
        (comparisonUpperStar (ModuleCat.{u + 1} Λ) X).mapDerivedCategory ≅
      (comparisonUpperStar (ModuleCat.{u + 1} Λ) U).mapDerivedCategory ⋙
        (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j).mapDerivedCategory :=
  (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso
      (openImmersionLowerShriekComparisonUpperStarIso (ModuleCat.{u + 1} Λ) j) ≪≫
    Functor.mapDerivedCategoryCompIso _ _

/-- The canonical inverse-image comparison, converted from exact termwise pullbacks
using `leftDerivedUpperStarIsoMapDerivedCategory` on both sites. Its direction is
`C_U Lj_e^* ≅ Lj_p^* C_X`. Source: Stacks Project, Tag 099R
(blueprint: lem-pur-open-projection-site-transport). -/
noncomputable def openProjectionRestrictionComparison (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    (Etale.upperStar (ModuleCat.{u + 1} Λ) j).leftDerivedFunctor ⋙
        (comparisonUpperStar (ModuleCat.{u + 1} Λ) U).mapDerivedCategory ≅
      (comparisonUpperStar (ModuleCat.{u + 1} Λ) X).mapDerivedCategory ⋙
        (upperStar (ModuleCat.{u + 1} Λ) j).leftDerivedFunctor :=
  Functor.isoWhiskerRight
      (Etale.leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} Λ) j) _ ≪≫
    ((Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
      Functor.mapDerivedCategoryNatIso
        (comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} Λ) j) ≪≫
      Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.isoWhiskerLeft _
      (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} Λ) j).symm

/-- The specified identification of the sources of the two projection adjuncts:
first the derived extension comparison, then the comparison's derived tensor
isomorphism, and finally the inverse-image comparison in the second tensor factor.
Source: Stacks Project, Tags 09AF and 0GL1
(blueprint: lem-pur-open-projection-site-transport). -/
noncomputable def openProjectionSourceComparison (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (F : DerivedCategory (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (G : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (comparisonUpperStar (ModuleCat.{u + 1} Λ) X).mapDerivedCategory.obj
        ((Etale.openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j).mapDerivedCategory.obj
          (((Etale.derivedTensorWhiskeringRightLeftDerivedUpperStar
            (ModuleCat.{u + 1} Λ) j).obj F).obj G)) ≅
      (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j).mapDerivedCategory.obj
        (((derivedTensorWhiskeringRightLeftDerivedUpperStar
          (ModuleCat.{u + 1} Λ) j).obj
            ((comparisonUpperStar (ModuleCat.{u + 1} Λ) U).mapDerivedCategory.obj F)).obj
          ((comparisonUpperStar (ModuleCat.{u + 1} Λ) X).mapDerivedCategory.obj G)) :=
  (openProjectionExtensionComparison Λ j).app _ ≪≫
    (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j).mapDerivedCategory.mapIso
      (((derivedTensorObjCompMapDerivedCategoryComparisonUpperStarIso
        (ModuleCat.{u + 1} Λ) F).app _) ≪≫
        ((derivedTensor (ModuleCat.{u + 1} Λ) U).obj _).mapIso
          ((openProjectionRestrictionComparison Λ j).app G))

/-- The specified identification of the targets of the two projection adjuncts:
the comparison's derived tensor isomorphism followed by the derived extension
comparison in its first factor. Source: Stacks Project, Tags 09AF and 0GL1
(blueprint: lem-pur-open-projection-site-transport). -/
noncomputable def openProjectionTargetComparison (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (F : DerivedCategory (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (G : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (comparisonUpperStar (ModuleCat.{u + 1} Λ) X).mapDerivedCategory.obj
        (((Etale.derivedTensorWhiskeringLeftOpenImmersionLowerShriek
          (ModuleCat.{u + 1} Λ) j).obj F).obj G) ≅
      ((derivedTensorWhiskeringLeftOpenImmersionLowerShriek
        (ModuleCat.{u + 1} Λ) j).obj
          ((comparisonUpperStar (ModuleCat.{u + 1} Λ) U).mapDerivedCategory.obj F)).obj
        ((comparisonUpperStar (ModuleCat.{u + 1} Λ) X).mapDerivedCategory.obj G) :=
  (derivedTensorObjCompMapDerivedCategoryComparisonUpperStarIso
      (ModuleCat.{u + 1} Λ)
      ((Etale.openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j).mapDerivedCategory.obj F)).app G ≪≫
    ((derivedTensor (ModuleCat.{u + 1} Λ) X).mapIso
      ((openProjectionExtensionComparison Λ j).app F)).app _

/-- The boundedness, inverse identities and the two canonical transport squares for
fixed derived objects. The forward maps are the inverses of the recorded canonical
projection isomorphisms; their identification as the forward open projection is
part of the recorded interfaces `lem-pur-etale-open-derived-tensor` and
`lem-cbc-extension-zero-projection-formula`. No comparison isomorphism is quantified
or chosen here. Source: Stacks Project, Tags 09AF and 0GL1
(blueprint: lem-pur-open-projection-site-transport). -/
def OpenProjectionTransport (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (F : DerivedCategory (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (G : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) : Prop :=
  let Fp := (comparisonUpperStar (ModuleCat.{u + 1} Λ) U).mapDerivedCategory.obj F
  let Gp := (comparisonUpperStar (ModuleCat.{u + 1} Λ) X).mapDerivedCategory.obj G
  let κe := ((Etale.derivedOpenImmersionLowerShriekProjectionMap
    (ModuleCat.{u + 1} Λ) j).app F).app G
  let κp := ((derivedOpenImmersionLowerShriekProjectionMap
    (ModuleCat.{u + 1} Λ) j).app Fp).app Gp
  let γe := ((Etale.derivedOpenImmersionLowerShriekProjectionIso
    (ModuleCat.{u + 1} Λ) j).inv.app F).app G
  let γp := ((derivedOpenImmersionLowerShriekProjectionIso
    (ModuleCat.{u + 1} Λ) j).inv.app Fp).app Gp
  DerivedCategory.TStructure.t.plus
      ((Etale.openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j).mapDerivedCategory.obj
        (((Etale.derivedTensorWhiskeringRightLeftDerivedUpperStar
          (ModuleCat.{u + 1} Λ) j).obj F).obj G)) ∧
    DerivedCategory.TStructure.t.plus
      (((Etale.derivedTensorWhiskeringLeftOpenImmersionLowerShriek
        (ModuleCat.{u + 1} Λ) j).obj F).obj G) ∧
    DerivedCategory.TStructure.t.plus
      ((openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j).mapDerivedCategory.obj
        (((derivedTensorWhiskeringRightLeftDerivedUpperStar
          (ModuleCat.{u + 1} Λ) j).obj Fp).obj Gp)) ∧
    DerivedCategory.TStructure.t.plus
      (((derivedTensorWhiskeringLeftOpenImmersionLowerShriek
        (ModuleCat.{u + 1} Λ) j).obj Fp).obj Gp) ∧
    IsIso κe ∧ IsIso γe ∧ IsIso κp ∧ IsIso γp ∧
    κe ≫ γe = 𝟙 _ ∧ γe ≫ κe = 𝟙 _ ∧
    κp ≫ γp = 𝟙 _ ∧ γp ≫ κp = 𝟙 _ ∧
    (comparisonUpperStar (ModuleCat.{u + 1} Λ) X).mapDerivedCategory.map κe ≫
        (openProjectionTargetComparison Λ j F G).hom =
      (openProjectionSourceComparison Λ j F G).hom ≫ κp ∧
    (comparisonUpperStar (ModuleCat.{u + 1} Λ) X).mapDerivedCategory.map γe ≫
        (openProjectionSourceComparison Λ j F G).hom =
      (openProjectionTargetComparison Λ j F G).hom ≫ γp

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The normalized open tensor projection and its forward inverse are transported
from the small etale site to the pro-etale site, under the specified comparisons.

Proof (Stacks Project, Tags 09AF and 0GL1):
1. Choose K-flat representatives. Local finite freeness makes tensor with `L` exact;
shifting translates a lower cohomological bound. Exact comparison inverse image and
extension by zero preserve that bound. The canonical etale and pro-etale projection
isomorphisms identify the targets with these bounded-below sources
(`lem-weil-pbc-ringed-topoi-derived-tensor-pullback`, `lem-sf-comparison-pullback-exact`,
`lem-weil-pbc-extension-by-zero-exact`, `lem-weil-extension-by-zero-exact`,
`lem-pur-etale-open-derived-tensor`, `lem-cbc-extension-zero-projection-formula`).
2. The recorded etale projection isomorphism is the adjunction transpose of the
open unit tensored with the identity, using the inverse tensor/pullback comparison;
its inverse is the canonical forward projection (`lem-pur-etale-open-derived-tensor`,
`prop-weil-open-closed-recollement-adjunctions`).
3. The same construction on the pro-etale site identifies the forward projection
and the inverse adjunct (`lem-cbc-extension-zero-projection-formula`,
`lem-sf-open-tensor-normalization`).
4. On K-flat total tensor representatives, apply the ordinary unit-normalized
comparison equality degreewise (`lem-sf-open-comparison-tensor-normalization`).
Exactness and the canonical derived tensor comparison descend this equality. These
are exactly the composites defining `openProjectionSourceComparison` and
`openProjectionTargetComparison`. Taking inverses gives the second transport square.
5. All units, adjunction bijections, extension, inverse-image and tensor comparisons
are natural, so the equalities are natural in both factors. No condition on `G`
beyond boundedness below, or on `Λ` over a smaller ring, is used.
(blueprint: lem-pur-open-projection-site-transport). -/
theorem openProjectionSiteTransport
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (L : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (t : ℕ)
    (hL : SheafOfModules.IsFiniteLocallyFreeOfRank.{u + 1, u, u + 1}
      (R := finiteCoefficientEtaleRingSheaf U Λ)
      ((finiteCoefficientEtaleRealization U Λ).obj L) t)
    (m : ℤ)
    (G : DerivedCategory.Plus
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    OpenProjectionTransport Λ j
      (((DerivedCategory.singleFunctor
        (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)) 0).obj L)⟦m⟧)
      (DerivedCategory.Plus.ι.obj G) := by
  let F := ((DerivedCategory.singleFunctor
    (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)) 0).obj L)⟦m⟧
  let B := DerivedCategory.Plus.ι.obj G
  let C := (comparisonUpperStar (ModuleCat.{u + 1} Λ) X).mapDerivedCategory
  let Fp := (comparisonUpperStar (ModuleCat.{u + 1} Λ) U).mapDerivedCategory.obj F
  let Gp := C.obj B
  let e := ((Etale.derivedOpenImmersionLowerShriekProjectionIso
    (ModuleCat.{u + 1} Λ) j).app F).app B
  let p := ((derivedOpenImmersionLowerShriekProjectionIso
    (ModuleCat.{u + 1} Λ) j).app Fp).app Gp
  have hS : DerivedCategory.TStructure.t.plus
      ((Etale.openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j).mapDerivedCategory.obj
        (((Etale.derivedTensorWhiskeringRightLeftDerivedUpperStar
          (ModuleCat.{u + 1} Λ) j).obj F).obj B)) := by
    exact openProjectionTransport_source_plus Λ j L t hL m G
  have hT : DerivedCategory.TStructure.t.plus
      (((Etale.derivedTensorWhiskeringLeftOpenImmersionLowerShriek
          (ModuleCat.{u + 1} Λ) j).obj F).obj B) :=
    DerivedCategory.TStructure.t.plus.prop_of_iso e hS
  have hCS : DerivedCategory.TStructure.t.plus
      (C.obj ((Etale.openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j).mapDerivedCategory.obj
        (((Etale.derivedTensorWhiskeringRightLeftDerivedUpperStar
          (ModuleCat.{u + 1} Λ) j).obj F).obj B))) := by
    exact ((comparisonUpperStar (ModuleCat.{u + 1} Λ) X).mapDerivedCategoryPlus.obj
      ⟨_, hS⟩).property
  have hPS : DerivedCategory.TStructure.t.plus
      ((openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j).mapDerivedCategory.obj
        (((derivedTensorWhiskeringRightLeftDerivedUpperStar
          (ModuleCat.{u + 1} Λ) j).obj Fp).obj Gp)) :=
    DerivedCategory.TStructure.t.plus.prop_of_iso
      (openProjectionSourceComparison Λ j F B) hCS
  have hPT : DerivedCategory.TStructure.t.plus
      (((derivedTensorWhiskeringLeftOpenImmersionLowerShriek
          (ModuleCat.{u + 1} Λ) j).obj Fp).obj Gp) :=
    DerivedCategory.TStructure.t.plus.prop_of_iso p hPS
  have hκ : C.map e.hom ≫ (openProjectionTargetComparison Λ j F B).hom =
      (openProjectionSourceComparison Λ j F B).hom ≫ p.hom :=
    by
      simpa only [e, p, C, Fp, Gp, Iso.app_hom,
        Etale.derivedTensorWhiskeringRightLeftDerivedUpperStar,
        derivedTensorWhiskeringLeftOpenImmersionLowerShriek,
        Functor.whiskeringLeft₂, Functor.whiskeringLeft, Functor.whiskeringRight,
        Functor.comp_obj, Functor.id_obj,
        Etale.derivedOpenImmersionLowerShriekProjectionIso_hom,
        derivedOpenImmersionLowerShriekProjectionIso_hom,
        openProjectionTargetComparison, openProjectionSourceComparison,
        openProjectionExtensionComparison, openProjectionRestrictionComparison] using
          openProjectionTransport_projection_square Λ j F B
  have hγ : C.map e.inv ≫ (openProjectionSourceComparison Λ j F B).hom =
      (openProjectionTargetComparison Λ j F B).hom ≫ p.inv := by
    apply (cancel_epi (C.map e.hom)).1
    simp only [← C.map_comp_assoc, e.hom_inv_id, C.map_id, Category.id_comp]
    rw [← Category.assoc, hκ]
    simp only [Category.assoc, p.hom_inv_id]
    erw [Category.comp_id]
  change DerivedCategory.TStructure.t.plus
      ((Etale.openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j).mapDerivedCategory.obj
        (((Etale.derivedTensorWhiskeringRightLeftDerivedUpperStar
          (ModuleCat.{u + 1} Λ) j).obj F).obj B)) ∧
    DerivedCategory.TStructure.t.plus (((Etale.derivedTensorWhiskeringLeftOpenImmersionLowerShriek
          (ModuleCat.{u + 1} Λ) j).obj F).obj B) ∧
    DerivedCategory.TStructure.t.plus
      ((openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j).mapDerivedCategory.obj
        (((derivedTensorWhiskeringRightLeftDerivedUpperStar
          (ModuleCat.{u + 1} Λ) j).obj Fp).obj Gp)) ∧
    DerivedCategory.TStructure.t.plus (((derivedTensorWhiskeringLeftOpenImmersionLowerShriek
          (ModuleCat.{u + 1} Λ) j).obj Fp).obj Gp) ∧
    IsIso e.hom ∧ IsIso e.inv ∧ IsIso p.hom ∧ IsIso p.inv ∧
    e.hom ≫ e.inv = 𝟙 _ ∧ e.inv ≫ e.hom = 𝟙 _ ∧
    p.hom ≫ p.inv = 𝟙 _ ∧ p.inv ≫ p.hom = 𝟙 _ ∧ _
  exact ⟨hS, hT, hPS, hPT, inferInstance, inferInstance, inferInstance, inferInstance,
    e.hom_inv_id, e.inv_hom_id, p.hom_inv_id, p.inv_hom_id, hκ, hγ⟩
end AlgebraicGeometry.ProEtale
