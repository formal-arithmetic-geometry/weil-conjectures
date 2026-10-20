/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q13
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import Sheaf.Paper.CartesianCoefficients
public import Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
public import Mathlib.AlgebraicGeometry.Pullbacks
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
import Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition
import Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Sheaf.CategoryTheory.KInjectiveDerivedMapComputation
import Sheaf.AlgebraicGeometry.ProEtaleOpenRestrictionCounit
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs

/-!
# Coherence of derived direct image and open restriction

Source: blueprint main-20261015, `sk-thm-sf-comp-composition`, Composition isomorphism
and Canonicity and associativity; Stacks Tags 08BJ, 070I, 070Y and 0D6E
(blueprint: lem-sfb-derived-direct-image-open-coherence).

All categories below are the ordinary unbounded derived categories of internal modules
on the small pro-etale sites, with the actual pulled-back condensed coefficient rings.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- Direct image preserves K-injectives, as the right adjoint of exact module pullback.
Source: Stacks Tag 08BJ (blueprint: lem-sfb-derived-direct-image-open-coherence). -/
instance lowerStar_preservesKInjectives {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (lowerStar Λ f).PreservesKInjectiveComplexes :=
  (upperStarLowerStarAdjunction Λ f).preservesKInjectiveComplexes

/-- The resolution-normalized composition comparison: derive the inverse of the existing
module direct-image comparison and then use the canonical derived composition isomorphism.
Source: Stacks Tag 0D6E (blueprint: lem-sfb-derived-direct-image-open-coherence). -/
noncomputable def directImageComposition {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (lowerStar Λ (f ≫ g)).rightDerivedFunctor ≅
      (lowerStar Λ f).rightDerivedFunctor ⋙ (lowerStar Λ g).rightDerivedFunctor :=
  Functor.rightDerivedFunctorNatIso (lowerStarComp Λ f g).symm ≪≫
    Functor.rightDerivedFunctorCompIso (lowerStar Λ f) (lowerStar Λ g)

/-- The canonical pullback square comparison on module objects; coefficient actions use
extension along alpha, equivalently restriction along alpha inverse by CartesianCoefficients.
Source: blueprint composition proof (blueprint: lem-sfb-derived-direct-image-open-coherence). -/
noncomputable def openCoherencePullbackSquare
    {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {j : Y' ⟶ Y}
    {f' : X' ⟶ Y'} {i : X' ⟶ X} (sq : CommSq i f' f j) :
    upperStar Λ j ⋙ upperStar Λ f' ≅ upperStar Λ f ⋙ upperStar Λ i :=
  (upperStarComp Λ f' j).symm ≪≫
    eqToIso (congrArg (upperStar Λ) sq.w.symm) ≪≫ upperStarComp Λ i f

/-- The canonical underived open restriction map, defined as the mate of the specified
pullback square comparison. Its sectionwise normalization is stated below.
Source: Stacks Tag 09A5 (blueprint: lem-sfb-derived-direct-image-open-coherence). -/
noncomputable def directImageOpenRestriction
    {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {j : Y' ⟶ Y}
    {f' : X' ⟶ Y'} {i : X' ⟶ X} (sq : CommSq i f' f j) :
    lowerStar Λ f ⋙ upperStar Λ j ⟶ upperStar Λ i ⋙ lowerStar Λ f' :=
  (mateEquiv (upperStarLowerStarAdjunction Λ f) (upperStarLowerStarAdjunction Λ f')
    (TwoSquare.mk _ _ _ _ (openCoherencePullbackSquare Λ sq).hom)).natTrans

/-- The same pullback square comparison after exact, termwise passage to derived categories.
Source: blueprint composition proof (blueprint: lem-sfb-derived-direct-image-open-coherence). -/
noncomputable def derivedOpenCoherencePullbackSquare
    {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {j : Y' ⟶ Y}
    {f' : X' ⟶ Y'} {i : X' ⟶ X} (sq : CommSq i f' f j) :
    (upperStar Λ j).mapDerivedCategory ⋙ (upperStar Λ f').mapDerivedCategory ≅
      (upperStar Λ f).mapDerivedCategory ⋙ (upperStar Λ i).mapDerivedCategory :=
  (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso (openCoherencePullbackSquare Λ sq) ≪≫
      Functor.mapDerivedCategoryCompIso _ _

/-- The canonical derived open restriction map, using the exact-left derived adjunctions.
Source: blueprint composition proof (blueprint: lem-sfb-derived-direct-image-open-coherence). -/
noncomputable def derivedDirectImageOpenRestriction
    {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {j : Y' ⟶ Y}
    {f' : X' ⟶ Y'} {i : X' ⟶ X} (sq : CommSq i f' f j) :
    (lowerStar Λ f).rightDerivedFunctor ⋙ (upperStar Λ j).mapDerivedCategory ⟶
      (upperStar Λ i).mapDerivedCategory ⋙ (lowerStar Λ f').rightDerivedFunctor :=
  (mateEquiv
    (upperStarLowerStarAdjunction Λ f).mapDerivedCategoryRightDerivedAdjunction
    (upperStarLowerStarAdjunction Λ f').mapDerivedCategoryRightDerivedAdjunction
    (TwoSquare.mk _ _ _ _ (derivedOpenCoherencePullbackSquare Λ sq).hom)).natTrans

/-- Open restriction preserves K-injectives because exact extension by zero is its left
adjoint. Source: Stacks Tag 08BJ (blueprint: lem-sfb-derived-direct-image-open-coherence). -/
instance upperStar_preservesKInjectives {X Y : Scheme.{u}} (j : X ⟶ Y)
    [IsOpenImmersion j] : (upperStar Λ j).PreservesKInjectiveComplexes :=
  (openImmersionLowerShriekUpperStarAdjunction Λ j).preservesKInjectiveComplexes

/-- The canonical open-slice section identification, expressed by the module adjunction
unit at the distinguished site object. Source: Stacks Tag 09A5
(blueprint: lem-sfb-derived-direct-image-open-coherence). -/
noncomputable def openCoherenceSectionCoprojection
    {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j]
    (M : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y))
    (V : X.ProEt) :
    M.X.obj.obj
        (op ((MorphismProperty.Over.map (f := j) ⊤ (inferInstance : WeaklyEtale j)).obj V)) →
      ((upperStar Λ j).obj M).X.obj.obj (op V) :=
  fun s ↦ ((upperStar Λ j).obj M).X.obj.map
    ((MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ j inferInstance trivial).unit.app V).op
      ((((upperStarLowerStarAdjunction Λ j).unit.app M).hom.hom.app
        (op ((MorphismProperty.Over.map (f := j) ⊤
          (inferInstance : WeaklyEtale j)).obj V))) s)

/-- The fibre-product identification used to compare sections in a Cartesian open square.
It is the identity on the test object and the specified open inclusion on the other factor.
Source: blueprint composition proof (blueprint: lem-sfb-derived-direct-image-open-coherence). -/
noncomputable def openCoherenceSectionArrow
    {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {j : Y' ⟶ Y}
    {f' : X' ⟶ Y'} {i : X' ⟶ X} [IsOpenImmersion j] [IsOpenImmersion i]
    (sq : CommSq i f' f j) (V : Y'.ProEt) :
    (MorphismProperty.Over.map (f := i) ⊤ (inferInstance : WeaklyEtale i)).obj
        ((Scheme.proEtaleBaseChange f').obj V) ⟶
      (Scheme.proEtaleBaseChange f).obj
        ((MorphismProperty.Over.map (f := j) ⊤ (inferInstance : WeaklyEtale j)).obj V) :=
  MorphismProperty.Over.homMk
    (pullback.map V.hom f' (V.hom ≫ j) f (𝟙 V.left) i j
      (Category.id_comp _).symm sq.w.symm)
    (pullback.lift_snd _ _ _)

/-- Sectionwise normalization: the open-slice identifications are bijective, and the
comparison sends a section to the same section along the canonical fibre-product map.
Identity maps and identity opens are included in these quantifiers.
Source: Stacks Tag 09A5 (blueprint: lem-sfb-derived-direct-image-open-coherence). -/
def OpenCoherenceSectionwise
    {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {j : Y' ⟶ Y}
    {f' : X' ⟶ Y'} {i : X' ⟶ X} [IsOpenImmersion j] [IsOpenImmersion i]
    (sq : CommSq i f' f j) : Prop :=
  (∀ (M : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y))
    (V : Y'.ProEt), Function.Bijective (openCoherenceSectionCoprojection Λ j M V)) ∧
  (∀ (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (V : X'.ProEt), Function.Bijective (openCoherenceSectionCoprojection Λ i M V)) ∧
  ∀ (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (V : Y'.ProEt)
    (s : M.X.obj.obj (op ((Scheme.proEtaleBaseChange f).obj
      ((MorphismProperty.Over.map (f := j) ⊤ (inferInstance : WeaklyEtale j)).obj V)))),
    ((directImageOpenRestriction Λ sq).app M).hom.hom.app (op V)
        (openCoherenceSectionCoprojection Λ j ((lowerStar Λ f).obj M) V s) =
      openCoherenceSectionCoprojection Λ i M ((Scheme.proEtaleBaseChange f').obj V)
        (M.X.obj.map (openCoherenceSectionArrow sq V).op s)

/-- The comparison is the resolution-normalized comparison of Tag 0D6E: on the common
K-injective representative it is the class of the inverse underived composition comparison.
Source: Stacks Tag 0D6E (blueprint: lem-sfb-derived-direct-image-open-coherence). -/
def DirectImageCompositionNormalized {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    Prop :=
  ∀ (I : CochainComplex
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) ℤ)
    [I.IsKInjective],
    (directImageComposition Λ f g).hom.app (DerivedCategory.Q.obj I) ≫
        (lowerStar Λ g).rightDerivedFunctor.map
          ((lowerStar Λ f).rightDerivedFunctorObjQIso I).hom ≫
        ((lowerStar Λ g).rightDerivedFunctorObjQIso
          (((lowerStar Λ f).mapHomologicalComplex (.up ℤ)).obj I)).hom =
      ((lowerStar Λ (f ≫ g)).rightDerivedFunctorObjQIso I).hom ≫
        DerivedCategory.Q.map
          ((NatTrans.mapHomologicalComplex (lowerStarComp Λ f g).inv (.up ℤ)).app I)

/-- Associativity with the canonical functor associator and scheme associativity inserted.
Source: blueprint canonicity paragraph (blueprint: lem-sfb-derived-direct-image-open-coherence).
-/
def DirectImageCompositionAssociative {X Y Z T : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T) : Prop :=
  (directImageComposition Λ (f ≫ g) h).hom ≫
      whiskerRight (directImageComposition Λ f g).hom
        (lowerStar Λ h).rightDerivedFunctor ≫ (Functor.associator _ _ _).hom =
    (Functor.rightDerivedFunctorNatIso
      (eqToIso (congrArg (lowerStar Λ) (Category.assoc f g h)))).hom ≫
      (directImageComposition Λ f (g ≫ h)).hom ≫
      whiskerLeft (lowerStar Λ f).rightDerivedFunctor (directImageComposition Λ g h).hom

/-- Open restriction is invertible and is the class of the degreewise canonical underived
restriction comparison on every K-injective representative. No boundedness is imposed.
Source: Stacks Tags 08BJ, 070I and 070Y
(blueprint: lem-sfb-derived-direct-image-open-coherence). -/
def DirectImageRestrictionNormalized
    {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {j : Y' ⟶ Y}
    {f' : X' ⟶ Y'} {i : X' ⟶ X} [IsOpenImmersion j] [IsOpenImmersion i]
    (sq : CommSq i f' f j) : Prop :=
  IsIso (derivedDirectImageOpenRestriction Λ sq) ∧
  IsIso (directImageOpenRestriction Λ sq) ∧ OpenCoherenceSectionwise Λ sq ∧
  ∀ (I : CochainComplex
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) ℤ)
    [I.IsKInjective],
    (derivedDirectImageOpenRestriction Λ sq).app (DerivedCategory.Q.obj I) ≫
        (lowerStar Λ f').rightDerivedFunctor.map
          ((upperStar Λ i).mapDerivedCategoryFactors.hom.app I) =
      (upperStar Λ j).mapDerivedCategory.map
          ((lowerStar Λ f).rightDerivedFunctorObjQIso I).hom ≫
        (upperStar Λ j).mapDerivedCategoryFactors.hom.app
          (((lowerStar Λ f).mapHomologicalComplex (.up ℤ)).obj I) ≫
        DerivedCategory.Q.map
          ((NatTrans.mapHomologicalComplex (directImageOpenRestriction Λ sq) (.up ℤ)).app I) ≫
        ((lowerStar Λ f').rightDerivedFunctorObjQIso
          (((upperStar Λ i).mapHomologicalComplex (.up ℤ)).obj I)).inv

/-- Exact derived restriction along a composite, including its canonical comparison.
Source: blueprint canonicity paragraph (blueprint: lem-sfb-derived-direct-image-open-coherence).
-/
noncomputable def openCoherenceRestrictionComp
    {X Y Z : Scheme.{u}} (i : X ⟶ Y) (j : Y ⟶ Z) :
    (upperStar Λ (i ≫ j)).mapDerivedCategory ≅
      (upperStar Λ j).mapDerivedCategory ⋙ (upperStar Λ i).mapDerivedCategory :=
  Functor.mapDerivedCategoryNatIso (upperStarComp Λ i j) ≪≫
    Functor.mapDerivedCategoryCompIso _ _

/-- Successive open restrictions agree with direct restriction, with the two canonical
restriction-composition comparisons inserted. Equality is stated on components so functor
associators are definitional. Source: blueprint canonicity paragraph
(blueprint: lem-sfb-derived-direct-image-open-coherence). -/
def DirectImageSuccessiveRestriction
    {X Y X' Y' X'' Y'' : Scheme.{u}}
    {f : X ⟶ Y} {j : Y' ⟶ Y} {f' : X' ⟶ Y'} {i : X' ⟶ X}
    {j' : Y'' ⟶ Y'} {f'' : X'' ⟶ Y''} {i' : X'' ⟶ X'}
    (sq : CommSq i f' f j) (sq' : CommSq i' f'' f' j') : Prop :=
  ∀ K : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)),
    (openCoherenceRestrictionComp Λ j' j).hom.app
        ((lowerStar Λ f).rightDerivedFunctor.obj K) ≫
      (upperStar Λ j').mapDerivedCategory.map
        ((derivedDirectImageOpenRestriction Λ sq).app K) ≫
      (derivedDirectImageOpenRestriction Λ sq').app
        ((upperStar Λ i).mapDerivedCategory.obj K) ≫
      (lowerStar Λ f'').rightDerivedFunctor.map
        ((openCoherenceRestrictionComp Λ i' i).inv.app K) =
    (derivedDirectImageOpenRestriction Λ (sq'.horiz_comp sq)).app K

/-- Open restriction commutes with composition of direct images. Components insert
all canonical associators by definitional identification of composite functor objects.
Source: blueprint composition and canonicity paragraphs
(blueprint: lem-sfb-derived-direct-image-open-coherence). -/
def DirectImageRestrictionComposition
    {X Y Z X' Y' Z' : Scheme.{u}}
    {f : X ⟶ Y} {g : Y ⟶ Z} {f' : X' ⟶ Y'} {g' : Y' ⟶ Z'}
    {i : X' ⟶ X} {j : Y' ⟶ Y} {k : Z' ⟶ Z}
    (sqf : CommSq i f' f j) (sqg : CommSq j g' g k) : Prop :=
  ∀ K : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)),
    (upperStar Λ k).mapDerivedCategory.map ((directImageComposition Λ f g).hom.app K) ≫
      (derivedDirectImageOpenRestriction Λ sqg).app
        ((lowerStar Λ f).rightDerivedFunctor.obj K) ≫
      (lowerStar Λ g').rightDerivedFunctor.map
        ((derivedDirectImageOpenRestriction Λ sqf).app K) =
    (derivedDirectImageOpenRestriction Λ (sqf.vert_comp sqg)).app K ≫
      (directImageComposition Λ f' g').hom.app ((upperStar Λ i).mapDerivedCategory.obj K)

/-- The three coherence clauses on the separated finite-type k-schemes of the setting.
Cartesian diagrams are allowed to use any chosen fibre products: their actual projections
are retained, so the statement includes the canonical fibre-product identifications.
Source: blueprint composition proof (blueprint: lem-sfb-derived-direct-image-open-coherence). -/
def DirectImageOpenCoherence (k : Type u) [Field k] : Prop :=
  (∀ (X Y Z T : Over (Spec (.of k)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]
    [LocallyOfFiniteType T.hom] [QuasiCompact T.hom] [IsSeparated T.hom]
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T),
    DirectImageCompositionNormalized Λ f.left g.left ∧
      DirectImageCompositionAssociative Λ f.left g.left h.left) ∧
  (∀ (X Y X' Y' : Over (Spec (.of k)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom] [IsSeparated X'.hom]
    [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom]
    (f : X ⟶ Y) (j : Y' ⟶ Y) (f' : X' ⟶ Y') (i : X' ⟶ X)
    [IsOpenImmersion j.left] [QuasiCompact j.left] [IsOpenImmersion i.left]
    (sq : IsPullback i.left f'.left f.left j.left),
    DirectImageRestrictionNormalized Λ sq.toCommSq) ∧
  (∀ (X Y X' Y' X'' Y'' : Over (Spec (.of k)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom] [IsSeparated X'.hom]
    [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom]
    [LocallyOfFiniteType X''.hom] [QuasiCompact X''.hom] [IsSeparated X''.hom]
    [LocallyOfFiniteType Y''.hom] [QuasiCompact Y''.hom] [IsSeparated Y''.hom]
    (f : X ⟶ Y) (j : Y' ⟶ Y) (f' : X' ⟶ Y') (i : X' ⟶ X)
    (j' : Y'' ⟶ Y') (f'' : X'' ⟶ Y'') (i' : X'' ⟶ X')
    [IsOpenImmersion j.left] [QuasiCompact j.left] [IsOpenImmersion i.left]
    [IsOpenImmersion j'.left] [QuasiCompact j'.left] [IsOpenImmersion i'.left]
    (sq : IsPullback i.left f'.left f.left j.left)
    (sq' : IsPullback i'.left f''.left f'.left j'.left),
    DirectImageSuccessiveRestriction Λ sq.toCommSq sq'.toCommSq) ∧
  (∀ (X Y Z X' Y' Z' : Over (Spec (.of k)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]
    [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom] [IsSeparated X'.hom]
    [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom]
    [LocallyOfFiniteType Z'.hom] [QuasiCompact Z'.hom] [IsSeparated Z'.hom]
    (f : X ⟶ Y) (g : Y ⟶ Z) (f' : X' ⟶ Y') (g' : Y' ⟶ Z')
    (i : X' ⟶ X) (j : Y' ⟶ Y) (a : Z' ⟶ Z)
    [IsOpenImmersion a.left] [QuasiCompact a.left]
    [IsOpenImmersion j.left] [IsOpenImmersion i.left]
    (sqf : IsPullback i.left f'.left f.left j.left)
    (sqg : IsPullback j.left g'.left g.left a.left),
    DirectImageRestrictionComposition Λ sqf.toCommSq sqg.toCommSq)

/-- Derived direct-image comparisons are associative and compatible with open restriction,
for E and for the finite-subextension-valued condensed algebraic closure.
The representative normalizations include identity scheme maps and identity open immersions:
under the canonical site identifications their section maps are identities.

Source: blueprint main-20261015, sk-thm-sf-comp-composition, Composition isomorphism and
Canonicity and associativity; Stacks Tags 08BJ, 070I, 070Y and 0D6E
(blueprint: lem-sfb-derived-direct-image-open-coherence).

Proof plan (the seven steps of the DAG node):
1. Identify internal modules with sheaves of modules over the section-ring sheaf using
   def-weil-pbc-internal-abelian-sheaf-module-equivalence. This preserves sections and
   actions. Exact pullback and its adjunction from sk-def-sfb-module-pushforward-pullback
   and sk-prop-sfb-cartesian-coefficients make every direct image preserve K-injectives
   by lem-weil-pbc-right-adjoint-preserves-kinjective. Exact open extension by zero from
   sk-def-sfb-module-lower-shriek makes open restriction preserve K-injectives as well.
   Resolutions exist by prop-pur-kinjective-resolutions-exist. Work on a single initial I.
2. In lem-weil-pbc-ringed-topoi-derived-pushforward-composition use the identity resolution
   of f_*I. Thus kappa is the class of the inverse underived lowerStarComp. This is the
   universal, unit-preserving derived comparison used in directImageComposition.
   The representative and transition formulas of lem-sf-kinjective-derived-map-computation
   make this computation natural and independent of I, including arbitrary resolutions.
3. For three direct images evaluate both bracketings in degree n at V over the target.
   Both identify the iterated fibre product with V times X. Their projections to V and X
   agree, hence the arrows agree by the fibre-product universal property. Applying the
   contravariant sections functor gives equal chain maps. The coefficient actions agree
   by lem-sfb-eta-comp; the module lifts of def-sfb-finite-lower-star-comp are faithful.
   Localization gives DirectImageCompositionAssociative with its canonical associator.
4. Apply lem-sfb-proetale-open-restriction-counit to the actual pulled-back ring sheaf.
   Transport coefficients through sk-prop-sfb-cartesian-coefficients, using alpha inverse.
   Its counit characterization identifies beta with directImageOpenRestriction, the mate
   of the canonical pullback square. The site object coprojections are bijections. On V,
   beta sends a section along openCoherenceSectionArrow, which fixes V and the source
   projection; this is the identity on I(V times X) under the fibre-product identification.
5. Open restriction of I is K-injective by step 1. Therefore both sides of rho are computed
   by the degreewise beta, which is invertible and commutes with differentials. This gives
   DirectImageRestrictionNormalized and identifies the derived mate with that class.
   Naturality for chain maps and independence under homotopy equivalences follow from
   lem-sf-kinjective-derived-map-computation, so no boundedness hypothesis is needed.
6. For successive opens evaluate both maps in degree n at a test object V. Both are the
   identity on I(V times X) under the displayed coprojections. Iterated coefficient
   restriction is restriction of the same ring sheaf, and both fibre-product maps have
   the same projections. Thus they agree degreewise and after localization. For an
   identity open or identity scheme map the same section computation is the identity.
7. In the composition/restriction square, f_*I and every restricted image remain
   K-injective by step 1. The left path splits the direct image, restricts g, then f;
   the right path first restricts the composite and then splits it. On V each sends a
   section over V times X to that same section on the iterated fibre product. The
   projections to V and X agree, so the maps coincide. Localize and use the transition
   formulas from step 2. This proves DirectImageRestrictionComposition with all the
   specified coefficient actions and canonical fibre-product identifications.
-/
theorem derivedDirectImageOpenCoherence
    (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    (E : PadicAlgCl.FiniteIntermediateField ℓ) :
    DirectImageOpenCoherence (Profinite.continuousMapRingObj E.1) k ∧
      DirectImageOpenCoherence (Profinite.padicAlgClRingObj ℓ) k := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
