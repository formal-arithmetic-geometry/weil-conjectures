/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NR
-/
module

public import Sheaf.Paper.IdentityOpenDerivedAdjunctionNormalization
public import Sheaf.AlgebraicGeometry.ChosenCartesianSquare
public import Sheaf.Paper.LocalizingAdmissibleCoefficients
public import Sheaf.Paper.CondensedModuleDerivedPushpull
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.CategoryTheory.Adjunction.CompositionIso
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import Sheaf.AlgebraicGeometry.CondensedModulePullbackExact
import Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence
import Sheaf.Paper.LocalizeRingedSiteMorphismGeneral
import Sheaf.Paper.CartesianCoefficients
import Sheaf.Algebra.Category.ModuleCat.Sheaf.PullbackLocalizationOfUniverses
import Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
import WeilConjectures.SixFunctors.ProEtale.UpperLowerStar.Defs
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic

/-!
# Underived identity-open normalization and its pullback square

Source: Stacks Project, sites-modules.tex, Tags 04J0 and 03D8;
sites-cohomology.tex, Tag 07A7; blueprint main-20261015,
det-sf-comp-composition-base-change, proof (3)
(blueprint: lem-sfb-identity-open-underived-square-normalization).

The restriction map, section arrows, and inverse pullback compositor are the existing
canonical constructions. The predicate below packages their normalization, including
the tensor-unit section calculation. The square uses exactly the termwise images of
the same compositors, on ordinary unbounded derived categories.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) AddCommGrpCat.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- The sectionwise identity, tensor-unit, unit and adjunct normalizations for the
specified module adjunction on an identity open. The coprojections use the actual
module-adjunction units, hence incorporate the restricted coefficient actions.
The tensor-unit clause sends the localized unit generator `1 ⊗ m` back to `m`.
Source: Stacks 04J0 and 03D8
(blueprint: lem-sfb-identity-open-underived-square-normalization). -/
def IdentityOpenUnderivedNormalization {U D Z : Scheme.{u}}
    (j : U ⟶ Z) (i : U ⟶ D) (h : D ⟶ Z) (hi : i ≫ h = j)
    [IsOpenImmersion j] [IsOpenImmersion i] : Prop :=
  IsIso (identityOpenRestriction Λ j i h hi) ∧
  (∀ V : U.ProEt, IsIso (identityOpenSectionArrow j i h hi V)) ∧
  (∀ (M : Mod (Sheaf (Scheme.ProEt.topology Z) AddCommGrpCat.{u + 1})
      (condensedRingObj Λ Z)) (V : U.ProEt),
    Function.Bijective (openCoherenceSectionCoprojection Λ j M V)) ∧
  (∀ (N : Mod (Sheaf (Scheme.ProEt.topology D) AddCommGrpCat.{u + 1})
      (condensedRingObj Λ D)) (V : U.ProEt),
    Function.Bijective (openCoherenceSectionCoprojection Λ i N V)) ∧
  (∀ (N : Mod (Sheaf (Scheme.ProEt.topology D) AddCommGrpCat.{u + 1})
      (condensedRingObj Λ D)) (V : U.ProEt)
    (s : N.X.obj.obj (op ((Scheme.proEtaleBaseChange h).obj
      ((MorphismProperty.Over.map (f := j) ⊤
        (inferInstance : WeaklyEtale j)).obj V)))),
    ((identityOpenRestriction Λ j i h hi).app N).hom.hom.app (op V)
        (openCoherenceSectionCoprojection Λ j ((lowerStar Λ h).obj N) V s) =
      openCoherenceSectionCoprojection Λ i N V
        (N.X.obj.map (identityOpenSectionArrow j i h hi V).op s)) ∧
  (∀ M : Mod (Sheaf (Scheme.ProEt.topology Z) AddCommGrpCat.{u + 1})
      (condensedRingObj Λ Z),
    (upperStar Λ j).map ((upperStarLowerStarAdjunction Λ h).unit.app M) ≫
        (identityOpenRestriction Λ j i h hi).app ((upperStar Λ h).obj M) =
      (identityOpenPullbackComparison Λ j i h hi).inv.app M) ∧
  (∀ (M : Mod (Sheaf (Scheme.ProEt.topology Z) AddCommGrpCat.{u + 1})
      (condensedRingObj Λ Z))
    (N : Mod (Sheaf (Scheme.ProEt.topology D) AddCommGrpCat.{u + 1})
      (condensedRingObj Λ D)) (t : (upperStar Λ h).obj M ⟶ N),
    (upperStar Λ j).map
        ((upperStarLowerStarAdjunction Λ h).unit.app M ≫ (lowerStar Λ h).map t) ≫
          (identityOpenRestriction Λ j i h hi).app N =
      (identityOpenPullbackComparison Λ j i h hi).inv.app M ≫
        (upperStar Λ i).map t) ∧
  (∀ (M : Mod (Sheaf (Scheme.ProEt.topology Z) AddCommGrpCat.{u + 1})
      (condensedRingObj Λ Z)) (V : U.ProEt)
    (s : M.X.obj.obj (op ((MorphismProperty.Over.map (f := j) ⊤
      (inferInstance : WeaklyEtale j)).obj V))),
    ((identityOpenPullbackComparison Λ j i h hi).hom.app M).hom.hom.app (op V)
        (openCoherenceSectionCoprojection Λ i ((upperStar Λ h).obj M) V
          (((upperStar Λ h).obj M).X.obj.map
            (identityOpenSectionArrow j i h hi V).op
            (((upperStarLowerStarAdjunction Λ h).unit.app M).hom.hom.app
              (op ((MorphismProperty.Over.map (f := j) ⊤
                (inferInstance : WeaklyEtale j)).obj V)) s))) =
      openCoherenceSectionCoprojection Λ j M V s)

/-- The path through the primed identity-open comparison, then theta and t0.
Associators merely identify the displayed iterated pullbacks.
Source: Stacks 03D8 and 07A7
(blueprint: lem-sfb-identity-open-underived-square-normalization). -/
def identityOpenSquareLeft {D Z U D' Z' U' : Scheme.{u}}
    (h : D ⟶ Z) (i : U ⟶ D)
    (v : Z' ⟶ Z) (h' : D' ⟶ Z') (w : D' ⟶ D)
    (vU : U' ⟶ U) (j' : U' ⟶ Z') (i' : U' ⟶ D')
    (hi' : i' ≫ h' = j') (sq : CommSq w h' h v) (hw : vU ≫ i = i' ≫ w) :
    upperStar Λ v ⋙ upperStar Λ j' ≅
      upperStar Λ h ⋙ upperStar Λ i ⋙ upperStar Λ vU :=
  Functor.isoWhiskerLeft _ (identityOpenPullbackComparison Λ j' i' h' hi').symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (openCoherencePullbackSquare Λ sq) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (openCoherencePullbackSquare Λ (CommSq.mk hw))

/-- The path through s and then the unprimed identity-open comparison.
Source: Stacks 03D8 and 07A7
(blueprint: lem-sfb-identity-open-underived-square-normalization). -/
def identityOpenSquareRight {D Z U Z' U' : Scheme.{u}}
    (h : D ⟶ Z) (j : U ⟶ Z) (i : U ⟶ D) (hi : i ≫ h = j)
    (v : Z' ⟶ Z) (vU : U' ⟶ U) (j' : U' ⟶ Z') (sqU : CommSq vU j' j v) :
    upperStar Λ v ⋙ upperStar Λ j' ≅
      upperStar Λ h ⋙ upperStar Λ i ⋙ upperStar Λ vU :=
  openCoherencePullbackSquare Λ sqU ≪≫
    Functor.isoWhiskerRight (identityOpenPullbackComparison Λ j i h hi).symm _ ≪≫
    Functor.associator _ _ _

/-- Underived adjunction normalization over an identity open and compatibility of the
canonical pullback square, including its termwise complex and ordinary derived images.
Source: Stacks 04J0, 03D8 and 07A7; blueprint det-sf-comp-composition-base-change (3)
(blueprint: lem-sfb-identity-open-underived-square-normalization).

Proof plan (the node's nine steps):
1. Identify both open sites with the small slice sites using
lem-weil-proetale-weakly-etale-localization. Use the sectionwise internal-module
equivalence and lem-weil-pbc-localize-ringed-site-morphism. The base-change functor
preserves finite limits; on the identity open it is the identity.
2. The canonical coefficient identifications and lem-sfb-eta-comp make its restricted
structural ring map the identity. Thus c is sectionwise identity with its module action.
3. Apply lem-pur-ringed-site-pullback-localization-universes. On the localized identity
ringed site, pullback is R tensor_R -, the unit is m ↦ 1 tensor m, and the counit is
r tensor n ↦ rn. Thus the restricted unit followed by c is an isomorphism.
4. The conjugate-iso unit equation, with the specified composite adjunction, identifies
that isomorphism with the forward upperStarComp. Its inverse a is the tensor-unit map.
5. Naturality of c, composed with this unit equation, gives the adjunct equation.
6. The two Cartesian squares identify the primed inverse image with U'. Repeat 1--5;
neither properness nor density is used.
7. Conjugate associativity of the sectionwise direct-image compositors using
lem-weil-pbc-mate-pasting and the injective conjugation bijection. Both direct-image
maps preserve all fibre-product projections and the same coefficient action.
8. Reassociate for the triples (i',h',v), (i',w,h) and (vU,i,h), then cancel the common
compositors. This gives the displayed natural square equality.
9. Exact additive pullbacks preserve quasi-isomorphisms. Apply the same comparisons
termwise to complexes and localize at quasi-isomorphisms; their equality is preserved.
No underived direct image is descended termwise here. -/
theorem identity_open_underived_square_normalization
    (ℓ : ℕ) [Fact ℓ.Prime] (hΛ : IsLocalizingAdmissibleCoefficient ℓ Λ)
    (k : Type u) [Field k] (p : ℕ) [CharP k p] (hp : 0 < p) (hpℓ : p ≠ ℓ)
    {D Z U D' Z' U' : Scheme.{u}}
    [D.Over (Spec (.of k))] [Z.Over (Spec (.of k))] [U.Over (Spec (.of k))]
    [D'.Over (Spec (.of k))] [Z'.Over (Spec (.of k))] [U'.Over (Spec (.of k))]
    [LocallyOfFiniteType (D ↘ Spec (.of k))] [QuasiCompact (D ↘ Spec (.of k))]
    [IsSeparated (D ↘ Spec (.of k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of k))] [QuasiCompact (Z ↘ Spec (.of k))]
    [IsSeparated (Z ↘ Spec (.of k))]
    [LocallyOfFiniteType (U ↘ Spec (.of k))] [QuasiCompact (U ↘ Spec (.of k))]
    [IsSeparated (U ↘ Spec (.of k))]
    [LocallyOfFiniteType (D' ↘ Spec (.of k))] [QuasiCompact (D' ↘ Spec (.of k))]
    [IsSeparated (D' ↘ Spec (.of k))]
    [LocallyOfFiniteType (Z' ↘ Spec (.of k))] [QuasiCompact (Z' ↘ Spec (.of k))]
    [IsSeparated (Z' ↘ Spec (.of k))]
    [LocallyOfFiniteType (U' ↘ Spec (.of k))] [QuasiCompact (U' ↘ Spec (.of k))]
    [IsSeparated (U' ↘ Spec (.of k))]
    (h : D ⟶ Z) (j : U ⟶ Z) (i : U ⟶ D)
    [h.IsOver (Spec (.of k))] [j.IsOver (Spec (.of k))] [i.IsOver (Spec (.of k))]
    [IsOpenImmersion j] [QuasiCompact j] [IsOpenImmersion i]
    (hi : i ≫ h = j) (hU : IsPullback i (𝟙 U) h j)
    (v : Z' ⟶ Z) (h' : D' ⟶ Z') (w : D' ⟶ D)
    [v.IsOver (Spec (.of k))] [h'.IsOver (Spec (.of k))] [w.IsOver (Spec (.of k))]
    (sq : ChosenCartesianSquare w h' h v)
    (vU : U' ⟶ U) (j' : U' ⟶ Z') (i' : U' ⟶ D')
    [vU.IsOver (Spec (.of k))] [j'.IsOver (Spec (.of k))] [i'.IsOver (Spec (.of k))]
    [IsOpenImmersion j'] [IsOpenImmersion i']
    (hi' : i' ≫ h' = j') (sqU : ChosenCartesianSquare vU j' j v)
    (hw : vU ≫ i = i' ≫ w) :
    IsPullback i' (𝟙 U') h' j' ∧
    IdentityOpenUnderivedNormalization Λ j i h hi ∧
    IdentityOpenUnderivedNormalization Λ j' i' h' hi' ∧
    (∀ A : Mod (Sheaf (Scheme.ProEt.topology Z) AddCommGrpCat.{u + 1})
        (condensedRingObj Λ Z),
      (identityOpenSquareLeft Λ h i v h' w vU j' i' hi' sq.toCommSq hw).hom.app A =
        (identityOpenSquareRight Λ h j i hi v vU j' sqU.toCommSq).hom.app A) ∧
    (∀ P : CochainComplex
        (Mod (Sheaf (Scheme.ProEt.topology Z) AddCommGrpCat.{u + 1})
          (condensedRingObj Λ Z)) ℤ,
      (NatIso.mapHomologicalComplex
          (identityOpenSquareLeft Λ h i v h' w vU j' i' hi' sq.toCommSq hw)
            (.up ℤ)).hom.app P =
        (NatIso.mapHomologicalComplex
          (identityOpenSquareRight Λ h j i hi v vU j' sqU.toCommSq) (.up ℤ)).hom.app P) ∧
    (∀ A : DerivedCategory
        (Mod (Sheaf (Scheme.ProEt.topology Z) AddCommGrpCat.{u + 1})
          (condensedRingObj Λ Z)),
      (Functor.mapDerivedCategoryNatIso
          (identityOpenSquareLeft Λ h i v h' w vU j' i' hi' sq.toCommSq hw)).hom.app A =
        (Functor.mapDerivedCategoryNatIso
          (identityOpenSquareRight Λ h j i hi v vU j' sqU.toCommSq)).hom.app A) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
