/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group O3
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
public import Sheaf.CategoryTheory.InternalSectionScalarAdjunction
public import Sheaf.AlgebraicGeometry.InternalModuleOperationsTransport
public import Sheaf.Paper.KFlatScalarComparisonNormalization
public import Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
public import Sheaf.CategoryTheory.ExactEquivalenceDerivedSquares
public import Sheaf.Algebra.Homology.ScalarInternalHomData
import Sheaf.CategoryTheory.EquivalenceAdjunctionComparison
import Sheaf.CategoryTheory.Sites.GeometricInverseImageExact
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-! # Internal balanced scalar comparison for an open immersion

Source: blueprint main-20261015, sec-six-functors-basics/sk-prop-scalar-six,
det-prop-scalar-six-pullback.proof.md (1), and the alternative argument in (2).
(blueprint: lem-sfb-open-internal-kflat-mate-normalization).

The transported comparison is specified by its value on flat-term K-flat representatives.
K-flatness and termwise flatness are read through the fixed section reconstruction E.
The ordinary comparison is the published balanced internal scalar/pullback comparison;
internal_section_scalar_adjunction and internal_module_operations_transport identify it
with the inverse balanced section comparison, preserving scalar generators and adjunctions.
The counits below retain the normalization of the published internal derived scalar pair.

## Main declarations

- `ScalarTransport`: normalized comparisons using the existing scalar pair.
- `TransportNormalization`: the complete four-corner transport equation.
- `RepresentativeNormalization`: the inverse balanced comparison on K-flat representatives.
- `normalization`: existence, uniqueness, invertibility, actual mate and unit transpose.
- `theta`: the resulting canonical comparison.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false

universe u c v r w

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.InternalAbelianSheafModule
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale
namespace OpenInternalScalar

section GeneralTransport

variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [UnivLE.{max c v, r}] [HasSheafify J AddCommGrpCat.{r}]
  [(J.W (A := AddCommGrpCat.{r})).IsMonoidal]
  {R S : Sheaf J AddCommGrpCat.{r}}
  [MonObj R] [MonObj S] [IsCommMonObj R] [IsCommMonObj S]
  (b : R ⟶ S) [IsMonHom b]
  [HasDerivedCategory.{w} (Mod (Sheaf J AddCommGrpCat.{r}) R)]
  [HasDerivedCategory.{w} (Mod (Sheaf J AddCommGrpCat.{r}) S)]
  [HasDerivedCategory.{w} (SheafOfModules.scalarModules J (sectionRingSheaf J R))]
  [HasDerivedCategory.{w} (SheafOfModules.scalarModules J (sectionRingSheaf J S))]

/-- Localization of the fixed ordinary scalar-restriction comparison.
Source: blueprint scalar-six pullback proof (1)
(blueprint: lem-sfb-open-internal-kflat-mate-normalization). -/
def restrictionComparison
    (r : Mod.comap b ⋙ (sectionModuleEquivalence J R).functor ≅
      (sectionModuleEquivalence J S).functor ⋙
        SheafOfModules.scalarRestriction (sectionScalarMap.{r, c, v} J b)) :=
  (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso r ≪≫ Functor.mapDerivedCategoryCompIso _ _

/-- The fixed section reconstruction comparisons with the actual internal adjunction.
Restriction is identity on sections. Mate normalization fixes all Hom bijections,
units and counits. The existing section pair retains its K-flat universal counit.
Source: lem-sfb-internal-section-scalar-adjunction, Stacks 03EK and 07A6
(blueprint: lem-sfb-open-internal-kflat-mate-normalization). -/
def ScalarTransport
    (L : DerivedCategory (Mod (Sheaf J AddCommGrpCat.{r}) R) ⥤
      DerivedCategory (Mod (Sheaf J AddCommGrpCat.{r}) S))
    (adj : L ⊣ (Mod.comap b).mapDerivedCategory) :=
  Σ pair : SheafOfModules.ScalarDerivedPair.{c, v, r, w} (sectionScalarMap.{r, c, v} J b),
  Σ restriction : Mod.comap b ⋙ (sectionModuleEquivalence J R).functor ≅
    (sectionModuleEquivalence J S).functor ⋙
      SheafOfModules.scalarRestriction (sectionScalarMap.{r, c, v} J b),
  { comparison : L ⋙ (sectionModuleEquivalence J S).functor.mapDerivedCategory ≅
      (sectionModuleEquivalence J R).functor.mapDerivedCategory ⋙ pair.derived //
    (∀ (N : Mod (Sheaf J AddCommGrpCat.{r}) S) (W : Cᵒᵖ) (x : N.X.obj.obj W),
      (restriction.hom.app N).val.app W x = x) ∧
    (mateEquiv adj pair.adjunction comparison.inv).natTrans =
      (restrictionComparison J b restriction).hom }

end GeneralTransport

variable {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
  (a : Λ ⟶ Λ') [IsMonHom a]

/-- The existing universal internal derived scalar extension, with no flatness assumption.
Source: blueprint scalar-six pullback proof (1)
(blueprint: lem-sfb-open-internal-kflat-mate-normalization). -/
abbrev extension (T : Scheme.{u}) :=
  (Mod.extendScalars (coefficientMap a T)).leftDerivedFunctor

/-- The specified internal scalar adjunction, including its actual unit and counit.
Source: blueprint scalar-six pullback proof (1)
(blueprint: lem-sfb-open-internal-kflat-mate-normalization). -/
abbrev adjunction (T : Scheme.{u}) :=
  Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a T)

/-- The cochain counit of the existing internal universal derived pair.
Source: blueprint scalar-six pullback proof (1); Stacks 06YY
(blueprint: lem-sfb-open-internal-kflat-mate-normalization). -/
abbrev counit (T : Scheme.{u}) :=
  derivedCochainCounit (Mod.extendScalars (coefficientMap a T)) (extension a T)
    (Mod.extendScalars (coefficientMap a T)).leftDerivedFunctorCounit

/-- Specialization of the normalized reconstruction data to the coefficient sheaves.
Source: blueprint scalar-six pullback (1)
(blueprint: lem-sfb-open-internal-kflat-mate-normalization). -/
abbrev scalarTransport (T : Scheme.{u})
    [HasDerivedCategory.{u + 1} (SheafOfModules.{u + 1} (InternalModuleOperations.ring Λ T))]
    [HasDerivedCategory.{u + 1} (SheafOfModules.{u + 1} (InternalModuleOperations.ring Λ' T))] :=
  ScalarTransport (Scheme.ProEt.topology T) (coefficientMap a T)
    (extension a T) (adjunction a T)

variable {U X : Scheme.{u}} (j : U ⟶ X)
  [HasDerivedCategory.{u + 1} (SheafOfModules.{u + 1} (InternalModuleOperations.ring Λ U))]
  [HasDerivedCategory.{u + 1} (SheafOfModules.{u + 1} (InternalModuleOperations.ring Λ X))]
  [HasDerivedCategory.{u + 1} (SheafOfModules.{u + 1} (InternalModuleOperations.ring Λ' U))]
  [HasDerivedCategory.{u + 1} (SheafOfModules.{u + 1} (InternalModuleOperations.ring Λ' X))]

section Transport

variable
  [(InternalModuleOperations.upperStar Λ j).Additive]
  [(InternalModuleOperations.upperStar Λ' j).Additive]
  [PreservesFiniteLimits (InternalModuleOperations.upperStar Λ j)]
  [PreservesFiniteColimits (InternalModuleOperations.upperStar Λ j)]
  [PreservesFiniteLimits (InternalModuleOperations.upperStar Λ' j)]
  [PreservesFiniteColimits (InternalModuleOperations.upperStar Λ' j)]

/-- The localization of the published pullback comparison, with its canonical associators.
Source: lem-sfb-internal-module-operations-transport; blueprint scalar-six pullback (1)
(blueprint: lem-sfb-open-internal-kflat-mate-normalization). -/
def pullbackComparison :
    (CondensedRing.upperStar Λ j).mapDerivedCategory ⋙
        (InternalModuleOperations.equivalence Λ U).functor.mapDerivedCategory ≅
      (InternalModuleOperations.equivalence Λ X).functor.mapDerivedCategory ⋙
        (InternalModuleOperations.upperStar Λ j).mapDerivedCategory :=
  (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso (InternalModuleOperations.upperComparison Λ j) ≪≫
      Functor.mapDerivedCategoryCompIso _ _

/-- The section action square, obtained by descent through E_BX of the fixed restriction
square. Its restriction and pullback comparisons are the termwise localizations, so on
ordinary representatives this is the identity after the balanced alpha collapses.
The preimage is taken through a fully faithful equivalence, not chosen arbitrarily.
Source: blueprint scalar-six pullback (1), action-square calculation
(blueprint: lem-sfb-open-internal-kflat-mate-normalization). -/
def sectionAction (sX : scalarTransport a X) (sU : scalarTransport a U) :
    SheafOfModules.scalarDerivedRestriction
        (sectionScalarMap.{u + 1, u + 1, u} (Scheme.ProEt.topology X) (coefficientMap a X)) ⋙
        (InternalModuleOperations.upperStar Λ j).mapDerivedCategory ≅
      (InternalModuleOperations.upperStar Λ' j).mapDerivedCategory ⋙
        SheafOfModules.scalarDerivedRestriction
          (sectionScalarMap.{u + 1, u + 1, u} (Scheme.ProEt.topology U) (coefficientMap a U)) :=
  ((Functor.whiskeringLeft _ _ _).obj
    (InternalModuleOperations.equivalence Λ' X).functor.mapDerivedCategory).preimageIso
    ((Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (restrictionComparison (Scheme.ProEt.topology X)
        (coefficientMap a X) sX.2.1).symm _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (pullbackComparison (Λ := Λ) j).symm ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (CondensedRing.derivedComapUpperStarIso a j).symm _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (restrictionComparison (Scheme.ProEt.topology U)
        (coefficientMap a U) sU.2.1) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (pullbackComparison (Λ := Λ') j) _ ≪≫
      Functor.associator _ _ _)

/-- The specified sectionwise inverse mate. The K-flat scalar comparison theorem identifies
this map with the inverse localized balanced comparison, for the same scalar pairs.
Source: lem-sfb-kflat-scalar-comparison-normalization; blueprint scalar-six pullback (1)
(blueprint: lem-sfb-open-internal-kflat-mate-normalization). -/
def sectionTheta (sX : scalarTransport a X) (sU : scalarTransport a U) :=
  SheafOfModules.ScalarPullback.mate sX.1.adjunction sU.1.adjunction
    (sectionAction a j sX sU).hom

end Transport

/-- The actual four-corner transport equation under the fixed section equivalences.
Exactness is asserted, not assumed, for the section pullbacks. ScalarTransport fixes
restriction on sections and the derived adjunction comparisons, including units/counits.
The sectionTheta is the inverse balanced K-flat comparison via its canonical action square.
Source: blueprint scalar-six pullback (1), transfer to internal modules
(blueprint: lem-sfb-open-internal-kflat-mate-normalization). -/
def TransportNormalization
    (θ : (CondensedRing.upperStar Λ j).mapDerivedCategory ⋙ extension a U ⟶
      extension a X ⋙ (CondensedRing.upperStar Λ' j).mapDerivedCategory) : Prop :=
  ∃ (_ : (InternalModuleOperations.upperStar Λ j).Additive)
    (_ : (InternalModuleOperations.upperStar Λ' j).Additive)
    (_ : PreservesFiniteLimits (InternalModuleOperations.upperStar Λ j))
    (_ : PreservesFiniteColimits (InternalModuleOperations.upperStar Λ j))
    (_ : PreservesFiniteLimits (InternalModuleOperations.upperStar Λ' j))
    (_ : PreservesFiniteColimits (InternalModuleOperations.upperStar Λ' j)),
  ∃ (sX : scalarTransport a X) (sU : scalarTransport a U),
  ∀ V : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)),
    (InternalModuleOperations.equivalence Λ' U).functor.mapDerivedCategory.map (θ.app V) ≫
        (pullbackComparison (Λ := Λ') j).hom.app ((extension a X).obj V) ≫
        (InternalModuleOperations.upperStar Λ' j).mapDerivedCategory.map
          (sX.2.2.val.hom.app V) =
      sU.2.2.val.hom.app ((CondensedRing.upperStar Λ j).mapDerivedCategory.obj V) ≫
        sU.1.derived.map ((pullbackComparison (Λ := Λ) j).hom.app V) ≫
        (sectionTheta a j sX sU).app
          ((InternalModuleOperations.equivalence Λ X).functor.mapDerivedCategory.obj V)

/-- The defining representative equation for the transport of the inverse balanced
section comparison. Both sides retain all localization counits and exact-pullback
factorizations. The fixed E_X determines the flat-term K-flat representatives.
Reconstruction preserves the generators of ordinary extension and the pullback comparison,
so the published pullIso is the internal form of chi_j inverse.
Source: blueprint scalar-six pullback proof (1)
(blueprint: lem-sfb-open-internal-kflat-mate-normalization). -/
def RepresentativeNormalization
    (θ : (CondensedRing.upperStar Λ j).mapDerivedCategory ⋙ extension a U ⟶
      extension a X ⋙ (CondensedRing.upperStar Λ' j).mapDerivedCategory) : Prop :=
  ∀ (P : CochainComplex
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) ℤ),
    CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
      (R := sectionRingSheaf.{u + 1, u + 1, u}
        (Scheme.ProEt.topology X) (condensedRingObj Λ X))
      (((InternalModuleOperations.equivalence Λ X).functor.mapHomologicalComplex
        (.up ℤ)).obj P) →
    (∀ n : ℤ, SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1}
      (J := Scheme.ProEt.topology X)
      (R := sectionRingSheaf.{u + 1, u + 1, u}
        (Scheme.ProEt.topology X) (condensedRingObj Λ X))
      ((InternalModuleOperations.equivalence Λ X).functor.obj (P.X n))) →
    θ.app (DerivedCategory.Q.obj P) ≫
        (CondensedRing.upperStar Λ' j).mapDerivedCategory.map ((counit a X).app P) ≫
        (CondensedRing.upperStar Λ' j).mapDerivedCategoryFactors.hom.app
          (((Mod.extendScalars (coefficientMap a X)).mapHomologicalComplex (.up ℤ)).obj P) =
      (extension a U).map ((CondensedRing.upperStar Λ j).mapDerivedCategoryFactors.hom.app P) ≫
        (counit a U).app
          (((CondensedRing.upperStar Λ j).mapHomologicalComplex (.up ℤ)).obj P) ≫
        DerivedCategory.Q.map
          ((NatIso.mapHomologicalComplex (CondensedRing.pullIso a j) (.up ℤ)).hom.app P)

/-- The transported balanced K-flat comparison exists uniquely, is invertible on all
unbounded objects, and is the mate for the specified internal scalar adjunctions.
The last equation is its specified transpose, with those adjunctions' actual units.
Source: blueprint scalar-six pullback proof (1), and alternative open-adjunction
argument in (2) (blueprint: lem-sfb-open-internal-kflat-mate-normalization).

Proof:
1. Collapse the pullback tensor along alpha_R by x tensor m ↦ alpha_R inverse(x)m,
with inverse m ↦ 1 tensor m. Alpha is an isomorphism (lem-sfb-alpha-iso), so the
pullbacks are exact. Use lem-trf-geometric-inverse-image-exact and
lem-weil-pbc-exact-functor-derived-factorization to localize them termwise.
2. The fixed section equivalences and scalar comparisons of
lem-sfb-internal-section-scalar-adjunction preserve the ordinary balanced generators
and the full specified derived adjunctions. The fixed pullback comparisons of
lem-sfb-internal-module-operations-transport localize termwise. In particular these
are the normalized left comparisons in lem-sfb-equivalence-square-inverse-mate-coherence.
3. The two routes around the restriction comparison square are the identity after
these collapses. Their A_U-actions agree by
map_coefficientMap_comp_condensedPullbackHom (sk-def-sfb-coefficient-change).
Thus the actual internal restriction identification is derivedComapUpperStarIso inverse.
4. Apply lem-sfb-kflat-scalar-comparison-normalization on the section side to j inverse
image and the alpha-identified rings. It gives the inverse balanced comparison on
flat-term K-flat representatives and invertibility on the entire unbounded category.
Use the equivalent site presentation with lifted homs when applying its same-universe
site API. Transport by E and its fixed scalar/pullback comparisons. Preservation of generators
identifies its representative equation with RepresentativeNormalization above.
5. Apply part (3) of lem-sfb-equivalence-square-inverse-mate-coherence to the restriction
square from step 3. Faithfulness identifies the transported transformation with the
inverse mate of d. All comparison maps are invertible, so it is invertible. K-flat
resolutions determine a transformation with the displayed representative equation
uniquely; no flatness of a, or boundedness, is used.
6. The inverse-mate formula is T_U R_A eta_X, followed by T_U d, followed by the
specified counit epsilon_U. Naturality of the specified eta_U and the right-adjoint
triangle identity contract its transpose to R_A eta_X followed by d. -/
theorem normalization [IsOpenImmersion j] :
    ∃! θ : (CondensedRing.upperStar Λ j).mapDerivedCategory ⋙ extension a U ⟶
        extension a X ⋙ (CondensedRing.upperStar Λ' j).mapDerivedCategory,
      RepresentativeNormalization a j θ ∧ TransportNormalization a j θ ∧ IsIso θ ∧
      (mateEquiv (adjunction a X) (adjunction a U) (.mk _ _ _ _ θ)).natTrans =
        (CondensedRing.derivedComapUpperStarIso a j).inv ∧
      ∀ V : DerivedCategory
          (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)),
        (adjunction a U).unit.app ((CondensedRing.upperStar Λ j).mapDerivedCategory.obj V) ≫
            (Mod.comap (coefficientMap a U)).mapDerivedCategory.map (θ.app V) =
          (CondensedRing.upperStar Λ j).mapDerivedCategory.map ((adjunction a X).unit.app V) ≫
            (CondensedRing.derivedComapUpperStarIso a j).inv.app ((extension a X).obj V) := by
  sorry

/-- The canonical transported inverse balanced comparison, fixed uniquely by the full
representative and reconstruction equations of `normalization`. Its data come from a
uniquely determining characterization, not a bare existence of a map or an isomorphism.
Source: blueprint scalar-six pullback (1)
(blueprint: lem-sfb-open-internal-kflat-mate-normalization). -/
def theta [IsOpenImmersion j] :
    (CondensedRing.upperStar Λ j).mapDerivedCategory ⋙ extension a U ⟶
      extension a X ⋙ (CondensedRing.upperStar Λ' j).mapDerivedCategory :=
  (normalization a j).exists.choose

end OpenInternalScalar
end AlgebraicGeometry.ProEtale
