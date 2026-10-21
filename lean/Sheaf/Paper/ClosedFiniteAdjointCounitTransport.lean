module

public import Sheaf.Paper.PurityFiniteSetting
public import Sheaf.AlgebraicGeometry.FixedFiniteExceptionalAt
public import Sheaf.AlgebraicGeometry.EtaleClosedSupportTriangle
public import Sheaf.AlgebraicGeometry.ProEtaleFiniteModules
public import Sheaf.AlgebraicGeometry.ProEtaleSiteComparison
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition
public import WeilConjectures.SixFunctors.ProEtale.UpperLowerStar.ClosedImmersion
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
import Sheaf.AlgebraicGeometry.ComparisonDerivedPullbackFixed
import Sheaf.AlgebraicGeometry.CanonicalCompactSupportSiteComparison
import Sheaf.CategoryTheory.Sites.OrientedClosedBaseLocalization
import Sheaf.AlgebraicGeometry.ProEtaleDirectImageComparison
import Sheaf.AlgebraicGeometry.CompactSupportComparisonUnit
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.CategoryTheory.Localization.Predicate

/-! # Closed finite exceptional inverse image and its counit

Source: blueprint main-20261015, sk-prop-a1, first localization triangle;
Stacks Project, Tags 04CA, 015F, 09A6 and 09BM
(blueprint: lem-pur-closed-finite-adjoint-counit-transport).

The auxiliary definitions are the specified canonical identifications, not additional
choices of functors or adjunctions. The support adjoint is exactly the one used by
`exists_etale_closedSupportTriangle`.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits WeilConjectures

namespace AlgebraicGeometry.ProEtale.ClosedFiniteTransport

/-- Finiteness of the coefficient quotient in the purity conventions.
Source: finite coefficient datum, sk-def-purity-conv
(blueprint: lem-pur-closed-finite-adjoint-counit-transport). -/
instance coefficientFinite (P : PurityFiniteSetting.{u}) : Finite P.Coefficient :=
  haveI : Finite P.Ring := Padic.finite_coefficientExtensionRing
    P.coefficients.l P.extension P.level P.level_pos
  inferInstanceAs (Finite (ULift.{u + 1} P.Ring))

variable (A : Type (u + 1)) [CommRing A] [Finite A]
variable {Z X U : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]

/-- The existing etale compact-support left-adjoint theorem at the identity compactification.
Source: sk-prop-a1 and the ordinary exceptional adjoint
(blueprint: lem-pur-closed-finite-adjoint-counit-transport). -/
instance compactSupportIsLeftAdjoint :
    (Etale.rightDerivedLowerShriekOfCompactification
      (ModuleCat.{u + 1} A) (Compactification.ofIsProper i)).IsLeftAdjoint :=
  Etale.isLeftAdjoint_rightDerivedLowerShriekOfCompactification A
    (Compactification.ofIsProper i)

/-- The canonical identity/proper compactification comparison, on all unbounded objects.
Source: sk-prop-a1, first localization triangle; identity extension by zero, Tag 03S3
(blueprint: lem-pur-closed-finite-adjoint-counit-transport). -/
def compactSupportIso :
    Etale.rightDerivedLowerShriekOfCompactification
        (ModuleCat.{u + 1} A) (Compactification.ofIsProper i) ≅
      (Etale.lowerStar (ModuleCat.{u + 1} A) i).rightDerivedFunctor :=
  Functor.isoWhiskerRight
    (Etale.mapDerivedCategoryOpenImmersionLowerShriekId (ModuleCat.{u + 1} A) Z) _ ≪≫
    Functor.leftUnitor _

/-- The second canonical identification with termwise closed direct image.
Source: Stacks Tags 04CA and 015F, exact closed pushforward
(blueprint: lem-pur-closed-finite-adjoint-counit-transport). -/
def termwiseIso :
    (Etale.lowerStar (ModuleCat.{u + 1} A) i).rightDerivedFunctor ≅
      (Etale.lowerStar (ModuleCat.{u + 1} A) i).mapDerivedCategory :=
  (Etale.lowerStar (ModuleCat.{u + 1} A) i).rightDerivedFunctorIsoMapDerivedCategory

/-- Uniqueness of right adjoints through the specified left-functor identification.
The target is literally the right adjoint of the closed-support triangle.
Source: sk-prop-a1; det-sp-unique-right-adjoint
(blueprint: lem-pur-closed-finite-adjoint-counit-transport). -/
def rightAdjointIso :
    (Etale.rightDerivedLowerShriekOfCompactification
        (ModuleCat.{u + 1} A) (Compactification.ofIsProper i)).rightAdjoint ≅
      (Etale.lowerStar (ModuleCat.{u + 1} A) i).rightDerivedFunctor.rightAdjoint :=
  ((Adjunction.ofIsLeftAdjoint
      (Etale.rightDerivedLowerShriekOfCompactification
        (ModuleCat.{u + 1} A) (Compactification.ofIsProper i))).ofNatIsoLeft
      (compactSupportIso A i)).rightAdjointUniq
    (Adjunction.ofIsLeftAdjoint
      (Etale.lowerStar (ModuleCat.{u + 1} A) i).rightDerivedFunctor)

variable (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
variable (hij : IsCompl (Set.range i.base) (Set.range j.base))

/-- Termwise pro-etale closed direct image, with exactness supplied by the complement.
Source: Stacks Tag 09BM (blueprint: lem-pur-closed-finite-adjoint-counit-transport). -/
def proTermwise :
    DerivedCategory (Sheaf (Scheme.ProEt.topology Z) (ModuleCat.{u + 1} A)) ⥤
      DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)) :=
  haveI := preservesFiniteColimits_lowerStar_of_isCompl (R := A) i j hij
  (lowerStar (ModuleCat.{u + 1} A) i).mapDerivedCategory

/-- The specified closed comparison: descend the underived direct-image comparison
termwise and identify the exact etale derived direct image with its termwise descent.
Source: Stacks Tags 09A6 and 09BM
(blueprint: lem-pur-closed-finite-adjoint-counit-transport). -/
def closedComparison :
    (Etale.lowerStar (ModuleCat.{u + 1} A) i).rightDerivedFunctor ⋙
        (comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory ≅
      (comparisonUpperStar (ModuleCat.{u + 1} A) Z).mapDerivedCategory ⋙
        proTermwise A i j hij :=
  haveI := preservesFiniteColimits_lowerStar_of_isCompl (R := A) i j hij
  haveI := isIso_lowerStarComparisonUpperStarBaseChange i (ModuleCat.{u + 1} A)
  Functor.isoWhiskerRight (termwiseIso A i) _ ≪≫
    (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso
      (asIso (lowerStarComparisonUpperStarBaseChange i (ModuleCat.{u + 1} A))) ≪≫
    Functor.mapDerivedCategoryCompIso _ _

/-- The transported counit obtained by expanding the finite etale-origin Hom bijections.
It uses the comparison inverse, the transported ordinary etale counit, and the actual
comparison-adjunction counit in that order; it asserts no ambient pro-etale adjunction.
Source: sk-prop-a1, first localization triangle; sk-def-sf-operations (vi)
(blueprint: lem-pur-closed-finite-adjoint-counit-transport). -/
def transportedCounit
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A))) :
    (proTermwise A i j hij).obj
        ((sfFiniteExceptionalAt A (Compactification.ofIsProper i)).obj K) ⟶ K :=
  (closedComparison A i j hij).inv.app _ ≫
    (comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.map
      (((Adjunction.ofIsLeftAdjoint
        (Etale.rightDerivedLowerShriekOfCompactification
          (ModuleCat.{u + 1} A) (Compactification.ofIsProper i))).ofNatIsoLeft
          (compactSupportIso A i)).counit.app _) ≫
    (derivedComparisonAdjunction (ModuleCat.{u + 1} A) X).counit.app K

/-- The inverse used in the classical-input comparison is the inverse of the actual unit.
Source: Bhatt--Scholze, Proposition 5.2.6; sk-prop-a1
(blueprint: lem-pur-closed-finite-adjoint-counit-transport). -/
def comparisonUnitIso (T : Scheme.{u})
    (B : DerivedCategory.Plus (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    B.obj ≅ ((comparisonLowerStar (ModuleCat.{u + 1} A) T).rightDerivedFunctor).obj
      (((comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategory).obj B.obj) :=
  haveI := isIso_derivedComparisonAdjunction_unit_app (ModuleCat.{u + 1} A) T B.obj B.property
  asIso ((derivedComparisonAdjunction (ModuleCat.{u + 1} A) T).unit.app B.obj)

/-- Closed compact support, its right adjoint, and the finite exceptional counit agree
with ordinary closed support, without a constructibility hypothesis.

Source: blueprint main-20261015, sk-prop-a1, first localization triangle
(blueprint: lem-pur-closed-finite-adjoint-counit-transport).

Proof, following the six steps of the node:
1. Finite type over the field makes X and Z Noetherian. Closed etale direct image is
   exact (lem-trf-oriented-closed-base-localization). Exact functors preserve cohomology
   and quasi-isomorphisms (lem-sf-exact-functor-derived-triangulated); localization
   uniqueness (lem-weil-pbc-localization-universal-property) identifies their total
   right derived functor with termwise descent. At c=(id,i), identity extension by zero
   is the identity (def-weil-pbc-extension-by-zero). These are compactSupportIso and
   termwiseIso, on the entire unbounded category.
2. Transport the compact-support adjunction through compactSupportIso. Apply
   det-sp-unique-right-adjoint to it and the adjunction of
   lem-exc-closed-support-triangle. This gives rightAdjointIso and its counit equation,
   including uniqueness among all component maps with that equation.
3. If B is in degrees at least a, take T=tau_{<=a-1}(JB). Exactness of i_* makes it
   t-exact, so Hom(i_*T,B)=0 by standard-t-structure orthogonality. Adjunction gives
   Hom(T,JB)=0. The truncation map is therefore zero and is an isomorphism on
   cohomology below a, forcing that cohomology of JB to vanish. Thus JB is bounded below.
4. The actual comparison unit eta_B is invertible on D+ (thm-weil-pbc-site-comparison).
   Put r_B=eta_B^{-1} and beta_B=G(r_B) followed by rightAdjointIso at B.
   The finite exceptional definition is literally nu_Z^* G Rnu_X,*; hence
   alpha_B=nu_Z^*(beta_B) is the asserted natural isomorphism. Exact comparison
   pullback preserves the lower bound (def-sf-comparison-derived-pullback).
5. The canonical direct-image comparison of sk-thm-pe-direct-image-comparison agrees
   with closedComparison: both are the descent of the underived mate and both direct
   images are exact (lem-exc-proetale-closed-exact). At the identity compactification
   it is the inverse of lem-sf-class-compact-support-comparison. Expanding the
   transported Hom bijections gives precisely transportedCounit: lambda^{-1}, then
   nu_X^* of the etale compact-support counit, then the comparison counit.
6. At K=nu_X^*B the comparison triangle identity makes its counit nu_X^*(r_B).
   Naturality of the etale counit and Step 2 identify r_B epsilon_G with
   epsilon_J i_*(beta_B). Substitute in Step 5 and apply naturality of lambda at
   beta_B. The result is the displayed counit equality after alpha_B. Every use of
   comparison full faithfulness in this argument is on bounded-below objects.
-/
theorem closedFiniteAdjointCounitTransport (P : PurityFiniteSetting.{u})
    {Z X U : Scheme.{u}}
    [Z.Over (Spec (.of P.field.k))] [X.Over (Spec (.of P.field.k))]
    [IsSeparated (Z ↘ Spec (.of P.field.k))]
    [IsSeparated (X ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (Z ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    (i : Z ⟶ X) [IsClosedImmersion i] [i.IsOver (Spec (.of P.field.k))]
    (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
    (hij : IsCompl (Set.range i.base) (Set.range j.base)) :
    (∀ B : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient)),
      ((Etale.lowerStar (ModuleCat.{u + 1} P.Coefficient) i).rightDerivedFunctor).map
          ((rightAdjointIso P.Coefficient i).hom.app B) ≫
        (Adjunction.ofIsLeftAdjoint
          ((Etale.lowerStar (ModuleCat.{u + 1} P.Coefficient) i).rightDerivedFunctor)).counit.app
            B =
      (compactSupportIso P.Coefficient i).inv.app
          (((Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} P.Coefficient)
            (Compactification.ofIsProper i)).rightAdjoint).obj B) ≫
        (Adjunction.ofIsLeftAdjoint
          (Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} P.Coefficient)
            (Compactification.ofIsProper i))).counit.app B) ∧
    (∀ B : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient)),
      DerivedCategory.TStructure.t.plus
        ((((Etale.lowerStar (ModuleCat.{u + 1} P.Coefficient)
          i).rightDerivedFunctor).rightAdjoint).obj B.obj)) ∧
    (∃ α :
      (DerivedCategory.Plus.ι ⋙
          (comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) X).mapDerivedCategory ⋙
          sfFiniteExceptionalAt P.Coefficient (Compactification.ofIsProper i)) ≅
        (DerivedCategory.Plus.ι ⋙
          ((Etale.lowerStar (ModuleCat.{u + 1} P.Coefficient) i).rightDerivedFunctor).rightAdjoint ⋙
          (comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) Z).mapDerivedCategory),
      (∀ B : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient)),
        α.hom.app B =
          ((comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) Z).mapDerivedCategory).map
            (((Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} P.Coefficient)
              (Compactification.ofIsProper i)).rightAdjoint).map
                (comparisonUnitIso P.Coefficient X B).inv ≫
              (rightAdjointIso P.Coefficient i).hom.app B.obj)) ∧
      (∀ B : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient)),
        transportedCounit P.Coefficient i j hij
            (((comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) X).mapDerivedCategory).obj
              B.obj) =
          (proTermwise P.Coefficient i j hij).map (α.hom.app B) ≫
            (closedComparison P.Coefficient i j hij).inv.app
              ((((Etale.lowerStar (ModuleCat.{u + 1} P.Coefficient)
                i).rightDerivedFunctor).rightAdjoint).obj B.obj) ≫
            ((comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) X).mapDerivedCategory).map
              ((Adjunction.ofIsLeftAdjoint
                ((Etale.lowerStar (ModuleCat.{u + 1} P.Coefficient)
                  i).rightDerivedFunctor)).counit.app B.obj))) := by
  sorry

end AlgebraicGeometry.ProEtale.ClosedFiniteTransport
