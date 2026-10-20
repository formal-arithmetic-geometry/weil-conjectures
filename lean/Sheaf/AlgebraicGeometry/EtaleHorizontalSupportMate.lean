module

public import Sheaf.AlgebraicGeometry.UnboundedEtaleCompactSupportComparisons
public import Sheaf.AlgebraicGeometry.QuasiFiniteCompactSupportExact
public import Sheaf.AlgebraicGeometry.EtaleAmbientAdjointLocality
public import Sheaf.AlgebraicGeometry.CompactifiableOverField
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.FreeSheaf
public import WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMap
public import WeilConjectures.Compactification.Refinement
public import WeilConjectures.Compactification.RefinementCategory
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.RingTheory.Noetherian.Defs
import Sheaf.AlgebraicGeometry.EtaleShriekOpenExchangeAdjoint
import Sheaf.AlgebraicGeometry.EtaleSupportMapCompatibility

/-!
# Etale horizontal compact-support exchange is the composition mate

Source: literature/stacks-project/more-etale.tex, Tags 0F7J and 0F7K
(blueprint: lem-pur-etale-horizontal-support-mate).
-/

set_option autoImplicit false
set_option warn.sorry false

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

/-- The compactification-independent proper-support comparison for an etale map.
Source: literature/stacks-project/more-etale.tex, Tags 0F4L and 0GKM
(blueprint: lem-pur-etale-horizontal-support-mate). -/
noncomputable def etaleCanonicalCompactSupportComparison
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {U V : Scheme.{u}} (e : U ⟶ V) [Etale e] [IsSeparated e]
    [IsLocallyNoetherian U] [CompactSpace U]
    [IsLocallyNoetherian V] [CompactSpace V]
    [QuasiCompact e] [HasCompactification e]
    (N : EtaleCompactSupportNormalization A) :
    rightDerivedLowerShriek (ModuleCat.{u + 1} A) e ≅
      (etaleLowerShriek (ModuleCat.{u + 1} A) e inferInstance).mapDerivedCategory :=
  (rightDerivedLowerShriekIso A (HasCompactification.compactification e)).symm ≪≫
    N.comparison e (HasCompactification.compactification e)

/-- The specified composition mate built from the normalized compact-support comparisons.
Source: literature/stacks-project/more-etale.tex, Tags 0F7J and 0F7K
(blueprint: lem-pur-etale-horizontal-support-mate). -/
noncomputable def etaleHorizontalSupportMateDelta
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X X' Y Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {v : Y' ⟶ Y} {v' : X' ⟶ X}
    [IsLocallyNoetherian X] [CompactSpace X]
    [IsLocallyNoetherian X'] [CompactSpace X']
    [IsLocallyNoetherian Y] [CompactSpace Y]
    [IsLocallyNoetherian Y'] [CompactSpace Y']
    [HasCompactification f] [HasCompactification f']
    [Etale v] [Etale v'] [IsSeparated v] [IsSeparated v']
    [LocallyOfFiniteType v] [LocallyOfFiniteType v']
    [HasCompactification v] [HasCompactification v']
    [HasCompactification (v' ≫ f)] [HasCompactification (f' ≫ v)]
    [QuasiCompact f] [QuasiCompact f'] [QuasiCompact v] [QuasiCompact v']
    [QuasiCompact (v' ≫ f)] [QuasiCompact (f' ≫ v)]
    (sq : IsPullback v' f' f v)
    (N : EtaleCompactSupportNormalization A) :
    (etaleLowerShriek (ModuleCat.{u + 1} A) v' inferInstance).mapDerivedCategory ⋙
        rightDerivedLowerShriek (ModuleCat.{u + 1} A) f ≅
      rightDerivedLowerShriek (ModuleCat.{u + 1} A) f' ⋙
        (etaleLowerShriek (ModuleCat.{u + 1} A) v inferInstance).mapDerivedCategory :=
  Functor.isoWhiskerRight
      (etaleCanonicalCompactSupportComparison A v' N).symm
      (rightDerivedLowerShriek (ModuleCat.{u + 1} A) f) ≪≫
    unboundedEtaleLowerShriekCompIso A v' f ≪≫
    unboundedEtaleLowerShriekCongr A sq.toCommSq.w ≪≫
    (unboundedEtaleLowerShriekCompIso A f' v).symm ≪≫
    Functor.isoWhiskerLeft
      (rightDerivedLowerShriek (ModuleCat.{u + 1} A) f')
      (etaleCanonicalCompactSupportComparison A v N)

/-- The specified unbounded compact-support exchange `C_{f,v} : v^* Rf_! ≅ Rf'_! v'^*` as an
isomorphism; its `hom` is the recorded exchange and its `inv` is `C_{f,v}⁻¹`.
Source: literature/stacks-project/more-etale.tex, Tags 0F7J and 0F7L
(blueprint: lem-pur-etale-horizontal-support-mate). -/
noncomputable def etaleHorizontalSupportBaseChangeIso
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X X' Y Y' : Scheme.{u}}
    [IsNoetherian X] [IsNoetherian X'] [IsNoetherian Y] [IsNoetherian Y']
    {f : X ⟶ Y} {f' : X' ⟶ Y'} {v : Y' ⟶ Y} {v' : X' ⟶ X}
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [HasCompactification f] [HasCompactification f'] [QuasiCompact f']
    (sq : IsPullback v' f' f v) :
    rightDerivedLowerShriek (ModuleCat.{u + 1} A) f ⋙
        (upperStar (ModuleCat.{u + 1} A) v).mapDerivedCategory ≅
      (upperStar (ModuleCat.{u + 1} A) v').mapDerivedCategory ⋙
        rightDerivedLowerShriek (ModuleCat.{u + 1} A) f' := by
  haveI : IsIso (unboundedEtaleCompactSupportBaseChange A sq) :=
    (unboundedEtaleCompactSupport_baseChange A sq).1
  exact asIso (unboundedEtaleCompactSupportBaseChange A sq)

/-- The counit identity for the composition mate of compact-support exchange.
Source: literature/stacks-project/more-etale.tex, Tags 0F7J and 0F7K
(blueprint: lem-pur-etale-horizontal-support-mate).

The proof follows the normalized mate calculation. First transport the sum/evaluation
adjunction across the proper-support comparisons. Next expand the inverse of the
composition mate and reduce the assertion to the diagonal square. The intermediate
fibre products and diagonal sections are separated etale finite-type maps, so the
specified compactifications and comparison maps apply. Identify the diagonal insertion
with the unit of the transported adjunction using the sum-extension description.
Apply the open-horizontal mate identity to the diagonal square, then use naturality and
associativity of the specified composition and exchange maps. The resulting composite
is the identity by the triangle identity for the transported adjunction. Invertibility
of the exchange gives the required adjunct formula for every unbounded complex.
-/
theorem etaleHorizontalSupportMate
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X X' Y Y' : Scheme.{u}}
    [IsNoetherian X] [IsNoetherian X'] [IsNoetherian Y] [IsNoetherian Y']
    {f : X ⟶ Y} {f' : X' ⟶ Y'} {v : Y' ⟶ Y} {v' : X' ⟶ X}
    [IsSeparated f] [IsSeparated f'] [IsSeparated v] [IsSeparated v']
    [Etale v] [Etale v'] [LocallyOfFiniteType f] [LocallyOfFiniteType f']
    [LocallyOfFiniteType v] [LocallyOfFiniteType v']
    [QuasiCompact f] [QuasiCompact f'] [QuasiCompact v] [QuasiCompact v']
    [HasCompactification f] [HasCompactification f'] [HasCompactification v]
    [HasCompactification v'] [HasCompactification (v' ≫ f)]
    [HasCompactification (f' ≫ v)] [QuasiCompact (v' ≫ f)]
    [QuasiCompact (f' ≫ v)] (sq : IsPullback v' f' f v)
    (N : EtaleCompactSupportNormalization A) :
    ∀ (M : DerivedCategoryModule A X),
      (etaleHorizontalSupportMateDelta A sq N).inv.app
          ((upperStar (ModuleCat.{u + 1} A) v').mapDerivedCategory.obj M) ≫
        (rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).map
          ((derivedEtaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) v'
            inferInstance).counit.app M) =
        (etaleLowerShriek (ModuleCat.{u + 1} A) v inferInstance).mapDerivedCategory.map
          ((etaleHorizontalSupportBaseChangeIso A sq).inv.app M) ≫
      (derivedEtaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) v
        inferInstance).counit.app
          ((rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).obj M) := by
  sorry

end AlgebraicGeometry.Etale
