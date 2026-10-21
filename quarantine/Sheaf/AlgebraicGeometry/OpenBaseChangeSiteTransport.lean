module

public import Sheaf.AlgebraicGeometry.ProEtaleFiniteModules
public import Sheaf.AlgebraicGeometry.FiniteConstantCoefficientTransport
public import Sheaf.AlgebraicGeometry.FiniteOpenBaseChangeNormalized
public import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekBaseChange
public import Sheaf.AlgebraicGeometry.Etale.DerivedExtensionZeroBaseChange
public import Sheaf.AlgebraicGeometry.OpenComparisonUnitNormalization
public import Sheaf.AlgebraicGeometry.ProEtaleConstantExact
public import Sheaf.AlgebraicGeometry.ProEtaleExtensionZero
public import Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence
public import Sheaf.SixFunctors.OpenTensorNormalization
public import WeilConjectures.AlgebraicGeometry.EtaleInverseImageExact
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.BaseChangeSquare
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs

@[expose] public section

/-!
# Site transport for open base change

Source: literature/stacks-project/proetale.tex, Tag 09AF (blueprint:
lem-trf-open-base-change-site-transport).
-/

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.StrictTower

set_option autoImplicit false

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
  [TopologicalSpace Λ] [DiscreteTopology Λ]
variable {U' U Z' Z : Scheme.{u}}
variable (r : U' ⟶ U) (j' : U' ⟶ Z') (j : U ⟶ Z) (q : Z' ⟶ Z)
variable [IsOpenImmersion j] [IsOpenImmersion j']

/-- The canonical derived site comparison for extension by zero, obtained from the
unit-normalized finite-coefficient transport
(blueprint: lem-trf-open-base-change-site-transport). -/
noncomputable def derivedOpenComparison {V W : Scheme.{u}} (i : V ⟶ W)
    [IsOpenImmersion i] :
    (Etale.openImmersionLowerShriek (ModuleCat.{u + 1} Λ) i).mapDerivedCategory ⋙
        (H Λ W Λ (RingHom.id Λ)).mapDerivedCategory ≅
      (H Λ V Λ (RingHom.id Λ)).mapDerivedCategory ⋙
        (moduleJ Λ i).mapDerivedCategory :=
  (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso
      (@asIso _ _ _ _ (hOpen Λ i Λ (RingHom.id Λ))
        (hOpen_isIso Λ i Λ (RingHom.id Λ))) ≪≫
    Functor.mapDerivedCategoryCompIso _ _

/-- The canonical inverse derived pullback comparison, obtained from the inverse mate
of the site-comparison direct-image map (blueprint: lem-trf-open-base-change-site-transport). -/
noncomputable def derivedPullbackComparison {V W : Scheme.{u}} (f : V ⟶ W) :
    (Etale.upperStar (ModuleCat.{u + 1} Λ) f).mapDerivedCategory ⋙
        (H Λ V Λ (RingHom.id Λ)).mapDerivedCategory ≅
      (H Λ W Λ (RingHom.id Λ)).mapDerivedCategory ⋙
        (modulePullback Λ f).mapDerivedCategory :=
  (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    (Functor.mapDerivedCategoryNatIso
      (@asIso _ _ _ _ (hPullbackInv Λ f Λ (RingHom.id Λ))
        (hPullbackInv_isIso Λ f Λ (RingHom.id Λ)))).symm ≪≫
    Functor.mapDerivedCategoryCompIso _ _

/-- The site comparison intertwines the two canonical open base-change maps
(blueprint: lem-trf-open-base-change-site-transport).

The proof proceeds in the ordinary bounded-below derived categories. First, exactness of
inverse image and extension by zero lets the named sheaf maps descend termwise. The
finite-coefficient transport supplies the unit-normalized open comparison and its inverse
pullback mate. The cartesian square gives the etale open base-change isomorphism, while
`singleBeta` is the canonical pro-etale one. Expanding both composites under the two open
adjunctions gives the same mate: the pullback comparison, the open unit, and the cartesian
comparison occur in the same order. The mate bijection then identifies the actual derived
morphisms, including the identity and empty-open cases. -/
theorem openBaseChangeSiteTransport
    [QuasiCompact r] [QuasiSeparated r] [QuasiCompact j'] [QuasiSeparated j']
    [QuasiCompact j] [QuasiSeparated j] [QuasiCompact q] [QuasiSeparated q]
    [IsNoetherian U'] [IsNoetherian U] [IsNoetherian Z'] [IsNoetherian Z]
    (sq : IsPullback r j' j q)
    (M : DerivedCategory.Plus
      (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (derivedPullbackComparison Λ q).hom.app
        ((Etale.openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j).mapDerivedCategory.obj
          (DerivedCategory.Plus.ι.obj M)) ≫
      (modulePullback Λ q).mapDerivedCategory.map
        ((derivedOpenComparison Λ j).hom.app (DerivedCategory.Plus.ι.obj M)) ≫
      (singleBeta Λ r j' j q sq.toCommSq.w sq).hom.app
        ((H Λ U Λ (RingHom.id Λ)).mapDerivedCategory.obj
          (DerivedCategory.Plus.ι.obj M)) =
    (H Λ Z' Λ (RingHom.id Λ)).mapDerivedCategory.map
        ((Etale.mapDerivedCategoryOpenImmersionLowerShriekBaseChangeIso
          (ModuleCat.{u + 1} Λ) sq).inv.app (DerivedCategory.Plus.ι.obj M)) ≫
      (derivedOpenComparison Λ j').hom.app
        ((Etale.upperStar (ModuleCat.{u + 1} Λ) r).mapDerivedCategory.obj
          (DerivedCategory.Plus.ι.obj M)) ≫
      (moduleJ Λ j').mapDerivedCategory.map
        ((derivedPullbackComparison Λ r).hom.app
          (DerivedCategory.Plus.ι.obj M)) := by
  sorry

end AlgebraicGeometry.ProEtale.StrictTower

