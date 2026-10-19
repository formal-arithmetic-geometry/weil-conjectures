/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q129
-/
module

public import Sheaf.Paper.PurityFiniteSetting
public import Sheaf.Paper.GlobalFiniteLevelCompactSupportBaseChange
public import Sheaf.AlgebraicGeometry.CompactSupportFiniteTorsion
public import Sheaf.AlgebraicGeometry.CanonicalCompactSupportSiteComparison
public import Sheaf.AlgebraicGeometry.ComparisonDerivedPullbackFixed
public import Sheaf.AlgebraicGeometry.CompactSupportComparisonUnit
public import Sheaf.AlgebraicGeometry.FixedFiniteExceptionalAt
import Sheaf.AlgebraicGeometry.FiniteComparisonClassAdjunction
import Mathlib.CategoryTheory.Adjunction.Mates
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint
import Sheaf.AlgebraicGeometry.SpecifiedExceptionalClassHom
import Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence
import Sheaf.Paper.CanonicalFiniteLevelCompactSupportBaseChange
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekPlusBaseChange

/-! # The normalized exceptional mate under site comparison

Source: literature/blueprint/main-20261015/blueprint/sec-smooth-purity/sk-prop-an/
thm-pur-affine-line-purity.proof.md, actual-adjoint comparison and final base-change
sentences (blueprint: lem-pur-exceptional-mate-site-comparison).

All constructions use the ordinary constant-coefficient categories. The etale right
adjoints are written on their bounded-below domains, as assumed in the node. The
relative transpose is the specified Hom chain, including its witness conjugation.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.ProEtale

/-- Finiteness of the finite purity quotient, from the recorded coefficient theorem.
Source: purity conventions (blueprint: lem-pur-exceptional-mate-site-comparison). -/
instance exceptionalMateRingFinite (D : WeilConjectures.PurityFiniteSetting.{u}) :
    Finite D.Ring :=
  Padic.finite_coefficientExtensionRing D.coefficients.l D.extension D.level D.level_pos

/-- The standard size lift preserves finiteness of the coefficient quotient.
Source: purity conventions (blueprint: lem-pur-exceptional-mate-site-comparison). -/
instance exceptionalMateCoeffFinite (D : WeilConjectures.PurityFiniteSetting.{u}) :
    Finite D.Coefficient :=
  @Finite.of_equiv (ULift.{u + 1} D.Ring) D.Ring (exceptionalMateRingFinite D) Equiv.ulift.symm

/-- The bounded-below coordinates of the finite exceptional functor C_X R U_Y.
Here R is the chosen ordinary etale right adjoint, restricted to D+. This is the
same composite as `sfFiniteExceptionalAt`, expressed with the chosen adjunction
rather than its noncomputably chosen representative.
Source: actual-adjoint comparison (blueprint: lem-pur-exceptional-mate-site-comparison). -/
def exceptionalMateH (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X Y : Scheme.{u}}
    (R : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ⥤
      DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :=
  (comparisonLowerStar (ModuleCat.{u + 1} Λ) Y).rightDerivedFunctorPlus ⋙ R ⋙
    siteComparisonDerivedPullbackPlus X Λ

/-- The actual unit comparison C_X R L ≅ H C_Y L.
Source: site-comparison unit (blueprint: lem-pur-exceptional-mate-site-comparison). -/
def exceptionalMateUnit (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X Y : Scheme.{u}}
    (R : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ⥤
      DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (L : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (siteComparisonDerivedPullbackPlus X Λ).obj (R.obj L) ≅ (exceptionalMateH Λ R).obj
      ((siteComparisonDerivedPullbackPlus Y Λ).obj L) :=
  (R ⋙ siteComparisonDerivedPullbackPlus X Λ).mapIso ((compactSupportComparisonUnit Y Λ).app L)

/-- The specified relative transpose: insert the witness, apply C_c, transpose under
C_Y ⊣ U_Y, transpose under F ⊣ R, apply C_X, and remove the witness. In particular
this definition permits no scalar renormalization of the Hom bijection.
Source: the displayed Hom chain (blueprint: lem-pur-exceptional-mate-site-comparison). -/
def exceptionalMateTranspose (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    {R : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ⥤
      DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (adj : (Etale.rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} Λ) c) ⊣ R)
    (G : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    {K : DerivedCategory.Plus (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ))}
    (α : (siteComparisonDerivedPullbackPlus X Λ).obj G ≅ K)
    (N : DerivedCategory.Plus (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} Λ)))
    (z : (rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} Λ) c).obj K ⟶ N) : K ⟶
      (exceptionalMateH Λ R).obj N :=
  α.inv ≫ (siteComparisonDerivedPullbackPlus X Λ).map (adj.homEquiv G (((comparisonLowerStar
    (ModuleCat.{u + 1} Λ) Y).rightDerivedFunctorPlus).obj N)
    ((derivedComparisonAdjunctionPlus (ModuleCat.{u + 1} Λ) Y).homEquiv _ N
      ((compactSupportSiteComparisonPlus Λ c).hom.app G ≫
        (rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} Λ) c).map α.hom ≫ z)))

/-- The relative counit, obtained by reversing the specified Hom chain on the identity.
Only the ordinary etale and site-comparison counits occur.
Source: actual-adjoint comparison (blueprint: lem-pur-exceptional-mate-site-comparison). -/
def exceptionalMateCounit (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    {R : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ⥤
      DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (adj : (Etale.rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} Λ) c) ⊣ R)
    (N : DerivedCategory.Plus (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} Λ))) :
    (rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} Λ) c).obj ((exceptionalMateH
      Λ R).obj N) ⟶ N :=
  (compactSupportSiteComparisonPlus Λ c).inv.app (R.obj (((comparisonLowerStar (ModuleCat.{u + 1}
    Λ) Y).rightDerivedFunctorPlus).obj N)) ≫
    (siteComparisonDerivedPullbackPlus Y Λ).map (adj.counit.app (((comparisonLowerStar
      (ModuleCat.{u + 1} Λ) Y).rightDerivedFunctorPlus).obj N)) ≫
    (derivedComparisonAdjunctionPlus (ModuleCat.{u + 1} Λ) Y).counit.app N

/-- The actual etale exchange component, inverted using finite-torsion base change.
Source: compact-support exchange (blueprint: lem-pur-exceptional-mate-site-comparison). -/
def exceptionalMateEtaleExchange (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X X' Y Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {g : Y' ⟶ Y} {g' : X' ⟶ X}
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (sq : IsPullback g' f' f g) (c : Compactification f)
    (G : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (Etale.upperStar (ModuleCat.{u + 1} Λ) g).mapDerivedCategoryPlus.obj
      (((Etale.rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} Λ) c)).obj G) ≅
      ((Etale.rightDerivedLowerShriekOfCompactificationPlus
      (ModuleCat.{u + 1} Λ) (c.ofIsPullback sq))).obj ((Etale.upperStar (ModuleCat.{u + 1} Λ)
        g').mapDerivedCategoryPlus.obj G) :=
  @asIso _ _ _ _
    ((Etale.rightDerivedLowerShriekOfCompactificationPlusBaseChangeMap Λ sq c).app G)
    ((Etale.compactSupportFiniteTorsion Λ sq c).1 G)

/-- Compactification transport T C(B^e) S^{-1}, with the specified proper/open comparison C_c.
Source: finite-level compactification exchange
(blueprint: lem-pur-exceptional-mate-site-comparison). -/
def exceptionalMateProExchange (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X X' Y Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {g : Y' ⟶ Y} {g' : X' ⟶ X}
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (sq : IsPullback g' f' f g) (c : Compactification f)
    (G : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (upperStar (ModuleCat.{u + 1} Λ) g).mapDerivedCategoryPlus.obj
      ((rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} Λ) c).obj
      ((siteComparisonDerivedPullbackPlus X Λ).obj G)) ≅
      (rightDerivedLowerShriekOfCompactificationPlus
        (ModuleCat.{u + 1} Λ) (c.ofIsPullback sq)).obj ((upperStar (ModuleCat.{u + 1} Λ)
          g').mapDerivedCategoryPlus.obj ((siteComparisonDerivedPullbackPlus X Λ).obj G)) :=
  ((cbcGlobalSource Λ g c).app G).symm ≪≫
    (siteComparisonDerivedPullbackPlus Y' Λ).mapIso (exceptionalMateEtaleExchange Λ sq c G) ≪≫
    (cbcGlobalTarget Λ sq c).app G

/-- The ordinary etale counit-transpose mate of inverse compact-support exchange.
Source: final base-change sentences (blueprint: lem-pur-exceptional-mate-site-comparison). -/
def exceptionalMateEtale (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X X' Y Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {g : Y' ⟶ Y} {g' : X' ⟶ X}
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (sq : IsPullback g' f' f g) (c : Compactification f)
    {R : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ⥤
      DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    {R' : DerivedCategory.Plus (Sheaf Y'.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ⥤
      DerivedCategory.Plus (Sheaf X'.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (adj : (Etale.rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} Λ) c) ⊣ R)
      (adj' : (Etale.rightDerivedLowerShriekOfCompactificationPlus
      (ModuleCat.{u + 1} Λ) (c.ofIsPullback sq)) ⊣ R')
    (L : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (Etale.upperStar (ModuleCat.{u + 1} Λ) g').mapDerivedCategoryPlus.obj (R.obj L) ⟶ R'.obj
      ((Etale.upperStar (ModuleCat.{u + 1} Λ) g).mapDerivedCategoryPlus.obj L) :=
  adj'.homEquiv _ _ ((exceptionalMateEtaleExchange Λ sq c (R.obj L)).inv ≫
    (Etale.upperStar (ModuleCat.{u + 1} Λ) g).mapDerivedCategoryPlus.map (adj.counit.app L))

/-- The pro-etale mate is the normalized relative transpose of inverse exchange
followed by the pulled-back relative counit. The pullback comparison supplies its witness.
Source: final base-change sentences (blueprint: lem-pur-exceptional-mate-site-comparison). -/
def exceptionalMatePro (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X X' Y Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {g : Y' ⟶ Y} {g' : X' ⟶ X}
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (sq : IsPullback g' f' f g) (c : Compactification f)
    {R : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ⥤
      DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    {R' : DerivedCategory.Plus (Sheaf Y'.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ⥤
      DerivedCategory.Plus (Sheaf X'.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (adj : (Etale.rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} Λ) c) ⊣ R)
      (adj' : (Etale.rightDerivedLowerShriekOfCompactificationPlus
      (ModuleCat.{u + 1} Λ) (c.ofIsPullback sq)) ⊣ R')
    (N : DerivedCategory.Plus (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} Λ))) :
    (upperStar (ModuleCat.{u + 1} Λ) g').mapDerivedCategoryPlus.obj ((exceptionalMateH Λ R).obj N) ⟶
      (exceptionalMateH Λ R').obj ((upperStar (ModuleCat.{u + 1} Λ) g).mapDerivedCategoryPlus.obj
        N) :=
  exceptionalMateTranspose Λ (c.ofIsPullback sq) adj'
    ((Etale.upperStar (ModuleCat.{u + 1} Λ) g').mapDerivedCategoryPlus.obj (R.obj
      (((comparisonLowerStar (ModuleCat.{u + 1} Λ) Y).rightDerivedFunctorPlus).obj N)))
    ((cbcGlobalPullbackComparison Λ g').app (R.obj (((comparisonLowerStar (ModuleCat.{u + 1} Λ)
      Y).rightDerivedFunctorPlus).obj N))) ((upperStar (ModuleCat.{u + 1} Λ)
      g).mapDerivedCategoryPlus.obj N)
    ((exceptionalMateProExchange Λ sq c (R.obj (((comparisonLowerStar (ModuleCat.{u + 1} Λ)
      Y).rightDerivedFunctorPlus).obj N))).inv ≫
      (upperStar (ModuleCat.{u + 1} Λ) g).mapDerivedCategoryPlus.map (exceptionalMateCounit Λ c
        adj N))

/-- The source endpoint v = kappa^{-1} after the pullback of h^{-1}.
Source: displayed endpoint formula (blueprint: lem-pur-exceptional-mate-site-comparison). -/
def exceptionalMateV (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X X' Y : Scheme.{u}} (g' : X' ⟶ X)
    (R : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ⥤
      DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (L : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (upperStar (ModuleCat.{u + 1} Λ) g').mapDerivedCategoryPlus.obj ((exceptionalMateH Λ R).obj
      ((siteComparisonDerivedPullbackPlus Y Λ).obj L)) ≅
      (siteComparisonDerivedPullbackPlus X' Λ).obj ((Etale.upperStar (ModuleCat.{u + 1} Λ)
        g').mapDerivedCategoryPlus.obj (R.obj L)) :=
  (upperStar (ModuleCat.{u + 1} Λ) g').mapDerivedCategoryPlus.mapIso (exceptionalMateUnit Λ R
    L).symm ≪≫ ((cbcGlobalPullbackComparison Λ g').app (R.obj L)).symm

/-- The target endpoint w = h'^{-1} after H' applied to kappa^{-1}.
Source: displayed endpoint formula (blueprint: lem-pur-exceptional-mate-site-comparison). -/
def exceptionalMateW (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X' Y Y' : Scheme.{u}} (g : Y' ⟶ Y)
    (R' : DerivedCategory.Plus (Sheaf Y'.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ⥤
      DerivedCategory.Plus (Sheaf X'.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (L : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (exceptionalMateH Λ R').obj ((upperStar (ModuleCat.{u + 1} Λ) g).mapDerivedCategoryPlus.obj
      ((siteComparisonDerivedPullbackPlus Y Λ).obj L)) ≅
      (siteComparisonDerivedPullbackPlus X' Λ).obj (R'.obj ((Etale.upperStar (ModuleCat.{u + 1} Λ)
        g).mapDerivedCategoryPlus.obj L)) :=
  (exceptionalMateH Λ R').mapIso ((cbcGlobalPullbackComparison Λ g).app L).symm ≪≫
    (exceptionalMateUnit Λ R' ((Etale.upperStar (ModuleCat.{u + 1} Λ)
      g).mapDerivedCategoryPlus.obj L)).symm

/-- Site comparison preserves the specified exceptional mate, naturally in L and
under every isomorphic witnessed replacement of its comparison pullback.
Source: thm-pur-affine-line-purity.proof.md, actual-adjoint comparison and final
base-change sentences (blueprint: lem-pur-exceptional-mate-site-comparison).

Proof: (1) The dimension bounds give the relative adjunction on the bounded-below
etale-origin class. The pullback comparison exhibits the required witnesses.
(2) Expanding the normalized Hom chain gives Psi(C_Y(b) a_G) = h C_X(J(b)), by
naturality of the comparison unit and the etale adjunction.
(3) Apply this to the etale counit: injectivity of the relative Hom bijection gives
E P(h) = C_Y(e) a_{RL}.
(4) Use the compactification formula of thm-cbc-finite-level-proetale with
C_c = a^{-1}; invert its three isomorphisms. The etale exchange is invertible by
thm-cbc-finite-torsion.
(5) The witness-conjugation clause of thm-cbc-finite-level-proetale gives
naturality of exchange at h. The preceding counit equation and naturality of
kappa then give kappa_g^{-1} z^p P'(v^{-1}) = C_{Y'}(z^e) a'.
(6) Apply the primed normalized relative transpose and cancel h' and v^{-1}.
This proves beta^p followed by w equals v followed by C(beta^e).
(7) Naturality of the ordinary etale exchange, compact-support comparisons and
kappa gives naturality on etale representatives. Full faithfulness and independence
of witnesses extend it to witnessed sources. Naturality of the normalized Hom
bijections and the unit then gives naturality of both exceptional mates in L.
(8) Apply that same naturality to an isomorphism alpha:C_Y L ≅ N and conjugate the
two endpoints. This is precisely the witnessed replacement equation below.
The inputs, right adjoints and all Hom-chain arguments are on D+, as in the node;
there is no unrestricted pro-etale adjunction or smoothness assumption. -/
theorem exceptionalMateSiteComparison
    (D : WeilConjectures.PurityFiniteSetting.{u})
    {X X' Y Y' : Scheme.{u}}
    (aX : X ⟶ Spec (.of D.field.k)) (aY : Y ⟶ Spec (.of D.field.k))
    (aY' : Y' ⟶ Spec (.of D.field.k))
    [IsSeparated aX] [LocallyOfFiniteType aX] [QuasiCompact aX]
    [IsSeparated aY] [LocallyOfFiniteType aY] [QuasiCompact aY]
    [IsSeparated aY'] [LocallyOfFiniteType aY'] [QuasiCompact aY']
    {f : X ⟶ Y} {f' : X' ⟶ Y'} {g : Y' ⟶ Y} {g' : X' ⟶ X}
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (_hf : f ≫ aY = aX) (_hg : g ≫ aY = aY')
    (sq : IsPullback g' f' f g) (c : Compactification f)
    [LocallyOfFiniteType (c.g ≫ aY)] [QuasiCompact (c.g ≫ aY)]
    [LocallyOfFiniteType ((c.ofIsPullback sq).g ≫ aY')]
    [QuasiCompact ((c.ofIsPullback sq).g ≫ aY')]
    (d d' : ℕ) (_hd : topologicalKrullDim c.Z ≤ (d : WithBot ℕ∞))
    (_hd' : topologicalKrullDim (c.ofIsPullback sq).Z ≤ (d' : WithBot ℕ∞))
    (R : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} D.Coefficient)) ⥤
      DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} D.Coefficient)))
    (R' : DerivedCategory.Plus (Sheaf Y'.smallEtaleTopology (ModuleCat.{u + 1} D.Coefficient)) ⥤
      DerivedCategory.Plus (Sheaf X'.smallEtaleTopology (ModuleCat.{u + 1} D.Coefficient)))
    (adj : (Etale.rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} D.Coefficient)
      c) ⊣ R) (adj' : (Etale.rightDerivedLowerShriekOfCompactificationPlus
      (ModuleCat.{u + 1} D.Coefficient) (c.ofIsPullback sq)) ⊣ R') :
    (∀ L, exceptionalMatePro D.Coefficient sq c adj adj' ((siteComparisonDerivedPullbackPlus Y
      D.Coefficient).obj L) ≫
        (exceptionalMateW D.Coefficient g R' L).hom =
      (exceptionalMateV D.Coefficient g' R L).hom ≫
        (siteComparisonDerivedPullbackPlus X' D.Coefficient).map (exceptionalMateEtale
          D.Coefficient sq c adj adj' L)) ∧
    (∀ (L M : DerivedCategory.Plus
        (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} D.Coefficient))) (b : L ⟶ M),
      (upperStar (ModuleCat.{u + 1} D.Coefficient) g').mapDerivedCategoryPlus.map
        ((exceptionalMateH D.Coefficient R).map
          ((siteComparisonDerivedPullbackPlus Y D.Coefficient).map b)) ≫
          exceptionalMatePro D.Coefficient sq c adj adj' ((siteComparisonDerivedPullbackPlus Y
            D.Coefficient).obj M) =
        exceptionalMatePro D.Coefficient sq c adj adj' ((siteComparisonDerivedPullbackPlus Y
          D.Coefficient).obj L) ≫
          (exceptionalMateH D.Coefficient R').map
            ((upperStar (ModuleCat.{u + 1} D.Coefficient) g).mapDerivedCategoryPlus.map
              ((siteComparisonDerivedPullbackPlus Y D.Coefficient).map b))) ∧
    (∀ (L M : DerivedCategory.Plus
        (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} D.Coefficient))) (b : L ⟶ M),
      (Etale.upperStar (ModuleCat.{u + 1} D.Coefficient) g').mapDerivedCategoryPlus.map (R.map b) ≫
          exceptionalMateEtale D.Coefficient sq c adj adj' M =
        exceptionalMateEtale D.Coefficient sq c adj adj' L ≫
          R'.map ((Etale.upperStar (ModuleCat.{u + 1} D.Coefficient) g).mapDerivedCategoryPlus.map
            b)) ∧
    (∀ (L : DerivedCategory.Plus
        (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} D.Coefficient)))
      (N : DerivedCategory.Plus
        (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} D.Coefficient)))
      (α : (siteComparisonDerivedPullbackPlus Y D.Coefficient).obj L ≅ N),
      exceptionalMatePro D.Coefficient sq c adj adj' N ≫
          (exceptionalMateH D.Coefficient R').map ((upperStar (ModuleCat.{u + 1} D.Coefficient)
            g).mapDerivedCategoryPlus.map α.inv) ≫
          (exceptionalMateW D.Coefficient g R' L).hom =
        (upperStar (ModuleCat.{u + 1} D.Coefficient) g').mapDerivedCategoryPlus.map
          ((exceptionalMateH D.Coefficient R).map α.inv) ≫
          (exceptionalMateV D.Coefficient g' R L).hom ≫
          (siteComparisonDerivedPullbackPlus X' D.Coefficient).map (exceptionalMateEtale
            D.Coefficient sq c adj adj' L)) := by
  sorry

end AlgebraicGeometry.ProEtale
