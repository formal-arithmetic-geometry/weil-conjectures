/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q29
-/
module

public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import Sheaf.AlgebraicGeometry.ProEtaleFiniteModules
public import Sheaf.AlgebraicGeometry.ProEtaleSiteComparison
public import Sheaf.AlgebraicGeometry.ComparisonDerivedPullbackFixed
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.Compactification.RefinementCategory
public import Mathlib.Topology.KrullDimension
public import Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients
public import Sheaf.AlgebraicGeometry.SfIntrinsicCompactSupport
public import Sheaf.AlgebraicGeometry.CanonicalCompactSupportSiteComparison
public import Sheaf.AlgebraicGeometry.FixedEtaleOriginWitness
public import Sheaf.Paper.PurityFiniteSetting
public import Sheaf.Paper.BoundedSiteAdjunctionTranspose
public import Sheaf.CategoryTheory.ConstantLeftModuleInverseImage
import Sheaf.AlgebraicGeometry.CompactSupportComparisonUnit

/-! # Comparison-unit transport of a specified composition mate

Source: Bhatt--Scholze, The pro-etale topology for schemes, Corollary 5.1.6;
formal comparison-unit and relative-counit calculation in the boundary-duality proof
(blueprint: lem-weil-boundary-comparison-composition-transport).

All functors below act on ordinary fixed-coefficient derived categories. The relative
counits are the inverse specified Hom transposes from BoundedSiteAdjunctionTranspose.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.BoundaryComparisonCompositionTransport

variable (P : WeilConjectures.PurityFiniteSetting.{u})

/-- The specified compactification, dimension bound, and ambient etale adjunction of one
leg, including precisely the assumed preservation of D+ by both functors.
Source: boundary-duality comparison-unit transport, initial data
(blueprint: lem-weil-boundary-comparison-composition-transport). -/
structure Leg {X Y : Scheme.{u}} (f : X ⟶ Y) where
  compactification : Compactification f
  dimension : ℕ
  dimension_le : topologicalKrullDim compactification.Z ≤ (dimension : WithBot ℕ∞)
  right : DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient)) ⥤
    DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient))
  adjunction : Etale.rightDerivedLowerShriekOfCompactification
    (ModuleCat.{u + 1} P.Coefficient) compactification ⊣ right
  right_plus : ∀ J : DerivedCategory.Plus
    (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient)),
    _root_.DerivedCategory.TStructure.t.plus (right.obj J.obj)
  left_plus : ∀ G : DerivedCategory.Plus
    (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient)),
    _root_.DerivedCategory.TStructure.t.plus
      ((Etale.rightDerivedLowerShriekOfCompactification
        (ModuleCat.{u + 1} P.Coefficient) compactification).obj G.obj)

variable {P}
namespace Leg
variable {X Y : Scheme.{u}} {f : X ⟶ Y} (L : Leg P f)

/-- The given etale compact-support functor, at the specified compactification.
Source: comparison-unit transport, F_h
(blueprint: lem-weil-boundary-comparison-composition-transport). -/
abbrev F := Etale.rightDerivedLowerShriekOfCompactification
  (ModuleCat.{u + 1} P.Coefficient) L.compactification

/-- Restrict the specified right adjoint using its assumed lower-bound preservation.
Source: comparison-unit transport, R_h on D+
(blueprint: lem-weil-boundary-comparison-composition-transport). -/
def rightPlus := _root_.DerivedCategory.TStructure.t.plus.lift
  (_root_.DerivedCategory.Plus.ι ⋙ L.right) L.right_plus

/-- Restrict the specified left functor using its assumed lower-bound preservation.
Source: comparison-unit transport, F_h on D+
(blueprint: lem-weil-boundary-comparison-composition-transport). -/
def leftPlus := _root_.DerivedCategory.TStructure.t.plus.lift
  (_root_.DerivedCategory.Plus.ι ⋙ L.F) L.left_plus

/-- The finite exceptional comparison functor is literally U_target, R_h, S_source.
Source: comparison-unit transport, Q_h = S_source R_h U_target
(blueprint: lem-weil-boundary-comparison-composition-transport). -/
abbrev Q := (comparisonLowerStar (ModuleCat.{u + 1} P.Coefficient) Y).rightDerivedFunctor ⋙
  L.right ⋙ (comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) X).mapDerivedCategory

variable (aX : X ⟶ Spec (.of P.field.k)) (aY : Y ⟶ Spec (.of P.field.k))
variable [LocallyOfFiniteType aX] [QuasiCompact aX]
  [LocallyOfFiniteType aY] [QuasiCompact aY]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
variable (hf : f ≫ aY = aX)

/-- The actual Q_h object with its lower bound, obtained from the existing bounded
etale right-adjoint intermediate object and exact comparison.
Source: comparison-unit transport, boundedness of Q_h
(blueprint: lem-weil-boundary-comparison-composition-transport). -/
def qObject (N : DerivedCategory.Plus
    (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} P.Coefficient))) :=
  (siteComparisonDerivedPullbackPlus X P.Coefficient).obj
    (boundedSiteRightAdjointPlus P aX aY f hf L.compactification L.dimension
      L.dimension_le L.right L.adjunction N)

/-- The specified relative counit, inverse Hom transpose of identity with the identity
etale-origin witness. It is not the counit of an assumed ambient pro-etale adjunction.
Source: comparison-unit transport, mu_h
(blueprint: lem-weil-boundary-comparison-composition-transport). -/
def mu (N : DerivedCategory.Plus
    (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} P.Coefficient))) :=
  boundedSiteCounit P aX aY f hf L.compactification L.dimension L.dimension_le
    L.right L.adjunction N

end Leg

/-- Short name for the existing exact derived site comparison S_T.
Source: Bhatt--Scholze, Corollary 5.1.6
(blueprint: lem-weil-boundary-comparison-composition-transport). -/
abbrev S (P : WeilConjectures.PurityFiniteSetting.{u}) (T : Scheme.{u}) :=
  (comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) T).mapDerivedCategory

namespace Leg
variable {X Y : Scheme.{u}} {f : X ⟶ Y} (L : Leg P f)

/-- The pro-etale compact-support functor at the same compactification.
Source: comparison-unit transport, P_h
(blueprint: lem-weil-boundary-comparison-composition-transport). -/
abbrev support := rightDerivedLowerShriekOfCompactification
  (ModuleCat.{u + 1} P.Coefficient) L.compactification

/-- B_h is exactly the inverse of the canonical proper/open site comparison.
Source: comparison-unit transport, B_h
(blueprint: lem-weil-boundary-comparison-composition-transport). -/
abbrev B := (compactSupportSiteComparison P.Coefficient L.compactification).symm

/-- The two functors joined by rho, on bounded-below etale inputs (source).
Source: comparison-unit transport, rho_h
(blueprint: lem-weil-boundary-comparison-composition-transport). -/
abbrev originSource := _root_.DerivedCategory.Plus.ι ⋙ L.right ⋙ S P X

/-- The two functors joined by rho, on bounded-below etale inputs (target).
Source: comparison-unit transport, rho_h
(blueprint: lem-weil-boundary-comparison-composition-transport). -/
abbrev originTarget := _root_.DerivedCategory.Plus.ι ⋙ S P Y ⋙ L.Q

variable (aX : X ⟶ Spec (.of P.field.k)) (aY : Y ⟶ Spec (.of P.field.k))
variable [LocallyOfFiniteType aX] [QuasiCompact aX]
  [LocallyOfFiniteType aY] [QuasiCompact aY]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
variable (hf : f ≫ aY = aX)

/-- The rho bounds, naturality of the specified relative counit, and its displayed
normalization. The transpose and counit are the existing canonical constructions.
Source: comparison-unit transport, rho and mu clauses
(blueprint: lem-weil-boundary-comparison-composition-transport). -/
def Normalized : Prop :=
  (∀ J : DerivedCategory.Plus
      (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient)),
    _root_.DerivedCategory.TStructure.t.plus (L.originSource.obj J) ∧
    _root_.DerivedCategory.TStructure.t.plus (L.originTarget.obj J)) ∧
  (∀ (N N' : DerivedCategory.Plus
      (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} P.Coefficient))) (b : N ⟶ N'),
    L.support.map (L.Q.map b.hom) ≫ L.mu aX aY hf N' = L.mu aX aY hf N ≫ b.hom) ∧
  (∀ J : DerivedCategory.Plus
      (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient)),
    L.B.hom.app (L.rightPlus.obj J) ≫
      L.support.map (boundedSiteRho P.Coefficient L.right J.obj) ≫
      L.mu aX aY hf ((siteComparisonDerivedPullbackPlus Y P.Coefficient).obj J) =
        (S P Y).map (L.adjunction.counit.app J.obj))

end Leg

/-- The degree-zero constant etale coefficient object, with its canonical lower bound.
Source: comparison-unit transport, A_e
(blueprint: lem-weil-boundary-comparison-composition-transport). -/
def constantEtalePlus (P : WeilConjectures.PurityFiniteSetting.{u}) (T : Scheme.{u}) :=
  (_root_.DerivedCategory.Plus.singleFunctor
    (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient)) 0).obj (P.constantEtale T)

/-- The canonical degree-zero comparison identifies S_T A_e with A_p, preserving
scalars because comparison is the fixed-module inverse image.
Source: comparison-unit transport, constant-left-module inverse image
(blueprint: lem-weil-boundary-comparison-composition-transport). -/
def constantIso (P : WeilConjectures.PurityFiniteSetting.{u}) (T : Scheme.{u}) :=
  (Functor.mapDerivedCategorySingleFunctor
    (comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) T) 0).app (P.constantEtale T)

/-- Comparison-unit transport of a specified inverse composition mate, with the pasted
relative-counit identity and the degree-zero scalar-preserving specialization.
Source: Bhatt--Scholze, Corollary 5.1.6; boundary-duality proof, comparison-unit transport
(blueprint: lem-weil-boundary-comparison-composition-transport).

Proof:
1. By thm-weil-pbc-site-comparison the actual unit eta is invertible on D+.
   Apply S_source R_h to obtain rho_h and its inverse; exact S and the assumed
   preservation by R_h give both lower bounds. Unit naturality gives naturality of rho.
2. Apply lem-pur-bounded-site-adjunction-transpose to f, g, gf at the chosen
   compactifications and dimension bounds. Its B and inverse Hom transpose are exactly
   Leg.B and Leg.mu. It gives the normalized counit equation in Leg.Normalized.
   Naturality of the Hom chain gives naturality of mu.
3. Compose the four invertible natural factors in the stated order to obtain Xi.
   Reversing the factors gives Xi inverse followed after rho_gf as
   S_X(theta), rho_f, then Q_f(rho_g). Naturality is preserved by inverse and composition.
4. Likewise compose B_f inverse under P_g, B_g inverse, S_B(alpha), and B_gf
   to obtain alphaP. The assumed preservation of D+ by F_f supplies its B_g input.
   Substitution into the left pasted counit and cancellation of B_gf reduce it to
   S_B(alpha followed by epsilon_gf), preceded by the two inverse B factors.
5. On the right use naturality of mu_f at rho_g to move Q_f(rho_g) through mu_f.
   All its targets are bounded below, as in step 1.
6. Apply the normalized counit equations for f at R_g H and g at H, cancelling B_f
   and B_g. Only bounded-below etale-origin inputs occur.
7. Use inverse naturality of B_g at epsilon_f, of B_f at theta, and of B_g at F_f(theta).
   Functoriality leaves S_B(F_g F_f(theta), F_g(epsilon_f), epsilon_g), with the same
   two initial inverse B factors as in step 4.
8. The assumed mate normalization identifies this composite with step 4.
   This proves the pasted identity without any ambient pro-etale adjunction.
9. Specialize to the bounded-below degree-zero constant object. The canonical
   constant-left-module inverse image identifies S_B A_e with A_p, preserving scalars.
   Conjugating Xi by that identification gives exactly the four displayed lambda arrows.
-/
theorem transport
    (P : WeilConjectures.PurityFiniteSetting.{u})
    {X Y B : Scheme.{u}}
    (aX : X ⟶ Spec (.of P.field.k)) (aY : Y ⟶ Spec (.of P.field.k))
    (aB : B ⟶ Spec (.of P.field.k))
    [IsSeparated aX] [LocallyOfFiniteType aX] [QuasiCompact aX]
    [IsSeparated aY] [LocallyOfFiniteType aY] [QuasiCompact aY]
    [IsSeparated aB] [LocallyOfFiniteType aB] [QuasiCompact aB]
    (f : X ⟶ Y) (g : Y ⟶ B)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    (hf : f ≫ aY = aX) (hg : g ≫ aB = aY)
    (Lf : Leg P f) (Lg : Leg P g) (Lgf : Leg P (f ≫ g))
    (alpha : _root_.DerivedCategory.Plus.ι ⋙ Lf.F ⋙ Lg.F ≅
      _root_.DerivedCategory.Plus.ι ⋙ Lgf.F)
    (theta : _root_.DerivedCategory.Plus.ι ⋙ Lgf.right ≅
      _root_.DerivedCategory.Plus.ι ⋙ Lg.right ⋙ Lf.right)
    (mate : ∀ H : DerivedCategory.Plus
      (Sheaf B.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient)),
      alpha.hom.app (Lgf.rightPlus.obj H) ≫ Lgf.adjunction.counit.app H.obj =
        Lg.F.map (Lf.F.map (theta.hom.app H)) ≫
          Lg.F.map (Lf.adjunction.counit.app (Lg.right.obj H.obj)) ≫
            Lg.adjunction.counit.app H.obj) :
    Lf.Normalized aX aY hf ∧ Lg.Normalized aY aB hg ∧ Lgf.Normalized aX aB
      ((Category.assoc f g aB).trans ((congrArg (fun t ↦ f ≫ t) hg).trans hf)) ∧
    ∃ (rf : Lf.originSource ≅ Lf.originTarget)
      (rg : Lg.originSource ≅ Lg.originTarget)
      (rgf : Lgf.originSource ≅ Lgf.originTarget),
      (∀ J, rf.hom.app J = boundedSiteRho P.Coefficient Lf.right J.obj) ∧
      (∀ J, rg.hom.app J = boundedSiteRho P.Coefficient Lg.right J.obj) ∧
      (∀ J, rgf.hom.app J = boundedSiteRho P.Coefficient Lgf.right J.obj) ∧
    ∃ (Xi : _root_.DerivedCategory.Plus.ι ⋙ S P B ⋙ Lg.Q ⋙ Lf.Q ≅
        _root_.DerivedCategory.Plus.ι ⋙ S P B ⋙ Lgf.Q)
      (alphaP : _root_.DerivedCategory.Plus.ι ⋙ S P X ⋙ Lf.support ⋙ Lg.support ≅
        _root_.DerivedCategory.Plus.ι ⋙ S P X ⋙ Lgf.support),
      (∀ H, Xi.hom.app H = Lf.Q.map (rg.inv.app H) ≫
        rf.inv.app (Lg.rightPlus.obj H) ≫ (S P X).map (theta.inv.app H) ≫ rgf.hom.app H) ∧
      (∀ G, alphaP.hom.app G = Lg.support.map (Lf.B.inv.app G) ≫
        Lg.B.inv.app (Lf.leftPlus.obj G) ≫ (S P B).map (alpha.hom.app G) ≫
          Lgf.B.hom.app G) ∧
      (∀ H, alphaP.hom.app (Lgf.rightPlus.obj H) ≫
        Lgf.support.map (rgf.hom.app H) ≫
          Lgf.mu aX aB
            ((Category.assoc f g aB).trans ((congrArg (fun t ↦ f ≫ t) hg).trans hf))
            ((siteComparisonDerivedPullbackPlus B P.Coefficient).obj H) =
        Lg.support.map (Lf.support.map (rgf.hom.app H ≫ Xi.inv.app H)) ≫
          Lg.support.map (Lf.mu aX aY hf
            (Lg.qObject aY aB hg
              ((siteComparisonDerivedPullbackPlus B P.Coefficient).obj H))) ≫
          Lg.mu aY aB hg ((siteComparisonDerivedPullbackPlus B P.Coefficient).obj H)) ∧
      (Lg.Q ⋙ Lf.Q).map (constantIso P B).inv ≫
          Xi.hom.app (constantEtalePlus P B) ≫ Lgf.Q.map (constantIso P B).hom =
        Lf.Q.map (Lg.Q.map (constantIso P B).inv ≫
          rg.inv.app (constantEtalePlus P B)) ≫
        rf.inv.app (Lg.rightPlus.obj (constantEtalePlus P B)) ≫
        (S P X).map (theta.inv.app (constantEtalePlus P B)) ≫
        (rgf.hom.app (constantEtalePlus P B) ≫ Lgf.Q.map (constantIso P B).hom) := by
  sorry

end AlgebraicGeometry.ProEtale.BoundaryComparisonCompositionTransport
