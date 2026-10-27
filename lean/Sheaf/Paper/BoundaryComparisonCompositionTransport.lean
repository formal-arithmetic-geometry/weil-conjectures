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
import Sheaf.CategoryTheory.BoundaryConjugatedComparisonNormalForm
import Sheaf.CategoryTheory.IteratedCounitNormalForm

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

private def rhoIso {X Y : Scheme.{u}} {f : X ⟶ Y} (L : Leg P f) :
    L.originSource ≅ L.originTarget := by
  refine NatIso.ofComponents (fun J ↦ ?_) ?_
  · haveI := isIso_derivedComparisonAdjunction_unit_app
      (ModuleCat.{u + 1} P.Coefficient) Y J.obj J.property
    exact (S P X).mapIso (L.right.mapIso
      (asIso ((derivedComparisonAdjunction
        (ModuleCat.{u + 1} P.Coefficient) Y).unit.app J.obj)))
  · intro J J' b
    change (S P X).map (L.right.map b.hom) ≫
        boundedSiteRho P.Coefficient L.right J'.obj =
      boundedSiteRho P.Coefficient L.right J.obj ≫
        (S P X).map (L.right.map
          ((comparisonLowerStar (ModuleCat.{u + 1} P.Coefficient) Y).rightDerivedFunctor.map
            ((S P Y).map b.hom)))
    simp only [boundedSiteRho, ← Functor.map_comp]
    exact congrArg (fun z ↦ (S P X).map (L.right.map z))
      ((derivedComparisonAdjunction (ModuleCat.{u + 1} P.Coefficient) Y).unit.naturality b.hom)

private theorem normalized {X Y : Scheme.{u}} {f : X ⟶ Y} (L : Leg P f)
    (aX : X ⟶ Spec (.of P.field.k)) (aY : Y ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aX] [QuasiCompact aX]
    [LocallyOfFiniteType aY] [QuasiCompact aY]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (hf : f ≫ aY = aX) : L.Normalized aX aY hf := by
  refine ⟨?_, ?_, ?_⟩
  · intro J
    have h := ((siteComparisonDerivedPullbackPlus X P.Coefficient).obj
      (L.rightPlus.obj J)).property
    exact ⟨h, _root_.DerivedCategory.TStructure.t.plus.prop_of_iso
      ((rhoIso L).app J) h⟩
  · intro N N' b
    let J := boundedSiteRightAdjointPlus P aX aY f hf L.compactification L.dimension
      L.dimension_le L.right L.adjunction N
    let J' := boundedSiteRightAdjointPlus P aX aY f hf L.compactification L.dimension
      L.dimension_le L.right L.adjunction N'
    let e := boundedSiteHomEquiv P aX aY f hf L.compactification L.dimension
      L.dimension_le L.right L.adjunction
    have hc (M) : e (boundedSiteRightAdjointPlus P aX aY f hf L.compactification
        L.dimension L.dimension_le L.right L.adjunction M) M
        (L.mu aX aY hf M) = 𝟙 _ := (e _ M).apply_symm_apply _
    have hn := boundedSiteAdjunctionTranspose_naturality P aX aY f hf
      L.compactification L.dimension L.dimension_le L.right L.adjunction
    let v := L.right.map
      ((comparisonLowerStar (ModuleCat.{u + 1} P.Coefficient) Y).rightDerivedFunctor.map
        b.hom)
    have hl := hn.1 J' J N' v (L.mu aX aY hf N')
    have hr := hn.2.1 J N N' b.hom (L.mu aX aY hf N)
    apply (e J N').injective
    have hm : (S P X).map v ≫ e J' N' (L.mu aX aY hf N') =
        e J N (L.mu aX aY hf N) ≫ (S P X).map v := by
      rw [hc N', hc N]
      exact (Category.comp_id _).trans (Category.id_comp _).symm
    exact hl.trans (hm.trans hr.symm)
  · intro J
    exact (boundedSiteAdjunctionTranspose P aX aY f hf L.compactification
      L.dimension L.dimension_le L.right L.adjunction (L.rightPlus.obj J) J
      (L.right_plus J)).2.1

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
  let hgf := (Category.assoc f g aB).trans ((congrArg (fun t ↦ f ≫ t) hg).trans hf)
  have nf := normalized Lf aX aY hf
  have ng := normalized Lg aY aB hg
  have nc := normalized Lgf aX aB hgf
  let rf := rhoIso Lf
  let rg := rhoIso Lg
  let rc := rhoIso Lgf
  let SX := _root_.DerivedCategory.Plus.ι ⋙ S P X
  let SY := _root_.DerivedCategory.Plus.ι ⋙ S P Y
  let SB := _root_.DerivedCategory.Plus.ι ⋙ S P B
  let al : Lf.leftPlus ⋙ Lg.leftPlus ≅ Lgf.leftPlus :=
    NatIso.ofComponents (fun G ↦ ObjectProperty.isoMk _ (alpha.app G)) (by
      intro G G' b
      ext
      exact alpha.hom.naturality b)
  let th : Lgf.rightPlus ≅ Lg.rightPlus ⋙ Lf.rightPlus :=
    NatIso.ofComponents (fun H ↦ ObjectProperty.isoMk _ (theta.app H)) (by
      intro H H' b
      ext
      exact theta.hom.naturality b)
  let ec : Lgf.rightPlus ⋙ Lgf.leftPlus ⟶ 𝟭 _ :=
    { app := fun H ↦ ObjectProperty.homMk (Lgf.adjunction.counit.app H.obj)
      naturality := fun H H' b ↦ by
        ext
        exact Lgf.adjunction.counit.naturality b.hom }
  have n := BoundaryConjugatedComparison.normalForm
    Lf.leftPlus Lg.leftPlus Lgf.leftPlus Lf.rightPlus Lg.rightPlus Lgf.rightPlus
    Lf.support Lg.support Lgf.support Lf.Q Lg.Q Lgf.Q SX SY SB rf rg rc
    Lf.B Lg.B Lgf.B al th ec
    (fun H ↦ Lgf.mu aX aB hgf ((siteComparisonDerivedPullbackPlus B P.Coefficient).obj H))
    nc.2.2
  let Xi := BoundaryConjugatedComparison.rightIso
    (Rf := Lf.rightPlus) (Rg := Lg.rightPlus) (Rc := Lgf.rightPlus)
    (Qf := Lf.Q) (Qg := Lg.Q) (Qc := Lgf.Q)
    (SX := SX) (SY := SY) (SB := SB) rf rg rc th
  let ap := BoundaryConjugatedComparison.leftIso
    (Ff := Lf.leftPlus) (Fg := Lg.leftPlus) (Fc := Lgf.leftPlus)
    (Pf := Lf.support) (Pg := Lg.support) (Pc := Lgf.support)
    (SX := SX) (SY := SY) (SB := SB) Lf.B Lg.B Lgf.B al
  refine ⟨nf, ng, nc, rf, rg, rc, (fun _ ↦ rfl), (fun _ ↦ rfl),
    (fun _ ↦ rfl), Xi, ap, n.1, n.2.1, ?_, ?_⟩
  · intro H
    let N := (siteComparisonDerivedPullbackPlus B P.Coefficient).obj H
    let N₀ := (siteComparisonDerivedPullbackPlus Y P.Coefficient).obj (Lg.rightPlus.obj H)
    let N₁ := Lg.qObject aY aB hg N
    let hr : N₀ ⟶ N₁ := ObjectProperty.homMk (rg.hom.app H)
    have hm := nf.2.1 N₀ N₁ hr
    dsimp only [hr, ObjectProperty.homMk_hom] at hm
    have hi := iteratedCounitNormalForm _ _ _ _ _ _
      Lf.leftPlus Lf.rightPlus Lg.leftPlus Lg.rightPlus Lf.support Lf.Q Lg.support Lg.Q
      SX SY SB Lf.B Lg.B H (Lgf.rightPlus.obj H) (th.hom.app H)
      (ObjectProperty.homMk (Lf.adjunction.counit.app (Lg.right.obj H.obj)))
      (ObjectProperty.homMk (Lg.adjunction.counit.app H.obj))
      (rg.hom.app H) (rf.hom.app (Lg.rightPlus.obj H))
      (Lg.mu aY aB hg N) (Lf.mu aX aY hf N₀) (Lf.mu aX aY hf N₁)
      (ng.2.2 H) (nf.2.2 (Lg.rightPlus.obj H)) hm
    let prefMap := Lg.support.map (Lf.B.inv.app (Lgf.rightPlus.obj H)) ≫
      Lg.B.inv.app (Lf.leftPlus.obj (Lgf.rightPlus.obj H))
    calc
      _ = prefMap ≫ (S P B).map
          (alpha.hom.app (Lgf.rightPlus.obj H) ≫ Lgf.adjunction.counit.app H.obj) := by
        exact (n.2.2.2 H).trans (Category.assoc _ _ _).symm
      _ = prefMap ≫ (S P B).map
          (Lg.F.map (Lf.F.map (theta.hom.app H)) ≫
            Lg.F.map (Lf.adjunction.counit.app (Lg.right.obj H.obj)) ≫
              Lg.adjunction.counit.app H.obj) :=
        congrArg (fun z ↦ prefMap ≫ (S P B).map z) (mate H)
      _ = Lg.support.map (Lf.support.map
          ((S P X).map (theta.hom.app H) ≫ rf.hom.app (Lg.rightPlus.obj H) ≫
            Lf.Q.map (rg.hom.app H))) ≫
          Lg.support.map (Lf.mu aX aY hf N₁) ≫ Lg.mu aY aB hg N :=
        (Category.assoc _ _ _).trans hi.symm
      _ = _ := congrArg (fun z ↦ Lg.support.map (Lf.support.map z) ≫
        Lg.support.map (Lf.mu aX aY hf N₁) ≫ Lg.mu aY aB hg N) (n.2.2.1 H).symm
  · rw [n.1]
    simp only [Functor.comp_map, Functor.map_comp, Category.assoc]
    rfl

end AlgebraicGeometry.ProEtale.BoundaryComparisonCompositionTransport
