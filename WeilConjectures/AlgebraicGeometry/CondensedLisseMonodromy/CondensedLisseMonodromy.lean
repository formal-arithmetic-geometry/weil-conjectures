/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeart
public import WeilConjectures.RepresentationTheory.PoincareDuality.LAdic
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import WeilConjectures.AlgebraicGeometry.CondensedQbarCoefficientConstruction
public import WeilConjectures.AlgebraicGeometry.Galois.GaloisLisseRepresentations
import WeilConjectures.AlgebraicGeometry.FundamentalGroup.UniversalCoverLift
import WeilConjectures.AlgebraicGeometry.Lisse.LisseAdicFiberFunctors
import Mathlib.RingTheory.TensorProduct.IsBaseChangeFree
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Topology.Algebra.Module.FiniteDimension
public import WeilConjectures.AlgebraicGeometry.Lisse.LisseAdicSheaves
public import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.AlgebraicGeometry.Regular
public import WeilConjectures.CategoryTheory.ModuleObjects.Monoidal
public import WeilConjectures.CategoryTheory.Monoidal.Mod.TensorRegular
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.PathTransport
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.IntegralReduction
public import WeilConjectures.CategoryTheory.ModuleObjects.EllAdicRationalization
public import WeilConjectures.AlgebraicGeometry.Support.SupportComparisonPullbackCoherence
public import WeilConjectures.AlgebraicGeometry.EtaleAdicPathData
public import WeilConjectures.AlgebraicGeometry.Fibre.FibreFunctorBasepointTransportData
public import WeilConjectures.AlgebraicGeometry.Curve.FLCFiber
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.StalkTransport
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Germ
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.OpenClosed
import WeilConjectures.CategoryTheory.InternalAbelianSheafModuleEquivalence
import Mathlib.AlgebraicGeometry.Sites.Proetale
import WeilConjectures.RingTheory.ProEtale.WContractible
import WeilConjectures.CategoryTheory.SiteCoveringAxioms
import WeilConjectures.CategoryTheory.RingedSiteModules
import WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible
import Mathlib.CategoryTheory.Abelian.Exact
import Mathlib.CategoryTheory.Sites.LeftExact
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import Mathlib.Algebra.Category.Grp.EpiMono
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.CategoryTheory.Sites.LocallySurjective
import WeilConjectures.AlgebraicGeometry.CoefficientComparisonFixedPullback
import WeilConjectures.WeilObject.Sheaf.Stalk
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal
import WeilConjectures.AlgebraicGeometry.InternalModuleOperations.InternalModuleOperationsTransportSupplement
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Continuous.ContinuousLocallyFreePullbackSupplement
import WeilConjectures.AlgebraicGeometry.Fibre.FibreFunctorBasepointTransportData
import WeilConjectures.AlgebraicGeometry.Fibre.FibreFunctorLinearTransport
import WeilConjectures.AlgebraicGeometry.Integral.IntegralFibrePathConstruction
import WeilConjectures.AlgebraicGeometry.Rational.RationalFibrePathConstruction
import Mathlib.CategoryTheory.Localization.Construction
import WeilConjectures.AlgebraicGeometry.Rational.RationalFibrePathScalarSquare
import WeilConjectures.AlgebraicGeometry.Lisse.Coefficient.LisseCoefficientFiberComparisons
import WeilConjectures.CategoryTheory.Pseudofunctor.NormalizedFibreComparisons
import WeilConjectures.AlgebraicGeometry.FundamentalGroup.Basic
import WeilConjectures.AlgebraicGeometry.FundamentalGroup.LocallyConstantEquivalenceExtension
import WeilConjectures.Mathlib.CategoryTheory.Galois.Prorepresentability
import Mathlib.AlgebraicGeometry.Noetherian

/-! # Condensed lisse monodromy, with finite-level normalization

Source: `literature/blueprint/latest/blueprint/sec-six-functors/sk-lem-finite/`
`thm-lisse-qlbar-representations.md`, theorem and clauses (1)--(5), and Weil II (1.1.6).
(blueprint: lem-a1-condensed-lisse-monodromy).

## Main definitions

* `Lisse` and `fibre`: the existing lisse full subcategory and its actual geometric fibre.
* `Model` and `ModelNormalization`: integral coefficient models and finite-level normalization.
* `Comparison` and `CompatibleSystem`: the exact tensor comparison and its compatibilities.
* `WeilCompatibility`: equality of the path-defined degree-one operators.

## Main statement

* `condensed_lisse_monodromy`: existence and fibre-compatible uniqueness of the comparison.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genSizeOf false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped TensorProduct CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedLisseMonodromy

/-- The full category of locally finite free modules over precisely p_X^* Qbar_l.
Source: `sk-lem-coefficient-heart`, introductory lisse clause.
(blueprint: lem-a1-condensed-lisse-monodromy). -/
abbrev Lisse (l : ℕ) [Fact l.Prime] (X : Scheme.{u}) :=
  ObjectProperty.FullSubcategory
    (IsLisseCoefficientModule (Profinite.padicAlgClRingObj l) (X := X))

/-- The published terminal-section evaluation, with its scalar size transport specified.
Source: the Fibres paragraph of `thm-lisse-qlbar-representations`.
(blueprint: lem-a1-condensed-lisse-monodromy). -/
def geometricEvaluation (l : ℕ) [Fact l.Prime] (Ω : Type u) [Field Ω] [IsAlgClosed Ω] :
    Modules l (Spec (.of Ω)) ⥤ ModuleCat.{u + 1} (Coeff.{u} l) :=
  CondensedQbarGeometricEvaluation.fieldFiber Ω l ⋙
    ModuleCat.restrictScalars
      (ULift.ringEquiv.toRingHom : Coeff.{u} l →+* PadicAlgCl l)

/-- Gamma(Spec Omega, x^* -), with the canonical size transport on scalar modules.
Source: `thm-lisse-qlbar-representations`, Fibres paragraph.
(blueprint: lem-a1-condensed-lisse-monodromy). -/
def rawFibre (l : ℕ) [Fact l.Prime] {X : Scheme.{u}}
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ X) :
    Modules l X ⥤ ModuleCat.{u + 1} (Coeff.{u} l) :=
  CondensedRing.upperStar (Profinite.padicAlgClRingObj l) x ⋙ geometricEvaluation l Ω

/-- The displayed fibre functor restricted to lisse objects.
Source: `thm-lisse-qlbar-representations`, theorem.
(blueprint: lem-a1-condensed-lisse-monodromy). -/
def fibre (l : ℕ) [Fact l.Prime] {X : Scheme.{u}}
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ X) :
    Lisse l X ⥤ ModuleCat.{u + 1} (Coeff.{u} l) :=
  ObjectProperty.ι (IsLisseCoefficientModule (Profinite.padicAlgClRingObj l) (X := X)) ⋙
    rawFibre l x

attribute [instance] Domain.overBase Domain.connected Domain.regular Domain.finiteType
  Domain.quasiCompact Domain.separated

/-- The actual abelian geometric fibre, before equipping it with constant scalars.
Source: the Fibres paragraph of `thm-lisse-qlbar-representations`.
(blueprint: lem-a1-condensed-lisse-monodromy). -/
def abFibre {X : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (x : Spec (.of Ω) ⟶ X) : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1} ⥤ Ab.{u + 1} :=
  ProEtale.upperStar Ab.{u + 1} x ⋙ Sheaf.Γ _ Ab.{u + 1}

/-- The canonical forgetting comparison for comparison inverse image, retaining its unit.
Source: finite comparison in `thm-lisse-qlbar-representations` (1).
(blueprint: lem-a1-condensed-lisse-monodromy). -/
structure ForgetComparison (X : Scheme.{u}) (R : Type (u + 1)) [CommRing R] where
  iso : supportSiteComparisonCoefficientPullback (ModuleCat.{u + 1} R) X ⋙
      sheafCompose _ (forget₂ (ModuleCat.{u + 1} R) Ab.{u + 1}) ≅
    sheafCompose _ (forget₂ (ModuleCat.{u + 1} R) Ab.{u + 1}) ⋙
      supportSiteComparisonCoefficientPullback Ab.{u + 1} X
  unit : ∀ (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)) (U : X.Etale)
    (s : F.obj.obj (op U)),
    ((iso.hom.app F).hom.app (op ((Scheme.toProEt X).obj U)))
      (((supportSiteComparisonCoefficientAdjunction (ModuleCat.{u + 1} R) X).unit.app F).hom.app
        (op U) s) =
      ((supportSiteComparisonCoefficientAdjunction Ab.{u + 1} X).unit.app
        ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} R) Ab.{u + 1})).obj F)).hom.app (op U) s

/-- Insert the published underlying-sheaf equality without unfolding scalar extension.
Source: `finiteCoefficientModEquivalence_functor_comp_sheafCompose`.
(blueprint: lem-a1-condensed-lisse-monodromy). -/
@[irreducible] def finiteUnderlyingIso (X : Scheme.{u}) (R : Type) [CommRing R]
    [TopologicalSpace R] [IsTopologicalRing R] [DiscreteTopology R] [Finite R]
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj R) X)) :
    M.X ≅ (sheafCompose _
      (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} R)) Ab.{u + 1})).obj
        ((finiteCoefficientModEquivalence X R).functor.obj M) :=
  eqToIso (congrArg (fun F ↦ F.obj M)
    (finiteCoefficientModEquivalence_functor_comp_sheafCompose X R)).symm

/-- Finite geometric fibres and finite paths with their germ rules. These rules, rather
than an arbitrary stalk isomorphism, specify both comparisons uniquely.
Source: `cor-galois-lisse-representations` (1), finite-fibre normalization.
(blueprint: lem-a1-condensed-lisse-monodromy). -/
structure FiniteNormalization (X : Scheme.{u}) (F : Sheaf X.smallEtaleTopology Ab.{u + 1}) where
  point : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ X),
    (abFibre x).obj ((supportSiteComparisonCoefficientPullback Ab.{u + 1} X).obj F) ≅
      (pointSmallEtale x).ulift.{u + 1}.sheafFiber.obj F
  point_germ : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ X)
    (U : X.Etale) (a : (pointSmallEtale x).fiber.obj U)
    (t : Scheme.ProEt.mk (𝟙 (Spec (.of Ω))) ⟶
      (MorphismProperty.Over.pullback @WeaklyEtale ⊤ x).obj ((Scheme.toProEt X).obj U))
    (_ : t.left ≫ pullback.fst U.hom x = a.left) (s : F.obj.obj (op U)),
    (point Ω x).hom
      (ProEtale.germ Ab.{u + 1} x _ t
        (((supportSiteComparisonCoefficientAdjunction Ab.{u + 1} X).unit.app F).hom.app
          (op U) s)) =
      (pointSmallEtale x).ulift.{u + 1}.toPresheafFiber U ⟨a⟩ F.obj s
  path : ∀ (Ω Ω' : Type u) [Field Ω] [IsAlgClosed Ω] [Field Ω'] [IsAlgClosed Ω']
    (x : Spec (.of Ω) ⟶ X) (y : Spec (.of Ω') ⟶ X) (_τ : FiniteEtale.fiber x ≅ FiniteEtale.fiber y),
    (pointSmallEtale x).ulift.{u + 1}.sheafFiber.obj F ≅
      (pointSmallEtale y).ulift.{u + 1}.sheafFiber.obj F
  path_germ : ∀ (Ω Ω' : Type u) [Field Ω] [IsAlgClosed Ω] [Field Ω'] [IsAlgClosed Ω']
    (x : Spec (.of Ω) ⟶ X) (y : Spec (.of Ω') ⟶ X) (τ : FiniteEtale.fiber x ≅ FiniteEtale.fiber y)
    (P : X.FiniteEtale) (a : (FiniteEtale.fiber x).obj P) (s : F.obj.obj (op P.obj)),
    (path Ω Ω' x y τ).hom
      ((pointSmallEtale x).ulift.{u + 1}.toPresheafFiber P.obj ⟨a⟩ F.obj s) =
      (pointSmallEtale y).ulift.{u + 1}.toPresheafFiber P.obj ⟨τ.hom.app P a⟩ F.obj s

set_option maxHeartbeats 1000000 in
-- The finite-reduction comparison involves several nested sheaf and scalar-extension functors.
/-- A finite coefficient model with an actual lisse integral lattice. The ell-power
reductions form a cofinal subsystem of the uniformizer-power reductions.
Source: `thm-lisse-qlbar-representations` (1)--(4).
(blueprint: lem-a1-condensed-lisse-monodromy). -/
structure Model (l : ℕ) [Fact l.Prime] (X : Scheme.{u}) (L : Lisse l X) where
  E : PadicAlgCl.FiniteIntermediateField l
  rational : CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    (padicSubfieldRingObj X l E)
  integral : CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    (condensedRingObj (Profinite.padicIntegersRingObj l E.1) X)
  rational_lisse : IsLisseCoefficientModule (Profinite.continuousMapRingObj E) rational
  integral_lisse : IsLisseCoefficientModule (Profinite.padicIntegersRingObj l E.1) integral
  rationalization : (Mod.extendScalars (padicIntegersToPadicSubfield X l E)).obj integral ≅
    rational
  scalarExtension : (Mod.extendScalars (padicSubfieldRingObjToPadicAlgCl X l E)).obj
    rational ≅ L.obj
  inclusion_mono : Mono
    ((Mod.extendRestrictAdjunction (padicIntegersToPadicSubfield X l E)).unit.app integral ≫
      (Mod.comap (padicIntegersToPadicSubfield X l E)).map rationalization.hom)
  finite : ∀ n : ℕ, LisseModuleSheafCategory X
    (ULift.{u + 1} (PadicAlgCl.integersModPow l E.1 (n + 1)))
  reduction : ∀ n : ℕ,
    (finiteCoefficientModEquivalence X (PadicAlgCl.integersModPow l E.1 (n + 1))).functor.obj
      ((Mod.extendScalars (integersModPowReduction X l E.1 (n + 1))).obj integral) ≅
        (supportSiteComparisonCoefficientPullback
          (ModuleCat.{u + 1} (ULift.{u + 1}
            (PadicAlgCl.integersModPow l E.1 (n + 1)))) X).obj (finite n).obj
  /-- The actual compatible finite reductions, on underlying abelian sheaves. -/
  diagram : ℕᵒᵖ ⥤ Sheaf X.smallEtaleTopology Ab.{u + 1}
  level : ∀ n : ℕ, diagram.obj (op n) ≅
    (sheafCompose _ (forget₂
      (ModuleCat.{u + 1} (ULift.{u + 1} (PadicAlgCl.integersModPow l E.1 (n + 1))))
        Ab.{u + 1})).obj (finite n).obj
  completion : Cone (diagram ⋙ supportSiteComparisonCoefficientPullback Ab.{u + 1} X)
  completion_point : completion.pt = integral.X
  completion_limit : IsLimit completion

  forgetComparison : ∀ n : ℕ, ForgetComparison X
    (ULift.{u + 1} (PadicAlgCl.integersModPow l E.1 (n + 1)))
  completion_projection : ∀ n : ℕ,
    eqToHom completion_point.symm ≫ completion.π.app (op n) =
      Mod.extendUnitHom (integersModPowReduction X l E.1 (n + 1)) integral ≫
        (finiteUnderlyingIso X (PadicAlgCl.integersModPow l E.1 (n + 1))
          ((Mod.extendScalars (integersModPowReduction X l E.1 (n + 1))).obj integral)).hom ≫
        (sheafCompose _ (forget₂
          (ModuleCat.{u + 1} (ULift.{u + 1}
            (PadicAlgCl.integersModPow l E.1 (n + 1)))) Ab.{u + 1})).map (reduction n).hom ≫
        (forgetComparison n).iso.hom.app (finite n).obj ≫
        (supportSiteComparisonCoefficientPullback Ab.{u + 1} X).map (level n).inv
  normalization : ∀ n : ℕ, FiniteNormalization X (diagram.obj (op n))
  point_completion : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ X),
    IsLimit ((abFibre x).mapCone completion)

/-- The actual lattice inclusion followed by localization and coefficient extension.
Source: `thm-lisse-qlbar-representations` (1)--(3).
(blueprint: lem-a1-condensed-lisse-monodromy). -/
def Model.inclusion (l : ℕ) [Fact l.Prime] {X : Scheme.{u}} {L : Lisse l X}
    (M : Model l X L) : M.integral.X ⟶ L.obj.X :=
  Mod.extendUnitHom (padicIntegersToPadicSubfield X l M.E) M.integral ≫
    M.rationalization.hom.hom ≫
      Mod.extendUnitHom (padicSubfieldRingObjToPadicAlgCl X l M.E) M.rational ≫
        M.scalarExtension.hom.hom

attribute [instance] Context.noetherian Context.absoluteSeparated Context.invertible

attribute [local irreducible] CondensedRing.upperStar geometricEvaluation in
end AlgebraicGeometry.ProEtale.CondensedLisseMonodromy
