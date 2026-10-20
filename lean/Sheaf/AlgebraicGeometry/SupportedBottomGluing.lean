/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NY
-/
module

public import Sheaf.Paper.PurityFiniteSetting
public import Sheaf.AlgebraicGeometry.EtaleSupportedKernelAdjunction
public import Sheaf.AlgebraicGeometry.DerivedSupportDirectImageComparison
public import Sheaf.Paper.FiniteTateSiteDescent
public import Sheaf.Paper.PbcCoefficientTwists
public import Sheaf.Paper.PbcQbarStandardCohomology
public import Mathlib.Algebra.Homology.Functor
public import WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMap

public import Sheaf.AlgebraicGeometry.EtaleFiniteTwistPullback
public import Sheaf.Paper.RingedTopoiDerivedTensorPullback
public import Sheaf.AlgebraicGeometry.SupportCohomology
import WeilConjectures.Mathlib.CategoryTheory.Preadditive.Injective.Preserves
import WeilConjectures.SixFunctors.BaseChange.DerivedPasting.Vertical
import WeilConjectures.AlgebraicGeometry.EtaleModuleSheavesGrothendieckAbelian
import Sheaf.CategoryTheory.GrothendieckSpectralSequence
import Sheaf.CategoryTheory.FirstQuadrantLowestRowEdge
import WeilConjectures.CategoryTheory.ExactCoupleConvergence
import WeilConjectures.CategoryTheory.GrothendieckEdgeCocycle
import Sheaf.Paper.ComparisonPullbackExact
import Sheaf.CategoryTheory.ModulePullbackTensorIso
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
import Sheaf.CategoryTheory.ModuleRestrictionKernelComparison
import Sheaf.CategoryTheory.LeftModuleDerivedEvaluationForget
import Mathlib.Algebra.Homology.DerivedCategory.DerivabilityStructureInjectives
public import Sheaf.AlgebraicGeometry.ProEtaleSiteComparison
import Sheaf.Paper.PurityComparisonUnitInjectiveModel
import Sheaf.AlgebraicGeometry.CompactSupportComparisonUnit
import Sheaf.AlgebraicGeometry.ProEtaleRestrictionInjectives
import Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Sheaf.AlgebraicGeometry.SupportSiteComparison
import Sheaf.AlgebraicGeometry.SupportComparisonBoundary
import Mathlib.Algebra.Homology.HomologySequenceLemmas
import Sheaf.AlgebraicGeometry.SupportLongExact
import Sheaf.AlgebraicGeometry.ComparisonGlobalCohomologyFiniteNormalized
import Mathlib.CategoryTheory.Sites.Sheaf
import Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted
import Sheaf.Paper.SfCommonStageWeilCohomology

/-!
# Supported cohomology in the lowest local degree

Source: Stacks Project, Tags 015N, 09XP, 09XQ and 099V
(blueprint: lem-pur-supported-bottom-gluing).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u vC uC vD uD
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry WeilConjectures

namespace AlgebraicGeometry.Scheme

/-- The signed finite pro-etale line, with exactly the recorded constant-scalar restriction.
Source: coefficient-twist convention and Stacks 099R
(blueprint: lem-pur-supported-bottom-gluing). -/
abbrev bottomProTwist (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (n : ℕ) (T : Scheme.{u}) (a : ℤ) :=
  (finiteTateConstantRestriction l E n T).obj (finiteCoefficientTwist l E T n a)

end AlgebraicGeometry.Scheme
namespace AlgebraicGeometry

/-- Forget the scalar action, retaining the actual abelian sheaf.
Source: Stacks 03FD and the support convention
(blueprint: lem-pur-supported-bottom-gluing). -/
abbrev bottomForgetEt (A : Type (u + 1)) [CommRing A] (X : Scheme.{u}) :=
  sheafCompose X.smallEtaleTopology (forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1})

/-- The same scalar-forgetting construction on the pro-etale site.
Source: Stacks 03FD (blueprint: lem-pur-supported-bottom-gluing). -/
abbrev bottomForgetPro (A : Type (u + 1)) [CommRing A] (X : Scheme.{u}) :=
  sheafCompose (Scheme.ProEt.topology X)
    (forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1})

/-- The pro-etale sheaf support kernel, in ordinary abelian sheaves.
Source: Stacks 09XP, the identical kernel construction in the other topology
(blueprint: lem-pur-supported-bottom-gluing). -/
def bottomProKernel {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] :=
  kernel (ProEtale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1}
    i.openComplement.ι).unit

/-- Evaluation of an abelian etale sheaf at an object.
Source: Stacks 09XP (blueprint: lem-pur-supported-bottom-gluing). -/
abbrev bottomEvalEt {X : Scheme.{u}} (U : X.Etale) :=
  sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ⋙
    (evaluation _ _).obj (op U)

/-- Evaluation of an abelian pro-etale sheaf at an etale object.
Source: Stacks 099R (blueprint: lem-pur-supported-bottom-gluing). -/
abbrev bottomEvalPro {X : Scheme.{u}} (U : X.Etale) :=
  sheafToPresheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1} ⋙
    (evaluation _ _).obj (op ((Scheme.toProEt X).obj U))

/-- The presheaf of cohomology of the evaluated complex. These are presheaf homology,
not sheafified homology; sheafhood is a conclusion of the bottom-degree theorem.
Source: Stacks 015N and 09XP (blueprint: lem-pur-supported-bottom-gluing). -/
def bottomComplexPresheaf {X : Scheme.{u}}
    (K : CochainComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) ℕ) (d : ℕ) :=
  (((sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).mapHomologicalComplex
    (ComplexShape.up ℕ)).obj K).asFunctor ⋙
      HomologicalComplex.homologyFunctor AddCommGrpCat.{u + 1} (ComplexShape.up ℕ) d

/-- Pro-etale supported groups evaluated on the etale site, before any sheafification.
Source: Stacks 099R (blueprint: lem-pur-supported-bottom-gluing). -/
def bottomProComplexPresheaf {X : Scheme.{u}}
    (K : CochainComplex (Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1}) ℕ)
    (d : ℕ) :=
  (Scheme.toProEt X).op ⋙
    (((sheafToPresheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1}).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj K).asFunctor ⋙
      HomologicalComplex.homologyFunctor AddCommGrpCat.{u + 1} (ComplexShape.up ℕ) d

/-- The canonical edge characterized on cocycles, together with the asserted unique gluing.
Source: Stacks 015N, lowest-row edge and the sheaf axiom
(blueprint: lem-pur-supported-bottom-gluing). -/
structure SupportedBottomEdge {X : Scheme.{u}}
    (K : CochainComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) ℕ) (d : ℕ) where
  edge : bottomComplexPresheaf K d ≅ (K.homology d).obj
  cycles : ∀ U : X.Etale,
    ((((sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj K).asFunctor.obj (op U)).cycles d ≅
        (K.cycles d).obj.obj (op U)
  cycles_inclusion : ∀ U : X.Etale,
    (cycles U).hom ≫ (K.iCycles d).hom.app (op U) =
      ((((sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj K).asFunctor.obj (op U)).iCycles d
  edge_cocycles : ∀ U : X.Etale,
    ((((sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj K).asFunctor.obj (op U)).homologyπ d ≫
        edge.hom.app (op U) = (cycles U).hom ≫ (K.homologyπ d).hom.app (op U)
  gluing : Presheaf.IsSheaf X.smallEtaleTopology (bottomComplexPresheaf K d)

open CategoryTheory.MonoidalCategory
open scoped TensorProduct

/-- The recorded coefficient quotient, indexed by its positive level minus one.
The level is positive in `P`, so `(P.level - 1) + 1 = P.level`.
Source: finite coefficient conventions (blueprint: lem-pur-supported-bottom-gluing). -/
abbrev bottomCoefficient (P : PurityFiniteSetting.{u}) :=
  Scheme.finiteTateCoefficient P.coefficients.l P.extension (P.level - 1)

/-- The existing signed etale root line at the chosen annihilating power.
Source: Stacks 03PK (blueprint: lem-pur-supported-bottom-gluing). -/
abbrev bottomEtaleTwist (P : PurityFiniteSetting.{u}) (T : Scheme.{u})
    (r : ℕ) (hA : ((P.coefficients.l ^ (r + 1) : ℕ) : bottomCoefficient P) = 0) (a : ℤ) :=
  Scheme.finiteEtaleTateSheaf (bottomCoefficient P) (P.coefficients.l ^ (r + 1)) T hA a

/-- The existing signed pro-etale root line, at exactly the same finite coefficient level.
Source: coefficient twists (blueprint: lem-pur-supported-bottom-gluing). -/
abbrev bottomProLine (P : PurityFiniteSetting.{u}) (T : Scheme.{u}) (a : ℤ) :=
  Scheme.bottomProTwist P.coefficients.l P.extension (P.level - 1) T a

/-- The comparison inverse image with these fixed ordinary module coefficients.
Source: Stacks 099R (blueprint: lem-pur-supported-bottom-gluing). -/
abbrev bottomNu (P : PurityFiniteSetting.{u}) (T : Scheme.{u}) :=
  ProEtale.comparisonUpperStar (ModuleCat.{u + 1} (bottomCoefficient P)) T

/-- Evaluation on the actual etale signed line.
Source: Stacks 03EL (blueprint: lem-pur-supported-bottom-gluing). -/
def bottomEtaleEvaluation (P : PurityFiniteSetting.{u}) (T : Scheme.{u})
    (r : ℕ) (hA : ((P.coefficients.l ^ (r + 1) : ℕ) : bottomCoefficient P) = 0) (b : ℕ) :
    bottomEtaleTwist P T r hA (b + 1 : ℕ) ⊗ bottomEtaleTwist P T r hA (.negSucc b) ⟶
      bottomEtaleTwist P T r hA 0 :=
  (ihom.ev (bottomEtaleTwist P T r hA (b + 1 : ℕ))).app (bottomEtaleTwist P T r hA 0)

/-- Signed coefficient comparisons, fixed by roots in nonnegative degrees and by evaluation
in negative degrees. The pullback comparisons are fixed by the same equations.
Source: Stacks 099R, 03PK and 03EL
(blueprint: lem-pur-supported-bottom-gluing). -/
structure SignedFiniteTateComparison (P : PurityFiniteSetting.{u}) where
  theta : ∀ (T : Scheme.{u}) [T.Over (Spec (CommRingCat.of P.field.k))]
    (r : ℕ) (hA : ((P.coefficients.l ^ (r + 1) : ℕ) : bottomCoefficient P) = 0) (a : ℤ),
    (bottomNu P T).obj (bottomEtaleTwist P T r hA a) ≅ bottomProLine P T a
  positive : ∀ (T : Scheme.{u}) [T.Over (Spec (CommRingCat.of P.field.k))]
    (r : ℕ) (hA : ((P.coefficients.l ^ (r + 1) : ℕ) : bottomCoefficient P) = 0) (a : ℕ),
    Scheme.IsFiniteTateSiteComparison P.coefficients.l P.extension (P.level - 1) T
      r hA a (theta T r hA a)
  evaluation : ∀ (T : Scheme.{u}) [T.Over (Spec (CommRingCat.of P.field.k))] (b : ℕ),
    bottomProLine P T (b + 1 : ℕ) ⊗ bottomProLine P T (.negSucc b) ⟶ bottomProLine P T 0
  evaluation_sections : ∀ (T : Scheme.{u}) [T.Over (Spec (CommRingCat.of P.field.k))]
    (b : ℕ) (W : T.ProEtᵒᵖ) (x : (bottomProLine P T (b + 1 : ℕ)).obj.obj W)
    (f : (bottomProLine P T (.negSucc b)).obj.obj W),
    (evaluation T b).hom.app W
      ((Functor.LaxMonoidal.μ
        (sheafToPresheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} (bottomCoefficient P)))
        _ _).app W (x ⊗ₜ[_] f)) = f.app (op (Over.mk (𝟙 W.unop))) x
  negative : ∀ (T : Scheme.{u}) [T.Over (Spec (CommRingCat.of P.field.k))]
    (r : ℕ) (hA : ((P.coefficients.l ^ (r + 1) : ℕ) : bottomCoefficient P) = 0) (b : ℕ),
    (bottomNu P T).map (bottomEtaleEvaluation P T r hA b) ≫ (theta T r hA 0).hom =
      Functor.OplaxMonoidal.δ (bottomNu P T) _ _ ≫
        tensorHom (theta T r hA (b + 1 : ℕ)).hom (theta T r hA (.negSucc b)).hom ≫ evaluation T b
  pullback : ∀ (T T' : Scheme.{u}) [T.Over (Spec (CommRingCat.of P.field.k))]
    [T'.Over (Spec (CommRingCat.of P.field.k))] (v : T' ⟶ T)
    (r : ℕ) (hA : ((P.coefficients.l ^ (r + 1) : ℕ) : bottomCoefficient P) = 0),
    Σ' (c : ∀ a : ℤ, (Etale.upperStar (ModuleCat.{u + 1} (bottomCoefficient P)) v).obj
          (bottomEtaleTwist P T r hA a) ≅ bottomEtaleTwist P T' r hA a)
      (e : ∀ a : ℤ, (ProEtale.upperStar (ModuleCat.{u + 1} (bottomCoefficient P)) v).obj
          (bottomProLine P T a) ≅ bottomProLine P T' a),
      (∀ a : ℕ, Scheme.IsFiniteTateEtalePullback P.coefficients.l P.extension (P.level - 1)
        T v r hA a (c a) ∧
        Scheme.IsFiniteTateProPullback P.coefficients.l P.extension (P.level - 1)
          T v a (e a)) ∧
      (∀ b : ℕ,
        (Etale.upperStar (ModuleCat.{u + 1} (bottomCoefficient P)) v).map
            (bottomEtaleEvaluation P T r hA b) ≫ (c 0).hom =
          Functor.OplaxMonoidal.δ (Etale.upperStar (ModuleCat.{u + 1} (bottomCoefficient P)) v)
            _ _ ≫ tensorHom (c (b + 1 : ℕ)).hom (c (.negSucc b)).hom ≫
              bottomEtaleEvaluation P T' r hA b) ∧
      (∀ b : ℕ,
        (ProEtale.upperStar (ModuleCat.{u + 1} (bottomCoefficient P)) v).map
            (evaluation T b) ≫ (e 0).hom =
          Functor.OplaxMonoidal.δ
            (ProEtale.upperStar (ModuleCat.{u + 1} (bottomCoefficient P)) v) _ _ ≫
              tensorHom (e (b + 1 : ℕ)).hom (e (.negSucc b)).hom ≫ evaluation T' b) ∧
      (∀ a : ℤ,
        (ProEtale.upperStar (ModuleCat.{u + 1} (bottomCoefficient P)) v).mapIso
            (theta T r hA a) ≪≫ e a =
          (ProEtale.comparisonUpperStarCompUpperStarIso
            (ModuleCat.{u + 1} (bottomCoefficient P)) v).app (bottomEtaleTwist P T r hA a) ≪≫
              (bottomNu P T').mapIso (c a) ≪≫ theta T' r hA a)

/-- The normalized etale coefficient restriction, on the underlying abelian sheaves.
It uses the actual root/evaluation-normalized pullback data stored in Theta.
Source: Stacks 03PK, finite-twist pullback (blueprint: lem-pur-supported-bottom-gluing). -/
def bottomLocalCoefficientEt {P : PurityFiniteSetting.{u}} (Theta : SignedFiniteTateComparison P)
    {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of P.field.k))] (U : X.Etale)
    (r : ℕ) (hA : ((P.coefficients.l ^ (r + 1) : ℕ) : bottomCoefficient P) = 0) (a : ℤ) :
    (Etale.localizationRestriction AddCommGrpCat.{u + 1} U.hom inferInstance).obj
      ((bottomForgetEt (bottomCoefficient P) X).obj (bottomEtaleTwist P X r hA a)) ≅
    (bottomForgetEt (bottomCoefficient P) U.left).obj (bottomEtaleTwist P U.left r hA a) :=
  letI : U.left.Over (Spec (CommRingCat.of P.field.k)) :=
    ⟨U.hom ≫ (X ↘ Spec (CommRingCat.of P.field.k))⟩
  (bottomForgetEt (bottomCoefficient P) U.left).mapIso
    (((Etale.upperStarIsoLocalizationRestriction
      (ModuleCat.{u + 1} (bottomCoefficient P)) U.hom inferInstance).app
        (bottomEtaleTwist P X r hA a)).symm ≪≫
      (Theta.pullback X U.left U.hom r hA).1 a)

/-- The normalized signed pro-etale coefficient restriction, including its negative duals.
Source: Stacks 099R and evaluation duality (blueprint: lem-pur-supported-bottom-gluing). -/
def bottomLocalCoefficientPro {P : PurityFiniteSetting.{u}} (Theta : SignedFiniteTateComparison P)
    {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of P.field.k))] (U : X.Etale)
    (r : ℕ) (hA : ((P.coefficients.l ^ (r + 1) : ℕ) : bottomCoefficient P) = 0) (a : ℤ) :
    (ProEtale.localizationRestriction AddCommGrpCat.{u + 1} U.hom inferInstance).obj
      ((bottomForgetPro (bottomCoefficient P) X).obj (bottomProLine P X a)) ≅
    (bottomForgetPro (bottomCoefficient P) U.left).obj (bottomProLine P U.left a) :=
  letI : U.left.Over (Spec (CommRingCat.of P.field.k)) :=
    ⟨U.hom ≫ (X ↘ Spec (CommRingCat.of P.field.k))⟩
  (bottomForgetPro (bottomCoefficient P) U.left).mapIso
    (((ProEtale.upperStarIsoLocalizationRestriction
      (ModuleCat.{u + 1} (bottomCoefficient P)) U.hom inferInstance).app
        (bottomProLine P X a)).symm ≪≫
      (Theta.pullback X U.left U.hom r hA).2.1 a)

/-- The scalar-forgotten comparison adjunct. This is the specified coefficient unit,
followed by the coefficient identification, rather than an arbitrary quasi-isomorphism.
Source: Stacks 099V (blueprint: lem-pur-supported-bottom-gluing). -/
def bottomCoefficientUnit (P : PurityFiniteSetting.{u}) (X : Scheme.{u})
    (r : ℕ) (hA : ((P.coefficients.l ^ (r + 1) : ℕ) : bottomCoefficient P) = 0) (a : ℤ)
    (theta : (bottomNu P X).obj (bottomEtaleTwist P X r hA a) ≅ bottomProLine P X a) :=
  (bottomForgetEt (bottomCoefficient P) X).map
    ((ProEtale.comparisonAdjunction (ModuleCat.{u + 1} (bottomCoefficient P)) X).unit.app
      (bottomEtaleTwist P X r hA a) ≫
        (ProEtale.comparisonLowerStar (ModuleCat.{u + 1} (bottomCoefficient P)) X).map theta.hom)

/-- The inclusion of a section kernel into ordinary sections.
Source: Stacks 09XP (blueprint: lem-pur-supported-bottom-gluing). -/
def bottomSupportInclusion {C : Type uC} [Category.{vC} C] (J : GrothendieckTopology C)
    {V W : C} (j : W ⟶ V) :
    Sheaf.supportedSectionsFunctor J AddCommGrpCat.{u + 1} j ⟶
      sheafToPresheaf J AddCommGrpCat.{u + 1} ⋙ (evaluation _ _).obj (op V) where
  app F := kernel.ι (F.obj.map j.op)
  naturality f := by simp [Sheaf.supportedSectionsFunctor]

/-- The literal final-object evaluation after etale localization.
Source: Stacks 09XP (blueprint: lem-pur-supported-bottom-gluing). -/
def bottomRestrictionEvaluationEt {X : Scheme.{u}} (U : X.Etale) :
    Etale.localizationRestriction AddCommGrpCat.{u + 1} U.hom inferInstance ⋙
      bottomEvalEt (Scheme.Etale.mk (𝟙 U.left)) ≅ bottomEvalEt U :=
  NatIso.ofComponents
    (fun F ↦ F.obj.mapIso
      ((MorphismProperty.Over.isoMk (Iso.refl _)
        (by change 𝟙 _ ≫ (𝟙 _ ≫ U.hom) = U.hom; simp only [Category.id_comp]) :
        U ≅ (MorphismProperty.Over.map ⊤ (inferInstance : Etale U.hom)).obj
          (Scheme.Etale.mk (𝟙 U.left)))).op)
    (by intro F G f; exact (f.hom.naturality _).symm)

/-- The literal final-object evaluation after pro-etale localization.
Source: Stacks 099R (blueprint: lem-pur-supported-bottom-gluing). -/
def bottomRestrictionEvaluationPro {X : Scheme.{u}} (U : X.Etale) :
    ProEtale.localizationRestriction AddCommGrpCat.{u + 1} U.hom inferInstance ⋙
      bottomEvalPro (Scheme.Etale.mk (𝟙 U.left)) ≅ bottomEvalPro U :=
  NatIso.ofComponents
    (fun F ↦ F.obj.mapIso
      ((MorphismProperty.Over.isoMk (Iso.refl _)
        (by change 𝟙 _ ≫ (𝟙 _ ≫ U.hom) = U.hom; simp only [Category.id_comp]) :
        (Scheme.toProEt X).obj U ≅
          (MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale U.hom)).obj
            (Scheme.ProEt.mk (𝟙 U.left)))).op)
    (by intro F G f; exact (f.hom.naturality _).symm)

/-- Localization adds sheaf morphisms sectionwise.
Source: Stacks 09XP (blueprint: lem-pur-supported-bottom-gluing). -/
instance bottomRestrictionEt_additive {X V : Scheme.{u}} (f : V ⟶ X) (h : Etale f) :
    (Etale.localizationRestriction AddCommGrpCat.{u + 1} f h).Additive where
  map_add := by intros; rfl

/-- Pro-etale localization adds sheaf morphisms sectionwise.
Source: Stacks 099R (blueprint: lem-pur-supported-bottom-gluing). -/
instance bottomRestrictionPro_additive {X V : Scheme.{u}} (f : V ⟶ X) (h : WeaklyEtale f) :
    (ProEtale.localizationRestriction AddCommGrpCat.{u + 1} f h).Additive where
  map_add := by intros; rfl

/-- A localized injective resolution and the actual kernel identity on its evaluated terms.
All identifications are conclusions of the theorem. The augmentation and kernel-inclusion
identities exclude arbitrary changes of the supported classes.
Source: Stacks 09XP and 09XQ (blueprint: lem-pur-supported-bottom-gluing). -/
structure SupportedLocalResolution
    {C : Type uC} [Category.{vC} C] [Abelian C]
    {D : Type uD} [Category.{vD} D] [Abelian D]
    (F : C) (I : InjectiveResolution F) (Q : C ⥤ C) [Q.Additive]
    (R : C ⥤ D) [R.Additive] (S : D ⥤ AddCommGrpCat.{u + 1}) [S.Additive]
    (E : C ⥤ AddCommGrpCat.{u + 1}) [E.Additive]
    (G : D ⥤ AddCommGrpCat.{u + 1})
    (alpha : Q ⋙ E ⟶ E) (beta : S ⟶ G) (epsilon : R ⋙ G ≅ E) where
  resolution : InjectiveResolution (R.obj F)
  restriction : resolution.cocomplex ≅ (R.mapHomologicalComplex (ComplexShape.up ℕ)).obj
    I.cocomplex
  augmentation : resolution.ι.f 0 ≫ restriction.hom.f 0 = R.map (I.ι.f 0)
  kernel : (S.mapHomologicalComplex (ComplexShape.up ℕ)).obj resolution.cocomplex ≅
    (E.mapHomologicalComplex (ComplexShape.up ℕ)).obj
      ((Q.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex)
  kernel_sections : ∀ n : ℕ, kernel.hom.f n ≫ alpha.app (I.cocomplex.X n) =
    beta.app (resolution.cocomplex.X n) ≫ G.map (restriction.hom.f n) ≫
      epsilon.hom.app (I.cocomplex.X n)

/-- The actual localized supported group computed by the preceding normalized resolution.
Source: Stacks 09XP, injective-resolution formula
(blueprint: lem-pur-supported-bottom-gluing). -/
def SupportedLocalResolution.groupIso
    {C : Type uC} [Category.{vC} C] [Abelian C]
    {D : Type uD} [Category.{vD} D] [Abelian D] [EnoughInjectives D]
    {F : C} {I : InjectiveResolution F} {Q : C ⥤ C} [Q.Additive]
    {R : C ⥤ D} [R.Additive] {S : D ⥤ AddCommGrpCat.{u + 1}} [S.Additive]
    {E : C ⥤ AddCommGrpCat.{u + 1}} [E.Additive] {G : D ⥤ AddCommGrpCat.{u + 1}}
    {alpha : Q ⋙ E ⟶ E} {beta : S ⟶ G} {epsilon : R ⋙ G ≅ E}
    (L : SupportedLocalResolution F I Q R S E G alpha beta epsilon) (d : ℕ) :
    (S.rightDerived d).obj (R.obj F) ≅
      ((E.mapHomologicalComplex (ComplexShape.up ℕ)).obj
        ((Q.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex)).homology d :=
  L.resolution.isoRightDerivedObj S d ≪≫
    (HomologicalComplex.homologyFunctor AddCommGrpCat.{u + 1}
      (ComplexShape.up ℕ) d).mapIso L.kernel

/-- The common injective model fixes the supported comparison by the comparison adjunct
and by the identity on support kernels. This is the resolution normalization of the
composite `RΓ_Z(η)` followed by the direct-image comparison and the signed coefficient map.
Source: Stacks 099V, 09XP; normalization in lem-pur-derived-support-comparison-direct-image
(blueprint: lem-pur-supported-bottom-gluing). -/
structure SupportedBottomModel (P : PurityFiniteSetting.{u}) (X : Scheme.{u})
    [X.Over (Spec (CommRingCat.of P.field.k))] {Z : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i]
    (r : ℕ) (hA : ((P.coefficients.l ^ (r + 1) : ℕ) : bottomCoefficient P) = 0) (a : ℤ)
    (Theta : SignedFiniteTateComparison P) where
  [additiveEt : (Etale.supportedKernel i.openComplement.ι).Additive]
  [additivePro : (bottomProKernel i).Additive]
  I : InjectiveResolution
    ((bottomForgetEt (bottomCoefficient P) X).obj (bottomEtaleTwist P X r hA a))
  J : InjectiveResolution
    ((bottomForgetPro (bottomCoefficient P) X).obj (bottomProLine P X a))
  resolution :
    ((ProEtale.comparisonLowerStar AddCommGrpCat.{u + 1} X).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj J.cocomplex ≅ I.cocomplex
  unit_normalization : bottomCoefficientUnit P X r hA a (Theta.theta X r hA a) ≫
    (ProEtale.comparisonLowerStar AddCommGrpCat.{u + 1} X).map (J.ι.f 0) ≫
      resolution.hom.f 0 = I.ι.f 0
  kernelIdentity : bottomProKernel i ⋙ ProEtale.comparisonLowerStar AddCommGrpCat.{u + 1} X ≅
    ProEtale.comparisonLowerStar AddCommGrpCat.{u + 1} X ⋙
      Etale.supportedKernel i.openComplement.ι
  kernel_normalization : ∀ F : Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1},
    (kernelIdentity.hom.app F) ≫
      (kernel.ι (Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1}
        i.openComplement.ι).unit).app
          ((ProEtale.comparisonLowerStar AddCommGrpCat.{u + 1} X).obj F) =
    (ProEtale.comparisonLowerStar AddCommGrpCat.{u + 1} X).map
      ((kernel.ι (ProEtale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1}
        i.openComplement.ι).unit).app F)
  localEt : ∀ U : X.Etale,
    SupportedLocalResolution _ I (Etale.supportedKernel i.openComplement.ι)
      (Etale.localizationRestriction AddCommGrpCat.{u + 1} U.hom inferInstance)
      (Etale.supportSections (pullback.snd i U.hom)) (bottomEvalEt U)
      (bottomEvalEt (Scheme.Etale.mk (𝟙 U.left)))
      (Functor.whiskerRight
        (kernel.ι (Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1}
          i.openComplement.ι).unit) (bottomEvalEt U))
      (bottomSupportInclusion _ (Etale.supportRestrictionArrow (pullback.snd i U.hom)))
      (bottomRestrictionEvaluationEt U)
  localPro : ∀ U : X.Etale,
    SupportedLocalResolution _ J (bottomProKernel i)
      (ProEtale.localizationRestriction AddCommGrpCat.{u + 1} U.hom inferInstance)
      (Sheaf.supportedSectionsFunctor (Scheme.ProEt.topology U.left) AddCommGrpCat.{u + 1}
        (ProEtale.supportRestrictionArrow (pullback.snd i U.hom))) (bottomEvalPro U)
      (bottomEvalPro (Scheme.Etale.mk (𝟙 U.left)))
      (Functor.whiskerRight
        (kernel.ι (ProEtale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1}
          i.openComplement.ι).unit) (bottomEvalPro U))
      (bottomSupportInclusion _ (ProEtale.supportRestrictionArrow (pullback.snd i U.hom)))
      (bottomRestrictionEvaluationPro U)

namespace SupportedBottomModel

/-- The actual sheaf-support complex of the etale injective resolution.
Its homology is the recorded derived cohomology sheaf, equivalently R^q P(F).
Source: Stacks 015N and 09XQ (blueprint: lem-pur-supported-bottom-gluing). -/
def etaleComplex {P : PurityFiniteSetting.{u}} {X : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of P.field.k))] {Z : Scheme.{u}} {i : Z ⟶ X}
    [IsClosedImmersion i] {r : ℕ}
    {hA : ((P.coefficients.l ^ (r + 1) : ℕ) : bottomCoefficient P) = 0} {a : ℤ}
    {Theta : SignedFiniteTateComparison P} (M : SupportedBottomModel P X i r hA a Theta) :=
  letI := M.additiveEt
  ((Etale.supportedKernel i.openComplement.ι).mapHomologicalComplex
    (ComplexShape.up ℕ)).obj M.I.cocomplex

/-- The identical pro-etale sheaf-support complex, on its injective resolution.
Source: Stacks 09XP and 099R (blueprint: lem-pur-supported-bottom-gluing). -/
def proComplex {P : PurityFiniteSetting.{u}} {X : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of P.field.k))] {Z : Scheme.{u}} {i : Z ⟶ X}
    [IsClosedImmersion i] {r : ℕ}
    {hA : ((P.coefficients.l ^ (r + 1) : ℕ) : bottomCoefficient P) = 0} {a : ℤ}
    {Theta : SignedFiniteTateComparison P} (M : SupportedBottomModel P X i r hA a Theta) :=
  letI := M.additivePro
  ((bottomProKernel i).mapHomologicalComplex (ComplexShape.up ℕ)).obj M.J.cocomplex

/-- The identity of support kernels in the common injective model.
The augmentation equation in M fixes the comparison adjunction unit; the kernel equation
fixes the direct-image comparison b. Hence the inverse of this identity is exactly the
canonical supported comparison specified in the node, including the signed theta.
Source: Stacks 099V; lem-pur-derived-support-comparison-direct-image, kernel normalization
(blueprint: lem-pur-supported-bottom-gluing). -/
def supportComplexIso {P : PurityFiniteSetting.{u}} {X : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of P.field.k))] {Z : Scheme.{u}} {i : Z ⟶ X}
    [IsClosedImmersion i] {r : ℕ}
    {hA : ((P.coefficients.l ^ (r + 1) : ℕ) : bottomCoefficient P) = 0} {a : ℤ}
    {Theta : SignedFiniteTateComparison P} (M : SupportedBottomModel P X i r hA a Theta) :
    ((ProEtale.comparisonLowerStar AddCommGrpCat.{u + 1} X).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj M.proComplex ≅ M.etaleComplex :=
  letI := M.additiveEt
  letI := M.additivePro
  (NatIso.mapHomologicalComplex M.kernelIdentity (ComplexShape.up ℕ)).app M.J.cocomplex ≪≫
    ((Etale.supportedKernel i.openComplement.ι).mapHomologicalComplex
      (ComplexShape.up ℕ)).mapIso M.resolution

/-- The canonical supported comparison on every etale object, with its restriction maps.
It is the inverse of the normalized identity on injective support complexes above.
Source: Stacks 099V and 09XP (blueprint: lem-pur-supported-bottom-gluing). -/
def comparison {P : PurityFiniteSetting.{u}} {X : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of P.field.k))] {Z : Scheme.{u}} {i : Z ⟶ X}
    [IsClosedImmersion i] {r : ℕ}
    {hA : ((P.coefficients.l ^ (r + 1) : ℕ) : bottomCoefficient P) = 0} {a : ℤ}
    {Theta : SignedFiniteTateComparison P} (M : SupportedBottomModel P X i r hA a Theta)
    (d : ℕ) : bottomComplexPresheaf M.etaleComplex d ≅
      bottomProComplexPresheaf M.proComplex d :=
  (Functor.isoWhiskerRight
    (HomologicalComplex.complexOfFunctorsToFunctorToComplex.mapIso
      (((sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).mapHomologicalComplex
        (ComplexShape.up ℕ)).mapIso M.supportComplexIso))
    (HomologicalComplex.homologyFunctor AddCommGrpCat.{u + 1}
      (ComplexShape.up ℕ) d)).symm

/-- The pro-etale edge to exactly the same local-cohomology sheaf sections.
Source: Stacks 015N and 099V (blueprint: lem-pur-supported-bottom-gluing). -/
def proEdge {P : PurityFiniteSetting.{u}} {X : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of P.field.k))] {Z : Scheme.{u}} {i : Z ⟶ X}
    [IsClosedImmersion i] {r : ℕ}
    {hA : ((P.coefficients.l ^ (r + 1) : ℕ) : bottomCoefficient P) = 0} {a : ℤ}
    {Theta : SignedFiniteTateComparison P} (M : SupportedBottomModel P X i r hA a Theta)
    {d : ℕ} (e : SupportedBottomEdge M.etaleComplex d) :
    bottomProComplexPresheaf M.proComplex d ≅ (M.etaleComplex.homology d).obj :=
  (M.comparison d).symm ≪≫ e.edge

/-- The displayed etale edge on the actual supported group on U, with the coefficient
identified with A_U(a) by the finite-twist pullback theorem.
Source: Stacks 015N and 09XP (blueprint: lem-pur-supported-bottom-gluing). -/
def etaleEdgeAt {P : PurityFiniteSetting.{u}} {X : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of P.field.k))] {Z : Scheme.{u}} {i : Z ⟶ X}
    [IsClosedImmersion i] {r : ℕ}
    {hA : ((P.coefficients.l ^ (r + 1) : ℕ) : bottomCoefficient P) = 0} {a : ℤ}
    {Theta : SignedFiniteTateComparison P} (M : SupportedBottomModel P X i r hA a Theta)
    {d : ℕ} (e : SupportedBottomEdge M.etaleComplex d) (U : X.Etale) :
    Etale.supportCohomology (pullback.snd i U.hom) d
      ((Etale.localizationRestriction AddCommGrpCat.{u + 1} U.hom inferInstance).obj
        ((bottomForgetEt (bottomCoefficient P) X).obj (bottomEtaleTwist P X r hA a))) ≅
      (M.etaleComplex.homology d).obj.obj (op U) :=
  letI := M.additiveEt
  (M.localEt U).groupIso d ≪≫ e.edge.app (op U)

/-- The pro-etale edge on the actual abelian-sheaf supported group on U, using the inverse
of the specified supported comparison and hence the same local-cohomology sheaf sections.
Source: Stacks 015N, 09XP and 099V (blueprint: lem-pur-supported-bottom-gluing). -/
def proEdgeAt {P : PurityFiniteSetting.{u}} {X : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of P.field.k))] {Z : Scheme.{u}} {i : Z ⟶ X}
    [IsClosedImmersion i] {r : ℕ}
    {hA : ((P.coefficients.l ^ (r + 1) : ℕ) : bottomCoefficient P) = 0} {a : ℤ}
    {Theta : SignedFiniteTateComparison P} (M : SupportedBottomModel P X i r hA a Theta)
    {d : ℕ} (e : SupportedBottomEdge M.etaleComplex d) (U : X.Etale) :
    ((Sheaf.supportedSectionsFunctor (Scheme.ProEt.topology U.left) AddCommGrpCat.{u + 1}
      (ProEtale.supportRestrictionArrow (pullback.snd i U.hom))).rightDerived d).obj
        ((ProEtale.localizationRestriction AddCommGrpCat.{u + 1} U.hom inferInstance).obj
          ((bottomForgetPro (bottomCoefficient P) X).obj (bottomProLine P X a))) ≅
      (M.etaleComplex.homology d).obj.obj (op U) :=
  letI := M.additivePro
  (M.localPro U).groupIso d ≪≫ (M.proEdge e).app (op U)

/-- The displayed etale edge with literally the prescribed A_U(a) coefficient sheaf.
Source: Stacks 015N, 09XP and 03PK (blueprint: lem-pur-supported-bottom-gluing). -/
def etaleTateEdgeAt {P : PurityFiniteSetting.{u}} {X : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of P.field.k))] {Z : Scheme.{u}} {i : Z ⟶ X}
    [IsClosedImmersion i] {r : ℕ}
    {hA : ((P.coefficients.l ^ (r + 1) : ℕ) : bottomCoefficient P) = 0} {a : ℤ}
    {Theta : SignedFiniteTateComparison P} (M : SupportedBottomModel P X i r hA a Theta)
    {d : ℕ} (e : SupportedBottomEdge M.etaleComplex d) (U : X.Etale) :
    Etale.supportCohomology (pullback.snd i U.hom) d
      ((bottomForgetEt (bottomCoefficient P) U.left).obj
        (bottomEtaleTwist P U.left r hA a)) ≅
      (M.etaleComplex.homology d).obj.obj (op U) :=
  ((Etale.supportSections (pullback.snd i U.hom)).rightDerived d).mapIso
    (bottomLocalCoefficientEt Theta U r hA a).symm ≪≫ M.etaleEdgeAt e U

/-- The displayed pro-etale edge with literally the prescribed A_U^pro(a) coefficient sheaf.
Source: Stacks 015N, 09XP and 099V (blueprint: lem-pur-supported-bottom-gluing). -/
def proTateEdgeAt {P : PurityFiniteSetting.{u}} {X : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of P.field.k))] {Z : Scheme.{u}} {i : Z ⟶ X}
    [IsClosedImmersion i] {r : ℕ}
    {hA : ((P.coefficients.l ^ (r + 1) : ℕ) : bottomCoefficient P) = 0} {a : ℤ}
    {Theta : SignedFiniteTateComparison P} (M : SupportedBottomModel P X i r hA a Theta)
    {d : ℕ} (e : SupportedBottomEdge M.etaleComplex d) (U : X.Etale) :
    ((Sheaf.supportedSectionsFunctor (Scheme.ProEt.topology U.left) AddCommGrpCat.{u + 1}
      (ProEtale.supportRestrictionArrow (pullback.snd i U.hom))).rightDerived d).obj
        ((bottomForgetPro (bottomCoefficient P) U.left).obj (bottomProLine P U.left a)) ≅
      (M.etaleComplex.homology d).obj.obj (op U) :=
  ((Sheaf.supportedSectionsFunctor (Scheme.ProEt.topology U.left) AddCommGrpCat.{u + 1}
    (ProEtale.supportRestrictionArrow (pullback.snd i U.hom))).rightDerived d).mapIso
      (bottomLocalCoefficientPro Theta U r hA a).symm ≪≫ M.proEdgeAt e U

end SupportedBottomModel

/-- Lowest-local-degree supported classes on both sites have canonical, restriction-compatible
edge isomorphisms to sections of the same local-cohomology sheaf, and unique gluing.
The local-resolution fields identify the presheaves with the supported groups on every U.
The finite-twist pullback theorem identifies their restricted coefficients with A_U(a).
All signed comparisons, including negative evaluation duality, are part of the conclusion.
Source: Stacks 015N, 09XP, 09XQ, 099V and 03PK
(blueprint: lem-pur-supported-bottom-gluing).

Proof:
1. Finite etale twists commute with restriction for every integer a. The support kernel
commutes with restriction, since on W both kernels are ker(G(W) -> G(W minus Z_W)).
Etale restriction preserves injectives, so the localized resolutions compute the specified
supported groups and the local cohomology sheaves.
2. The support-kernel closed adjunction makes P=i_*i^!_0 preserve injectives: i^!_0 is
right adjoint to the exact i_*, and i_* preserves injectives. Thus P of an injective is
acyclic for sections on every etale U.
3. Apply the Grothendieck spectral sequence to P followed by sections on U, obtaining
H^p(U,H^q(P(I))) => H_Z^(p+q)(U,F). Its finite decreasing filtration converges.
4. Vanishing below d leaves only (0,d) in total degree d. Exhaustiveness gives F^0=H^d
and separation gives F^(d+1)=0. The lowest-row edge lemma gives the asserted isomorphism.
5. The Grothendieck cocycle-edge description is precisely edge_cocycles. It uses the same
sheaf quotient on every U, proving naturality for further etale restriction.
6. Nonnegative finite Tate descent gives theta and its root normalization for all powers.
7. Pull back evaluation at negative a. In local frames the map sends the dual frame to
its dual; changes of frame act inversely, so the maps glue and commute with pullback.
8. The module/abelian restriction-kernel comparison preserves support kernels, evaluations
and connecting maps. Hence all support groups here are those of the underlying abelian
sheaves, without treating module injectives as abelian injectives.
9. Choose a pro-etale abelian injective resolution J. Exact comparison inverse image makes
nu_*J termwise injective. The comparison unit and theta make its augmentation an etale
injective resolution I. Both resolutions remain injective after etale restriction.
10. The canonical supported comparison is RΓ_Z of the unit, then the direct-image comparison
b, then theta. Its normalization is the identity between the two injective support kernels;
these are exactly unit_normalization, kernel_normalization and supportComplexIso.
11. The same degreewise short exact restriction-kernel sequences give the support boundary
maps with identical signs, by naturality of the long exact sequence.
12. Restriction on every etale V -> U is evaluation of the same complex maps. Thus comparison
and both edges commute with restriction, also in degree zero.
13. The sheaf axiom for H^d(P(I)) gives existence and uniqueness of glued sections. Transfer
along the etale edge and then the comparison gives unique gluing of supported classes on
both sites, for all etale covers and hence for Zariski covers. No higher-degree claim is made.
-/
theorem supported_bottom_gluing (P : PurityFiniteSetting.{u}) (X : Scheme.{u})
    [X.Over (Spec (CommRingCat.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of P.field.k))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of P.field.k))]
    [IsSeparated (X ↘ Spec (CommRingCat.of P.field.k))]
    {Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] (a : ℤ) (r : ℕ)
    (hA : ((P.coefficients.l ^ (r + 1) : ℕ) : bottomCoefficient P) = 0) :
    ∃ (Theta : SignedFiniteTateComparison P) (M : SupportedBottomModel P X i r hA a Theta),
      ∀ d : ℕ, (∀ q : ℕ, q < d → IsZero (M.etaleComplex.homology q)) →
        Nonempty (SupportedBottomEdge M.etaleComplex d) ∧
          Presheaf.IsSheaf X.smallEtaleTopology (bottomProComplexPresheaf M.proComplex d) := by
  sorry

end AlgebraicGeometry
