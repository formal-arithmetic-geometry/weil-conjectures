/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.VerdierExchangeData
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import WeilConjectures.AlgebraicGeometry.ConstructibleExceptionalAdjunctionCoefficients
public import Mathlib.CategoryTheory.Adjunction.Mates
public import WeilConjectures.CategoryTheory.RingedSiteDualityMaps
public import WeilConjectures.AlgebraicGeometry.CoefficientRingedTensorHomModelSupplement
public import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.RingTheory.Flat.CategoryTheory
public import WeilConjectures.AlgebraicGeometry.CoefficientHomRepresentativeEvaluation
public import WeilConjectures.Algebra.Homology.DerivedInternalHomOfUniverses
public import WeilConjectures.Algebra.Homology.DerivedInternalHom
public import WeilConjectures.SixFunctors.Etale.Derived.Hom
public import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.CategoryTheory.Generator.Basic
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
public import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMapOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplex
public import WeilConjectures.Algebra.Homology.HomComplexSectionsQuasiIsoOfUniverses
public import WeilConjectures.CategoryTheory.Sites.RGammaDerivedLimitSupplement
public import Mathlib.Algebra.Category.Grp.Abelian
public import WeilConjectures.Algebra.Homology.HomComplexSectionsDerivedNaturalityOfUniverses
public import WeilConjectures.Algebra.Homology.RhomIntoKInjectiveLocal
public import WeilConjectures.Algebra.Homology.KInjectiveRestrictLocalizedOfUniverses
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import WeilConjectures.Algebra.Homology.LocalizedRestrictionAdjunctionOfUniverses
public import WeilConjectures.Algebra.Homology.LocalizedRestrictionExtensionExistsOfUniverses
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import WeilConjectures.Algebra.Homology.HomComplexSectionsHomotopyNaturalityOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplexProjections
public import WeilConjectures.Algebra.Homology.HomComplexSectionsCanonicalComparisonOfUniverses
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexShift
public import WeilConjectures.Algebra.Homology.HomComplexSectionsCochainsOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplexSectionsCochainsCommOfUniverses
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology
public import Mathlib.Algebra.Category.Grp.EpiMono
public import WeilConjectures.Algebra.Homology.LocalizedModuleRestrictionQuasiIsoOfUniverses
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
public import WeilConjectures.Algebra.Homology.QuasiIsoOfSectionsOfUniverses
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.Algebra.Homology.Functor
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
public import WeilConjectures.Algebra.Homology.HomComplexComponents
public import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMap
public import WeilConjectures.Algebra.Homology.HomTensorDegreewiseEquation
public import WeilConjectures.Algebra.Homology.SignedDoubleHomConeSupplement
public import Mathlib.CategoryTheory.Triangulated.Opposite.Pretriangulated
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import WeilConjectures.AlgebraicGeometry.FieldShriekCompositionQcqs

/-! # Verdier-duality exchange

Source: blueprint main-20261015, sec-six-functors/sk-thm-sf-verdier-exchange,
order 2503 (blueprint: sk-thm-sf-verdier-exchange).

The exceptional functors below are the existing constructible adjoints. In particular
none of these definitions uses an ambient exceptional-adjoint datum.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genInjectivity false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genCtorIdx false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
universe u a b c d e v w z
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme


namespace WeilConjectures
namespace VerdierExchange
open CategoryTheory.Pretriangulated.Opposite

variable (l : ℕ) [Fact l.Prime]
  (Ω : Type u) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]

open ConstructibleExceptionalCoefficients

section Geometry
variable (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
  {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
  [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))] [Z.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
  [LocallyOfFiniteType (Z ↘ Spec (.of D.k))] [QuasiCompact (Z ↘ Spec (.of D.k))]
  [f.IsOver (Spec (.of D.k))] [g.IsOver (Spec (.of D.k))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
  (Sf : System.{u} l Ω D hl (f := f)) (Sg : System.{u} l Ω D hl (f := g))
  (Sfg : System.{u} l Ω D hl (f := f ≫ g))
  (cf : Compactification f) (cg : Compactification g) (cfg : Compactification (f ≫ g))

/-- All-stage exchange on the actual coefficient categories. These are conclusions,
including the realizations: there is no extra hypothesis about existence of an ambient
exceptional adjoint, a duality, a projection isomorphism, or a coefficient comparison.
The integral compositor normalization and all finite reductions fix c; rational and
common-stage passages descend that same map. The component epsilon is a real definition.
Source: blueprint exchange statement and proof steps 1--8
(blueprint: sk-thm-sf-verdier-exchange). -/
structure Package where
  unit (s : Stage.{u} l) : C.{u} l Ω Z s
  stage (s : Stage.{u} l) : StageData l Ω s
    (Sf.ring.operation cf s) (Sg.ring.operation cg s) (Sfg.ring.operation cfg s) (unit s)
  ring (s : RingStage.{u} l) : RingRealization l Ω f s (stage (s.stage l))
  projection (s : RingStage.{u} l) :
    RingProjection l Ω cf s (ring s) (Sf.ring.left cf s)
  conclusion (s : Stage.{u} l) : StageConclusion l Ω (stage s)
  ringShifts (s : RingStage.{u} l) :
    RingShiftRealization l Ω (ring s) (conclusion (s.stage l))
  exchangeNaturality {s t : Stage.{u} l}
      {TX : C.{u} l Ω X s ⥤ C.{u} l Ω X t} {TY : C.{u} l Ω Y s ⥤ C.{u} l Ω Y t}
      {TZ : C.{u} l Ω Z s ⥤ C.{u} l Ω Z t}
      (b : StageScalar l Ω (stage s) (stage t) TX TY TZ)
      (_hc : TX.map (stage s).dualizing.hom ≫ (b.kappaX l Ω).hom =
        (b.exceptional.b l Ω).hom.app ((Sg.ring.operation cg s).G.obj (unit s)) ≫
          (Sf.ring.operation cf t).G.map (b.kappaY l Ω).hom ≫ (stage t).dualizing.hom)
      (M : C.{u} l Ω X s) :
    TY.map ((stage s).epsilon l Ω M) ≫
        b.star l Ω (((stage s).dualX l Ω).obj (op M)) ≫
        (stage t).star.map (b.dualX l Ω M) =
      b.dualY l Ω ((Sf.ring.operation cf s).F.obj M) ≫
        ((stage t).dualY l Ω).map ((b.exceptional.q l Ω).inv.app M).op ≫
        (stage t).epsilon l Ω (TX.obj M)
  integralAlpha (E : FieldStage.{u} l) :
    (Sf.ring.operation cf (.integral E)).F ⋙ (Sg.ring.operation cg (.integral E)).F ≅
      (Sfg.ring.operation cfg (.integral E)).F
  integralAlpha_normalized (E : FieldStage.{u} l) :
    Functor.isoWhiskerRight (integralAlpha E)
        (PurCompactSupport.finiteTorIntegralInclusion l E.carrier Z) =
      integralAlphaRealization l Ω D hl f g Sf Sg Sfg cf cg cfg E
  integralDualizing (E : FieldStage.{u} l) :
    (stage (.integral E)).dualizing =
      (composition (Sf.ring.operation cf (.integral E)).adjunction
        (Sg.ring.operation cg (.integral E)).adjunction
        (Sfg.ring.operation cfg (.integral E)).adjunction (integralAlpha E)).app
          (unit (.integral E))
  ringScalar {s t : RingStage.{u} l}
      (a : PurCompactSupport.Change (s.coefficients l) (t.coefficients l)) (ha : Allowed l a) :
    ∃ (SX : Scalar.{u} l Ω a X) (SY : Scalar.{u} l Ω a Y) (SZ : Scalar.{u} l Ω a Z),
      ∃ b : StageScalar l Ω (stage (s.stage l)) (stage (t.stage l))
          SX.functor SY.functor SZ.functor,
        ScalarConclusion l Ω b ∧
        Nonempty (ScalarShifts l Ω (conclusion (s.stage l))
          (conclusion (t.stage l)) b) ∧
        (∀ K : C.{u} l Ω X (s.stage l),
          (t.inclusion.{u} l Ω Y).map ((b.exceptional.q l Ω).hom.app K) ≫
              (Sf.ring.left cf t).hom.app (SX.functor.obj K) ≫
              (PurCompactSupport.image (t.coefficients l) cf).map
                (SX.realization.hom.app K) =
            SY.realization.hom.app ((Sf.ring.operation cf (s.stage l)).F.obj K) ≫
              (pbcDerivedExtend (a.map Y)).map ((Sf.ring.left cf s).hom.app K) ≫
              (PurCompactSupport.comparison a cf).app ((s.inclusion.{u} l Ω X).obj K)) ∧
        (∀ K : C.{u} l Ω Y (s.stage l),
          (t.inclusion.{u} l Ω Z).map ((b.structureY.q l Ω).hom.app K) ≫
              (Sg.ring.left cg t).hom.app (SY.functor.obj K) ≫
              (PurCompactSupport.image (t.coefficients l) cg).map
                (SY.realization.hom.app K) =
            SZ.realization.hom.app ((Sg.ring.operation cg (s.stage l)).F.obj K) ≫
              (pbcDerivedExtend (a.map Z)).map ((Sg.ring.left cg s).hom.app K) ≫
              (PurCompactSupport.comparison a cg).app ((s.inclusion.{u} l Ω Y).obj K)) ∧
        (∀ K : C.{u} l Ω X (s.stage l),
          (t.inclusion.{u} l Ω Z).map ((b.structureX.q l Ω).hom.app K) ≫
              (Sfg.ring.left cfg t).hom.app (SX.functor.obj K) ≫
              (PurCompactSupport.image (t.coefficients l) cfg).map
                (SX.realization.hom.app K) =
            SZ.realization.hom.app ((Sfg.ring.operation cfg (s.stage l)).F.obj K) ≫
              (pbcDerivedExtend (a.map Z)).map ((Sfg.ring.left cfg s).hom.app K) ≫
              (PurCompactSupport.comparison a cfg).app ((s.inclusion.{u} l Ω X).obj K)) ∧
        (t.inclusion.{u} l Ω Z).map b.unit.hom ≫ (ring t).unitIso.hom =
          SZ.realization.hom.app (unit (s.stage l)) ≫
            (pbcDerivedExtend (a.map Z)).map (ring s).unitIso.hom ≫ ringUnitScalar l a Z
  rationalization (E : FieldStage.{u} l) :
    ∃ b : StageScalar l Ω (stage (.integral E)) (stage (.rational E))
        (ConstructibleExceptionalCoefficients.rationalization.{u} l Ω E X)
        (ConstructibleExceptionalCoefficients.rationalization.{u} l Ω E Y)
        (ConstructibleExceptionalCoefficients.rationalization.{u} l Ω E Z),
      ScalarConclusion l Ω b ∧
      Nonempty (ScalarShifts l Ω (conclusion (.integral E))
        (conclusion (.rational E)) b) ∧
      b.exceptional = Sf.fields.rationalizationComparison cf E ∧
      b.structureY = Sg.fields.rationalizationComparison cg E ∧
      b.structureX = Sfg.fields.rationalizationComparison cfg E
  rationalScalar (E L : FieldStage.{u} l) (i : E.carrier →ₐ[Padic l] L.carrier) :
    ∃ b : StageScalar l Ω (stage (.rational E)) (stage (.rational L))
        (ConstructibleExceptionalCoefficients.rationalScalar.{u} l Ω E L i X)
        (ConstructibleExceptionalCoefficients.rationalScalar.{u} l Ω E L i Y)
        (ConstructibleExceptionalCoefficients.rationalScalar.{u} l Ω E L i Z),
      ScalarConclusion l Ω b ∧
      Nonempty (ScalarShifts l Ω (conclusion (.rational E))
        (conclusion (.rational L)) b) ∧
      b.exceptional = Sf.fields.rationalComparison cf E L i ∧
      b.structureY = Sg.fields.rationalComparison cg E L i ∧
      b.structureX = Sfg.fields.rationalComparison cfg E L i
  common (i : AlgebraicallyClosedCoefficients.Index l Ω) :
    ∃ b : StageScalar l Ω (stage (.rational (commonField.{u} l Ω i))) (stage .closed)
        (commonInclusion.{u} l Ω X i) (commonInclusion.{u} l Ω Y i) (commonInclusion.{u} l Ω Z i),
      ScalarConclusion l Ω b ∧
      Nonempty (ScalarShifts l Ω (conclusion (.rational (commonField.{u} l Ω i)))
        (conclusion .closed) b) ∧
      b.exceptional = Sf.common.commonComparison cf i ∧
      b.structureY = Sg.common.commonComparison cg i ∧
      b.structureX = Sfg.common.commonComparison cfg i

end Geometry

/-- Specialize the operation package to the coefficient point with its identity
structure map. This fixes the base-over-base instance explicitly; the Spec algebra
instance can otherwise choose Spec(map id), which is not definitionally the identity.
All choices below are of existing normalized operations and compactifications.
Source: blueprint exchange setting s=Spec k (blueprint: sk-thm-sf-verdier-exchange). -/
def Assertion (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    {X Y : Scheme.{u}} [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))] [IsSeparated (Y ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of D.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] : Prop :=
  letI : (Spec (.of D.k)).Over (Spec (.of D.k)) := ⟨𝟙 _⟩
  ∀ (Sf : System.{u} l Ω D hl (f := f))
    (SY : System.{u} l Ω D hl (f := Y ↘ Spec (.of D.k)))
    (SX : System.{u} l Ω D hl (f := f ≫ (Y ↘ Spec (.of D.k))))
    (cf : Compactification f) (cY : Compactification (Y ↘ Spec (.of D.k)))
    (cX : Compactification (f ≫ (Y ↘ Spec (.of D.k)))),
    Nonempty (Package l Ω D hl f (Y ↘ Spec (.of D.k)) Sf SY SX cf cY cX)

/-- Verdier exchange for separated finite-type schemes over the fixed algebraic
closure of a finite field, at every positive finite level, at completed integral
coefficients, at finite coefficient fields, and over the algebraic closure of Q_l.
The three Systems are choices of the already constructed normalized operations, not
ambient exceptional-adjoint hypotheses. The conclusion supplies the canonical maps,
their ambient realizations, naturality, the [-r] shift law, and coefficient squares.

Source: main-20261015, sec-six-functors/sk-thm-sf-verdier-exchange, order 2503
(blueprint: sk-thm-sf-verdier-exchange).

Proof plan, in the order of the node:
1. The coefficient unit at the point is constructible of Tor amplitude [0,0]. Apply
   the constructible exceptional functors to obtain omega_X and omega_Y. The ring
   realizations use the original small pro-etale sites and completed integral sheaf.
2. Use lem-sf-constructible-exceptional-adjunction-coefficients for f, a_Y and a_X.
   Restrict canonical compact-support composition, thm-sf-comp-composition, to these
   full domains. At integral coefficients use the completed proper/open compositor
   in fix-lem-exchanges, realized by integralAlphaRealization. Conjugate its inverse
   under the composite adjunction and evaluate at the coefficient unit to obtain c.
3. Apply sk-thm-sf-tensor-hom with N=omega_Y and invert its isomorphism. Follow it
   by Rf_* RHom(M,c). Transposing the evaluations shows that this is exactly epsilon,
   which is defined above from the actual projection and the two adjunctions.
4. Naturality in the contravariant variable follows from naturality of evaluation,
   projection, both adjunction bijections and c. Their shift comparisons yield the
   commutative square with [-r]. DualShiftModel fixes the ordinary Hom shift
   to the product-component sign (-1)^(m*q) before localization.
   RingShiftRealization restricts it to the constructible categories; ScalarShifts
   carries that normalization through rationalization and common stages.
5. For each allowed finite quotient, integral reduction, or ramified finite-free
   scalar map, use the counit-normalized q and b of the constructible System.
   lem-sp-et-proet-coefficient-compatibility gives the composition/q square.
6. Transpose its two sides under the composite adjunction. The counit equations
   identify both with the same composite of q, inverse alpha and the old counits.
   Faithfulness of the Hom equivalence proves the scalar square for c; this is the
   mate-pasting calculation of lem-weil-pbc-mate-pasting and adjunction-conjugate.
7. Use lem-coef-cartesian-section-adjoint-mates and the finite adjoint comparisons
   on coherent cartesian systems. lem-coef-semilinear-derived-sections and
   lem-sf-integral-compactification-system-realization identify the actual completed
   proper/open composites before total limit. Their maps, not an arbitrary family
   of evaluated finite arrows, give the integral equation. Rationalization and
   common finite-stage descent preserve these equations and all inverses.
8. Evaluate at the coefficient unit. Naturality gives the kappa/c equation displayed
   in ScalarConclusion. Internal-Hom comparison is extended evaluation transposed;
   direct-image comparison is the pullback/counit mate. Paste their squares to obtain
   the displayed epsilon equation, on exactly these constructible domains. The
   exchangeNaturality field records it for every projection-compatible comparison,
   so it applies to the specified canonical maps independently of their presentations. Field
   reduction always means reduction of an integral representative before localization.
-/
theorem verdier_exchange
    (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    {X Y : Scheme.{u}} [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))] [IsSeparated (Y ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of D.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    : Assertion l Ω D hl f := by
  sorry

end VerdierExchange
end WeilConjectures
