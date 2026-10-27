module

public import WeilConjectures.AlgebraicGeometry.DerivedCategory

public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree

public import WeilConjectures.AlgebraicGeometry.Modules.Invertible

public import WeilConjectures.AlgebraicGeometry.EffectiveCartier

public import Sheaf.AlgebraicGeometry.AlgebraicSpace

public import Mathlib.AlgebraicGeometry.Noetherian

public import Mathlib.AlgebraicGeometry.Scheme

public import Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids
public import WeilConjectures.AlgebraicGeometry.Picard.DegreeMorphism
public import WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceSchemeRestriction
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties
public import Sheaf.AlgebraicGeometry.Modules.ExteriorSheaf
public import WeilConjectures.AlgebraicGeometry.Hilbert.Curve
public import WeilConjectures.AlgebraicGeometry.Modules.ZeroLocus
public import WeilConjectures.AlgebraicGeometry.TensorPullbackStructureSheaf
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import Mathlib.Algebra.Homology.Double
public import Sheaf.TraceFormula.TwoTermPerfectDeterminantData
import Sheaf.TraceFormula.ProjectiveBundleProper
import Sheaf.AlgebraicGeometry.ProperFlatGlobalSections
import Sheaf.TraceFormula.SmoothCurveSectionCartier
import WeilConjectures.AlgebraicGeometry.Cohomology.EulerChar
public import WeilConjectures.AlgebraicGeometry.Picard.Defs
import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.BaseChange
import Sheaf.AlgebraicGeometry.AlgebraicSpaceOpenSubspace
import Sheaf.AlgebraicGeometry.CurveDegreeTensorAdditive
import WeilConjectures.AlgebraicGeometry.Curve.RiemannRoch
import Sheaf.RingTheory.PseudoCoherentMaximalFibrePerfect
import Sheaf.TraceFormula.TwoTermPerfectTorWindow
import Sheaf.Paper.RingedSitePerfectProjectionFormula
import Sheaf.AlgebraicGeometry.AlgebraicSpaceInvertibleDescent
import WeilConjectures.AlgebraicGeometry.Regular
import WeilConjectures.AlgebraicGeometry.Picard.Jacobian
import Sheaf.AlgebraicGeometry.SymmetricAbelImageGeometry
import Sheaf.AlgebraicGeometry.NonzeroSectionIntegralCartier
import WeilConjectures.AlgebraicGeometry.Modules.LocalInvertibleMinorBlock
import Sheaf.RingTheory.RegularLocalUFDBoundaryFactorization
import Sheaf.AlgebraicGeometry.RegularPrimeDivisorLocalEquations
import WeilConjectures.AlgebraicGeometry.FibreCartierLocal
import Sheaf.AlgebraicGeometry.DerivedEtaleZariskiEquivalence

/-! # The relative degree-(g-1) Picard torsor and its theta divisor

Source: Milne, Abelian Varieties, III §§6 and 8, Theorem 8.1, pp.110--111;
Stacks, perfect.tex, Tags 0FJX and 0FJY; divisors.tex, Tag 062Y
(blueprint: lem-sfb-relative-degree-gminusone-theta).

The structures below only package the hypotheses and all clauses of this node.
The theta pair is retained on every test scheme, as well as on the small etale
site. This makes arbitrary base change a comparison of ordinary module pairs.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry

/-- The family hypotheses, including the case of an empty base and no marked points.
Source: Milne III §8; the stable-family convention
(blueprint: lem-sfb-relative-degree-gminusone-theta). -/
structure RelativeThetaCurve where
  ambient : Scheme.{u}
  genus : ℕ
  family : StablePointedModuli ambient genus 0
  noetherian : IsLocallyNoetherian family.base.left
  smooth : Smooth family.projection

/-- The actual base of the family; the ambient scheme imposes no extra condition.
Source: Milne III §8 (blueprint: lem-sfb-relative-degree-gminusone-theta). -/
abbrev RelativeThetaCurve.base (C : RelativeThetaCurve.{u}) : Scheme.{u} :=
  C.family.base.left

/-- The given smooth stable curve morphism.
Source: Milne III §8 (blueprint: lem-sfb-relative-degree-gminusone-theta). -/
abbrev RelativeThetaCurve.map (C : RelativeThetaCurve.{u}) := C.family.projection

/-- Properness follows from the already recorded projective-bundle convention.
Source: Stacks 01W7 (blueprint: lem-sfb-relative-degree-gminusone-theta). -/
instance RelativeThetaCurve.proper (C : RelativeThetaCurve.{u}) : IsProper C.map :=
  projectiveBundle_proper _ C.family.stable.1

/-- Finite presentation is part of the given stable-family data.
Source: stable-family convention (blueprint: lem-sfb-relative-degree-gminusone-theta). -/
instance RelativeThetaCurve.finitePresentation (C : RelativeThetaCurve.{u}) :
    LocallyOfFinitePresentation C.map := C.family.stable.2.2.choose

/-- The relative degree component uses the existing Euler-characteristic degree.
Source: Milne III §8; Stacks 0B9L
(blueprint: lem-sfb-relative-degree-gminusone-theta). -/
abbrev RelativeThetaCurve.degree (C : RelativeThetaCurve.{u}) (d : ℤ) :=
  (picardDegreeSubfunctor C.map d).toFunctor

/-- A small algebraic-space representation of a specified degree subfunctor.
The lift changes only the size of the section sets, not the functor represented.
Source: Milne III §8; Stacks 025Y
(blueprint: lem-sfb-relative-degree-gminusone-theta). -/
structure RelativeThetaRepresentation (C : RelativeThetaCurve.{u}) (d : ℤ) where
  space : AlgebraicSpace C.base
  identification : space.obj.obj ⋙ uliftFunctor.{u + 1, u} ≅ C.degree d

/-- The given representability hypothesis on the degree-zero Picard sheaf.
Source: Milne III §8 (blueprint: lem-sfb-relative-degree-gminusone-theta). -/
structure RelativeThetaInput where
  curve : RelativeThetaCurve.{u}
  jacobian : RelativeThetaRepresentation curve 0

/-- The Picard class of a point of a degree-component model.
Source: Milne III §8 (blueprint: lem-sfb-relative-degree-gminusone-theta). -/
def RelativeThetaRepresentation.class {C : RelativeThetaCurve.{u}} {d : ℤ}
    (P : RelativeThetaRepresentation C d) (T : Over C.base)
    (a : P.space.obj.obj.obj (op T)) : (picardFunctor C.map).obj.obj (op T) :=
  ((P.identification.hom.app (op T)) (ULift.up a)).val

/-- A test scheme of a degree-component model, retaining its classifying map.
Source: Milne III §8 (blueprint: lem-sfb-relative-degree-gminusone-theta). -/
abbrev RelativeThetaRepresentation.Test {C : RelativeThetaCurve.{u}} {d : ℤ}
    (P : RelativeThetaRepresentation C d) :=
  CostructuredArrow yoneda P.space.obj.obj

/-- The class classified by a test scheme, read by Yoneda from its classifying map.
Source: Milne III §8 (blueprint: lem-sfb-relative-degree-gminusone-theta). -/
def RelativeThetaRepresentation.testClass {C : RelativeThetaCurve.{u}} {d : ℤ}
    (P : RelativeThetaRepresentation C d) (T : P.Test) :=
  P.class T.left (T.hom.app (op T.left) (𝟙 T.left))

/-- Equal-rank two-term models in the stated degrees 0 and 1. Neither term nor the
complex is chosen from an unproved existence statement.
Source: Stacks 0FJX, reindexed (blueprint: lem-sfb-relative-degree-gminusone-theta). -/
structure RelativeThetaModel (V : Scheme.{u}) extends TwoTermDeterminantModel V where
  equal_rank : negRank = nonnegRank

/-- The actual two-term complex, including rank zero.
Source: Stacks 0FJX (blueprint: lem-sfb-relative-degree-gminusone-theta). -/
def RelativeThetaModel.complex {V : Scheme.{u}} (E : RelativeThetaModel V) :
    CochainComplex (SheafOfModules.{u} (moduleRings V.toRingedSpace)) ℤ :=
  HomologicalComplex.double E.differential
    (c := ComplexShape.up ℤ) (i₀ := 0) (i₁ := 1) (by decide)

/-- The displayed line det(E1) tensor det(E0)-dual, in the order of the node.
Source: Stacks 0FJX (blueprint: lem-sfb-relative-degree-gminusone-theta). -/
def RelativeThetaModel.line {V : Scheme.{u}} (E : RelativeThetaModel V) : V.Modules :=
  E.nonneg.exteriorSheaf E.negRank ⊗ (E.neg.exteriorSheaf E.negRank)ᵛ

/-- The determinant-section condition without a choice of bases: contraction of
s tensor a top wedge is the top wedge of the images. This also fixes the sign.
Source: Stacks 0FJI and 0FJX (blueprint: lem-sfb-relative-degree-gminusone-theta). -/
def RelativeThetaModel.IsDeterminantPair {V : Scheme.{u}} (E : RelativeThetaModel V)
    (L : V.Modules) (s : 𝟙_ V.Modules ⟶ L) : Prop :=
  ∃ e : L ≅ E.line,
    ∃ d : E.neg.exteriorSheaf E.negRank ⟶ E.nonneg.exteriorSheaf E.negRank,
      (∀ (U : V.Opens) (a : Fin E.negRank → E.neg.val.obj (op U)),
        d.val.app (op U) (Scheme.Modules.exteriorSheafSection E.neg E.negRank U a) =
          Scheme.Modules.exteriorSheafSection E.nonneg E.negRank U
            (fun i ↦ E.differential.val.app (op U) (a i))) ∧
      (ρ_ (E.neg.exteriorSheaf E.negRank)).inv ≫
        (E.neg.exteriorSheaf E.negRank) ◁ (s ≫ e.hom) ≫
        (α_ _ _ _).inv ≫
        (β_ (E.neg.exteriorSheaf E.negRank) (E.nonneg.exteriorSheaf E.negRank)).hom ▷ _ ≫
        (α_ _ _ _).hom ≫
        (E.nonneg.exteriorSheaf E.negRank) ◁
          (Scheme.Modules.dualEvaluation (E.neg.exteriorSheaf E.negRank)) ≫
        (ρ_ (E.nonneg.exteriorSheaf E.negRank)).hom = d

variable [∀ V : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings V.toRingedSpace))]

/-- A model computes the actual canonical injective-resolution direct image.
Source: Stacks 0CTM and 0FJX (blueprint: lem-sfb-relative-degree-gminusone-theta). -/
def RelativeThetaModel.Computes {C : RelativeThetaCurve.{u}} {d : ℤ}
    {P : RelativeThetaRepresentation C d} (T : P.Test)
    (U : (pullback C.map T.left.hom).Modules) (E : RelativeThetaModel T.left.left) : Prop :=
  Nonempty ((schemeDerivedDirectImage (pullback.snd C.map T.left.hom)).obj
    ((DerivedCategory.singleFunctor _ 0).obj U) ≅ DerivedCategory.Q.obj E.complex)

/-- The line pair and its ordinary tensor pullbacks on all scheme tests. Its restriction
to etale tests is the specified line pair on the algebraic space's small site.
Source: Stacks 03G7 and 0FJY (blueprint: lem-sfb-relative-degree-gminusone-theta). -/
structure RelativeThetaPair {C : RelativeThetaCurve.{u}}
    (P : RelativeThetaRepresentation C (C.genus - 1 : ℤ)) where
  line : P.space.Modules
  invertible : P.space.IsLineModule line
  thetaSection : SheafOfModules.unit P.space.structureSheaf ⟶ line
  testLine : ∀ T : P.Test, T.left.left.Modules
  testInvertible : ∀ T : P.Test, (testLine T).IsInvertible
  testSection : ∀ T : P.Test, 𝟙_ T.left.left.Modules ⟶ testLine T
  restriction : ∀ {T U : P.Test} (a : T ⟶ U),
    (Scheme.Modules.tensorPullback a.left.left).obj (testLine U) ≅ testLine T
  restriction_section : ∀ {T U : P.Test} (a : T ⟶ U),
    (Scheme.Modules.tensorPullback a.left.left).map (testSection U) ≫
      (restriction a).hom =
        Scheme.Modules.tensorPullbackObjUnitToUnit a.left.left ≫ testSection T
  restriction_id : ∀ T : P.Test,
    restriction (𝟙 T) = (Scheme.Modules.tensorPullbackSectionId T.left.left).app (testLine T)
  restriction_comp : ∀ {T U V : P.Test} (a : T ⟶ U) (b : U ⟶ V),
    restriction (a ≫ b) =
      (Scheme.Modules.tensorPullbackSectionComp a.left.left b.left.left).app (testLine V) ≪≫
        (Scheme.Modules.tensorPullback a.left.left).mapIso (restriction b) ≪≫ restriction a
  chartIso : ∀ T : P.space.EtaleSite,
    testLine T.obj ≅ (P.space.schemeRestriction T).obj line
  chartUnit : ∀ T : P.space.EtaleSite,
    𝟙_ T.obj.left.left.Modules ≅
      (P.space.schemeRestriction T).obj (SheafOfModules.unit P.space.structureSheaf)
  chartUnit_one : ∀ (T : P.space.EtaleSite) (U : T.obj.left.left.Opens),
    (chartUnit T).hom.val.app (op U) (1 : Γ(T.obj.left.left, U)) =
      (P.space.schemeOpensRingHom T).app (op U) (1 : Γ(T.obj.left.left, U))
  chart_section : ∀ T : P.space.EtaleSite,
    testSection T.obj ≫ (chartIso T).hom =
      (chartUnit T).hom ≫ (P.space.schemeRestriction T).map thetaSection
  cartier_flat : ∀ T : P.space.EtaleSite,
    (testSection T.obj).zeroLocus.IsRelativeEffectiveCartier T.obj.left.hom
  divisorLine : ∀ T : P.space.EtaleSite,
    Nonempty (testLine T.obj ≅ (testSection T.obj).zeroLocus.toModulesᵛ)
  local_models : ∀ (T : P.space.EtaleSite)
    (U : (pullback C.map T.obj.left.hom).Pic),
    (toPicardFunctor C.map).app (op T.obj.left) U = P.testClass T.obj →
    ∀ x : T.obj.left.left, ∃ (V : P.Test) (a : V ⟶ T.obj),
      IsOpenImmersion a.left.left ∧ (∃ y : V.left.left, a.left.left y = x) ∧
      ∃ E : RelativeThetaModel V.left.left,
        E.Computes V ((Scheme.Modules.tensorPullback (baseChangeMap C.map a.left)).obj
          ((fromSkeleton _).obj U.val))
  determinant : ∀ (T : P.Test) (U : (pullback C.map T.left.hom).Pic)
    (E : RelativeThetaModel T.left.left),
    (toPicardFunctor C.map).app (op T.left) U = P.testClass T →
    E.Computes T ((fromSkeleton _).obj U.val) →
    E.IsDeterminantPair (testLine T) (testSection T)

/-- The fibre test corresponding to the universal point of a scheme representing
an algebraic-space fibre. Its scheme is Q, viewed over the original base.
Source: Milne III §8 (blueprint: lem-sfb-relative-degree-gminusone-theta). -/
def RelativeThetaRepresentation.fibreTest {C : RelativeThetaCurve.{u}} {d : ℤ}
    (P : RelativeThetaRepresentation C d) {K : Type u} [Field K]
    (k : Spec (.of K) ⟶ C.base) (Q : Over (Spec (.of K)))
    (e : ((Over.map k).op ⋙ P.space.obj.obj).RepresentableBy Q) : P.Test :=
  CostructuredArrow.mk (yonedaEquiv.symm (e.homEquiv (𝟙 Q)))

/-- The geometric fibre is the scheme-theoretic Abel image, including its ideal,
not only its support. The Abel map is specified on every Hilbert-scheme test point.
Source: Milne III §§5--6 and 8 (blueprint: lem-sfb-relative-degree-gminusone-theta). -/
def RelativeThetaPair.GeometricAbelImage {C : RelativeThetaCurve.{u}}
    {P : RelativeThetaRepresentation C (C.genus - 1 : ℤ)} (B : RelativeThetaPair P) : Prop :=
  ∀ (K : Type u) [Field K] [IsAlgClosed K] (k : Spec (.of K) ⟶ C.base),
    ∃ (Q H : Over (Spec (.of K)))
      (eQ : ((Over.map k).op ⋙ P.space.obj.obj).RepresentableBy Q)
      (eH : (hilbertPresheaf (pullback.snd C.map k) (C.genus - 1)).RepresentableBy H)
      (abel : H ⟶ Q),
      (∀ (T : Over (Spec (.of K))) (a : T ⟶ H),
        ∃ L : (pullback (pullback.snd C.map k) T.hom).Pic,
          Nonempty ((fromSkeleton _).obj L.val ≅ (eH.homEquiv a).val.toModulesᵛ) ∧
          (picardFunctorIsoOfIsPullback (IsPullback.of_hasPullback C.map k)).hom.app
              (op T) (P.class ((Over.map k).obj T) (eQ.homEquiv (a ≫ abel))) =
            (toPicardFunctor (pullback.snd C.map k)).app (op T) L) ∧
      (B.testSection (P.fibreTest k Q eQ)).zeroLocus = abel.left.ker

/-- The canonical equality of underlying group and set sheaf sections as an equivalence.
Source: relative Picard tensor law, Stacks 0B9L
(blueprint: lem-sfb-relative-degree-gminusone-theta). -/
def relativeThetaClassEquiv {X S : Scheme.{u}} (f : X ⟶ S) (T : Over S) :
    ((picardFunctorGrp f).obj (op T)) ≃ (picardFunctor f).obj.obj (op T) :=
  Equiv.cast (congrArg (fun F : (Over S)ᵒᵖ ⥤ Type (u + 1) ↦ F.obj (op T))
    (picardFunctorGrp_comp_forget f))

/-- Tensor product of Picard sheaf sections, using the recorded group-valued sheaf.
Source: Stacks 0B9L (blueprint: lem-sfb-relative-degree-gminusone-theta). -/
def relativeThetaTensorClass {X S : Scheme.{u}} (f : X ⟶ S) (T : Over S)
    (x y : (picardFunctor f).obj.obj (op T)) : (picardFunctor f).obj.obj (op T) :=
  relativeThetaClassEquiv f T
    ((relativeThetaClassEquiv f T).symm x * (relativeThetaClassEquiv f T).symm y)

/-- Tensor action and its simply transitive property on sections, together with
etale local curve sections and their actual divisor-line trivializations.
Source: Milne III §8, Stacks 0B9U (blueprint: lem-sfb-relative-degree-gminusone-theta). -/
structure RelativeThetaTorsor (I : RelativeThetaInput.{u})
    (P : RelativeThetaRepresentation I.curve (I.curve.genus - 1 : ℤ)) where
  action : ∀ T : Over I.curve.base,
    I.jacobian.space.obj.obj.obj (op T) → P.space.obj.obj.obj (op T) →
      P.space.obj.obj.obj (op T)
  tensor : ∀ (T : Over I.curve.base)
    (M : I.jacobian.space.obj.obj.obj (op T)) (L : P.space.obj.obj.obj (op T)),
    P.class T (action T M L) =
      relativeThetaTensorClass I.curve.map T
        (I.jacobian.class T M) (P.class T L)
  naturality : ∀ {T U : Over I.curve.base} (a : T ⟶ U)
    (M : I.jacobian.space.obj.obj.obj (op U)) (L : P.space.obj.obj.obj (op U)),
    P.space.obj.obj.map a.op (action U M L) =
      action T (I.jacobian.space.obj.obj.map a.op M) (P.space.obj.obj.map a.op L)
  simply_transitive : ∀ T : Over I.curve.base,
    Function.Bijective (fun x : I.jacobian.space.obj.obj.obj (op T) ×
        P.space.obj.obj.obj (op T) ↦ (action T x.1 x.2, x.2))
  coverIndex : Type u
  cover : coverIndex → Over I.curve.base
  cover_etale : ∀ i, Etale (cover i).hom
  cover_noetherian : ∀ i, IsLocallyNoetherian (cover i).left
  cover_surjective : ∀ x : I.curve.base,
    ∃ (i : coverIndex) (y : (cover i).left), (cover i).hom y = x
  curveSection : ∀ i, (cover i).left ⟶ pullback I.curve.map (cover i).hom
  curveSection_projection : ∀ i,
    curveSection i ≫ pullback.snd I.curve.map (cover i).hom = 𝟙 _
  beta : ∀ (T : Over I.curve.base) (p : T.left ⟶ pullback I.curve.map T.hom),
    p ≫ pullback.snd I.curve.map T.hom = 𝟙 _ →
    (((Over.map T.hom).op ⋙ I.jacobian.space.obj.obj) ≅
      ((Over.map T.hom).op ⋙ P.space.obj.obj))
  beta_tensor : ∀ (T : Over I.curve.base) (p : T.left ⟶ pullback I.curve.map T.hom)
    (hp : p ≫ pullback.snd I.curve.map T.hom = 𝟙 _),
    ∃ A : (pullback I.curve.map T.hom).Pic,
      Nonempty ((fromSkeleton _).obj A.val ≅
        (p.ker.toModulesᵛ).tensorPow (I.curve.genus - 1)) ∧
      ∀ (V : Over T.left)
        (M : I.jacobian.space.obj.obj.obj (op ((Over.map T.hom).obj V))),
        P.class ((Over.map T.hom).obj V) ((beta T p hp).hom.app (op V) M) =
          relativeThetaTensorClass I.curve.map ((Over.map T.hom).obj V)
            (I.jacobian.class ((Over.map T.hom).obj V) M)
            ((toPicardFunctor I.curve.map).app (op ((Over.map T.hom).obj V))
              (Scheme.Pic.map
                ((pullbackIsoOfIsPullback
                  (IsPullback.of_hasPullback I.curve.map T.hom) V).inv ≫
                    pullback.fst (pullback.snd I.curve.map T.hom) V.hom) A))


/-- The scheme test classified by an actual point of the relative Picard space.
Source: Yoneda; Milne III §8 (blueprint: lem-sfb-relative-degree-gminusone-theta). -/
def RelativeThetaRepresentation.pointTest {C : RelativeThetaCurve.{u}} {d : ℤ}
    (P : RelativeThetaRepresentation C d) (T : Over C.base)
    (x : P.space.obj.obj.obj (op T)) : P.Test :=
  CostructuredArrow.mk (yonedaEquiv.symm x)

/-- All conclusions for one input. The Cartier divisor is the zero scheme of
pair.thetaSection, as explicitly tested by pair.cartier_flat on every etale chart.
Source: Milne III §§6,8; Stacks 0FJX, 062Y
(blueprint: lem-sfb-relative-degree-gminusone-theta). -/
structure RelativeThetaDatum (I : RelativeThetaInput.{u}) where
  picard : RelativeThetaRepresentation I.curve (I.curve.genus - 1 : ℤ)
  torsor : RelativeThetaTorsor I picard
  pair : RelativeThetaPair picard
  geometric : pair.GeometricAbelImage

/-- Cartesian morphisms of smooth genus-g families. In particular an isomorphism
u:C→D over one base supplies this square, so the point comparison is (u inverse)*.
Source: Milne III §8 (blueprint: lem-sfb-relative-degree-gminusone-theta). -/
structure RelativeThetaArrow (C D : RelativeThetaCurve.{u}) where
  base : C.base ⟶ D.base
  map : C.family.curve ⟶ D.family.curve
  square : IsPullback map C.map D.map base
  genus : C.genus = D.genus

/-- The comparisons on degree components and pairs for an arbitrary base change
or cartesian family isomorphism. Classes are pinned to the canonical Picard pullback.
Source: Milne III §8; Stacks 0FJY
(blueprint: lem-sfb-relative-degree-gminusone-theta). -/
structure RelativeThetaComparison {I J : RelativeThetaInput.{u}}
    (D : RelativeThetaDatum I) (E : RelativeThetaDatum J)
    (a : RelativeThetaArrow I.curve J.curve) where
  picard : (Over.map a.base).op ⋙ E.picard.space.obj.obj ≅ D.picard.space.obj.obj
  jacobian : (Over.map a.base).op ⋙ J.jacobian.space.obj.obj ≅ I.jacobian.space.obj.obj
  picard_class : ∀ (T : Over I.curve.base)
    (x : E.picard.space.obj.obj.obj (op ((Over.map a.base).obj T))),
    D.picard.class T (picard.hom.app (op T) x) =
      (picardFunctorIsoOfIsPullback a.square).hom.app (op T)
        (E.picard.class ((Over.map a.base).obj T) x)
  jacobian_class : ∀ (T : Over I.curve.base)
    (x : J.jacobian.space.obj.obj.obj (op ((Over.map a.base).obj T))),
    I.jacobian.class T (jacobian.hom.app (op T) x) =
      (picardFunctorIsoOfIsPullback a.square).hom.app (op T)
        (J.jacobian.class ((Over.map a.base).obj T) x)
  action : ∀ (T : Over I.curve.base)
    (M : J.jacobian.space.obj.obj.obj (op ((Over.map a.base).obj T)))
    (L : E.picard.space.obj.obj.obj (op ((Over.map a.base).obj T))),
    picard.hom.app (op T) (E.torsor.action ((Over.map a.base).obj T) M L) =
      D.torsor.action T (jacobian.hom.app (op T) M) (picard.hom.app (op T) L)
  lineIso : ∀ (T : Over I.curve.base)
    (x : E.picard.space.obj.obj.obj (op ((Over.map a.base).obj T))),
    E.pair.testLine (E.picard.pointTest ((Over.map a.base).obj T) x) ≅
      D.pair.testLine (D.picard.pointTest T (picard.hom.app (op T) x))
  section_eq : ∀ (T : Over I.curve.base)
    (x : E.picard.space.obj.obj.obj (op ((Over.map a.base).obj T))),
    E.pair.testSection (E.picard.pointTest ((Over.map a.base).obj T) x) ≫
      (lineIso T x).hom =
        D.pair.testSection (D.picard.pointTest T (picard.hom.app (op T) x))

/-- A simultaneous choice with coherent canonical comparisons. Heterogeneous equality
only suppresses the reindexing along the asserted equalities of Picard points and bases.
Source: Milne III §8; Stacks 0FJY
(blueprint: lem-sfb-relative-degree-gminusone-theta). -/
structure RelativeThetaSystemData where
  datum : ∀ I : RelativeThetaInput.{u}, RelativeThetaDatum I
  comparison : ∀ {I J : RelativeThetaInput.{u}} (a : RelativeThetaArrow I.curve J.curve),
    RelativeThetaComparison (datum I) (datum J) a

/-- The identity points coherence condition on the same canonical comparisons.
Source: Milne III §8; Stacks 0FJY
(blueprint: lem-sfb-relative-degree-gminusone-theta). -/
def RelativeThetaSystemData.identity_points (B : RelativeThetaSystemData.{u, w}) : Prop :=
  ∀ (I : RelativeThetaInput.{u})
    (a : RelativeThetaArrow I.curve I.curve),
    a.base = 𝟙 I.curve.base → a.map = 𝟙 I.curve.family.curve →
    ∀ T : Over I.curve.base,
      HEq ((B.comparison a).picard.hom.app (op T))
        (𝟙 ((B.datum I).picard.space.obj.obj.obj (op T)))

/-- The identity lines coherence condition on the same canonical comparisons.
Source: Milne III §8; Stacks 0FJY
(blueprint: lem-sfb-relative-degree-gminusone-theta). -/
def RelativeThetaSystemData.identity_lines (B : RelativeThetaSystemData.{u, w}) : Prop :=
  ∀ (I : RelativeThetaInput.{u})
    (a : RelativeThetaArrow I.curve I.curve),
    a.base = 𝟙 I.curve.base → a.map = 𝟙 I.curve.family.curve →
    ∀ (T : Over I.curve.base)
      (x : (B.datum I).picard.space.obj.obj.obj (op ((Over.map a.base).obj T))),
      HEq ((B.comparison a).lineIso T x)
        (Iso.refl ((B.datum I).pair.testLine
          ((B.datum I).picard.pointTest ((Over.map a.base).obj T) x)))

/-- The composition points coherence condition on the same canonical comparisons.
Source: Milne III §8; Stacks 0FJY
(blueprint: lem-sfb-relative-degree-gminusone-theta). -/
def RelativeThetaSystemData.composition_points (B : RelativeThetaSystemData.{u, w}) : Prop :=
  ∀ {I J K : RelativeThetaInput.{u}}
    (a : RelativeThetaArrow I.curve J.curve) (b : RelativeThetaArrow J.curve K.curve)
    (c : RelativeThetaArrow I.curve K.curve),
    c.base = a.base ≫ b.base → c.map = a.map ≫ b.map →
    ∀ (T : Over I.curve.base),
      HEq ((B.comparison c).picard.hom.app (op T))
        ((B.comparison b).picard.hom.app (op ((Over.map a.base).obj T)) ≫
          (B.comparison a).picard.hom.app (op T))

/-- The composition lines coherence condition on the same canonical comparisons.
Source: Milne III §8; Stacks 0FJY
(blueprint: lem-sfb-relative-degree-gminusone-theta). -/
def RelativeThetaSystemData.composition_lines (B : RelativeThetaSystemData.{u, w}) : Prop :=
  ∀ {I J K : RelativeThetaInput.{u}}
    (a : RelativeThetaArrow I.curve J.curve) (b : RelativeThetaArrow J.curve K.curve)
    (c : RelativeThetaArrow I.curve K.curve),
    c.base = a.base ≫ b.base → c.map = a.map ≫ b.map →
    ∀ (T : Over I.curve.base)
      (x : (B.datum K).picard.space.obj.obj.obj
        (op ((Over.map b.base).obj ((Over.map a.base).obj T)))),
      ∃ y : (B.datum K).picard.space.obj.obj.obj (op ((Over.map c.base).obj T)),
        HEq y x ∧ HEq ((B.comparison c).lineIso T y)
          ((B.comparison b).lineIso ((Over.map a.base).obj T) x ≪≫
            (B.comparison a).lineIso T
              ((B.comparison b).picard.hom.app (op ((Over.map a.base).obj T)) x))

/-- Naturality of the pair comparisons on every ordinary test-scheme triangle.
Source: Milne III §8; Stacks 0FJY
(blueprint: lem-sfb-relative-degree-gminusone-theta). -/
def RelativeThetaSystemData.Natural (B : RelativeThetaSystemData.{u, w}) : Prop :=
  ∀ {I J : RelativeThetaInput.{u}} (a : RelativeThetaArrow I.curve J.curve),
    ∀ (T U : Over I.curve.base)
    (x : (B.datum J).picard.space.obj.obj.obj (op ((Over.map a.base).obj T)))
    (y : (B.datum J).picard.space.obj.obj.obj (op ((Over.map a.base).obj U)))
    (b : (B.datum J).picard.pointTest ((Over.map a.base).obj T) x ⟶
      (B.datum J).picard.pointTest ((Over.map a.base).obj U) y)
    (c : (B.datum I).picard.pointTest T ((B.comparison a).picard.hom.app (op T) x) ⟶
      (B.datum I).picard.pointTest U ((B.comparison a).picard.hom.app (op U) y))
    (_h : b.left.left = c.left.left),
    HEq (((B.datum J).pair.restriction b).hom ≫ ((B.comparison a).lineIso T x).hom)
      ((Scheme.Modules.tensorPullback c.left.left).map ((B.comparison a).lineIso U y).hom ≫
        ((B.datum I).pair.restriction c).hom)

/-- The full coherent system, with proof fields referring to the same retained data.
Source: Milne III §8; Stacks 0FJY
(blueprint: lem-sfb-relative-degree-gminusone-theta). -/
structure RelativeThetaSystem extends RelativeThetaSystemData.{u, w} where
  identity_points : toRelativeThetaSystemData.identity_points
  identity_lines : toRelativeThetaSystemData.identity_lines
  composition_points : toRelativeThetaSystemData.composition_points
  composition_lines : toRelativeThetaSystemData.composition_lines
  natural : toRelativeThetaSystemData.Natural

/-- The degree-(g-1) Picard torsor, its canonical determinant theta pair, its geometric
Abel-image divisor, and all coherent base-change and family-isomorphism comparisons.
Source: Milne, Abelian Varieties, III Sections 5, 6 and 8, Theorem 8.1,
pp.101--102 and 110--111; Stacks 0FJX, 0FJY, 0CTM and 062Y
(blueprint: lem-sfb-relative-degree-gminusone-theta).

Proof:

1. The family is flat and finitely presented, with nonempty smooth geometrically connected fibres
of dimension one, by the stable-family hypothesis; it is proper because it is projective in the
projective-bundle sense. Apply universal structure-sheaf pushforward to get $\mathcal
O_T\simeq(f_T)_*\mathcal O_{C_T}$ for every $T$. Smoothness and nonempty fibres make $C\to S$ a
smooth surjection, so choose an etale cover $S_i\to S$ with sections $p_i$. The $S_i$ are locally
Noetherian by local finite type over $S$. Each $p_i$ is an effective Cartier divisor because the
curve is separated and smooth of relative dimension one. Its geometric fibre is one rational
point, so $\mathcal O((g-1)p_i)$ has degree $g-1$.
Uses: def-sfb-stable-pointed-moduli-groupoids, lem-trf-projective-bundle-proper, lem-sc-proper-
flat-global-sections, lem-sfb-smooth-space-cover-etale-sections, pqf-lem-locnoeth-lft, lem-trf-
smooth-curve-section-cartier, lem-pc-degree-base-change.

2. The full Picard fppf sheaf is a smooth algebraic space by the curve-Picard theorem, using Step
1's universal structure-sheaf condition. Its degree-$r$ subfunctor is open: on $S_i$, every class
on a parameter scheme $T$ has a normalized line representative, by rigidification; the locus where
$\chi(L_t)-\chi(\mathcal O_{C_t})=r$ is open and closed by Euler local constancy. These loci agree
on overlaps since Euler degree is invariant under field extension and base twists. Thus they glue
to the required open subscheme of every test scheme $T$; the definition of open subspace makes the
subfunctor an algebraic space. In particular $P$ is represented and is smooth over $S$. Here
$J=\operatorname{Pic}^0_{C/S}$ is the degree-zero Picard sheaf, in the convention of the
statement.
Uses: lem-sfb-picard-space-curves-smooth, sk-prop-picard-pic-split, lem-sfb-proper-flat-sheaf-
euler-local-constancy, lem-pc-degree-base-change, def-a1-space-open-subspace.

3. Tensor degree is additive on each geometric curve, so tensoring defines $J\times_SP\to P$. For
any test scheme the map $(M,L)\mapsto(M\otimes L,L)$ has inverse $(L_1,L_2)\mapsto(L_1\otimes
L_2^{-1},L_2)$; both formulas are formulas for Picard sheaf sections, and their composites cancel
the dual factors. Thus it is an isomorphism of sheaves and hence of representing spaces. On $S_i$,
tensoring by $A_i=\mathcal O((g-1)p_i)$ has inverse tensoring by $A_i^{-1}$ and gives
$\beta_{p_i}:J_{S_i}\simeq P_{S_i}$. The class of $A_i$ is a local section of $P$, proving the
torsor assertion.
Uses: lem-trf-curve-degree-tensor-additive, sk-def-picard-pic.

4. Choose etale scheme charts of $P$ lying over the $S_i$. On each such chart $V$ rigidification
along $p_i$ supplies an actual line module $U$ on $C_V$ representing its classifying map. Since
$f_V$ is proper, hence quasi-compact and quasi-separated, the etale--Zariski equivalence on
$D_{\mathrm{QCoh}}$ intertwines the Zariski complex $K=Rf_{V,*}U$ with
$R\epsilon_{V,*}Rf_{V,\mathrm{et},*}U$. By perfect coherent base change, $K$ is therefore perfect
and its derived pullback is the cohomology complex for every base change. On a geometric fibre it
has cohomology only in degrees $0,1$, by the coherent curve vanishing, and its Euler
characteristic is $(g-1)+(1-g)=0$, by Riemann--Roch and the definition of degree. On an affine
chart, the residue-field criterion puts this perfect object in Tor degrees $[0,1]$. Apply the two-
term Tor-window equivalence to $K[1]$ in degrees $[-1,0]$ and reindex back to obtain
$E^0\xrightarrow d E^1$ (rescaling one term removes the shift sign). The equality of Euler
characteristics forces the ranks of $E^0,E^1$ to agree on each component. Only the fibrewise
degree $g-1$ of $U$ was used, so the same holds for any representing module on any scheme chart of
$P$.
Uses: sk-prop-picard-pic-split, lem-sfb-derived-etale-zariski-equivalence, lem-sfb-proper-flat-
space-derived-base-change, lem-sfb-proper-space-curve-qcoh-bound, lem-sc-riemann-roch, lem-weil-
pbc-pseudocoherent-maximal-fibre-perfect, lem-trf-two-term-perfect-tor-window.

5. Apply the canonical-section lemma to $K$ to obtain $(D(K),\delta_K)$ on $V$ with the displayed
exterior-power formula. This immediately removes dependence on a chosen two-term complex,
including after adding an acyclic identity complex. If $U'=U\otimes f_V^*N$, the perfect
projection formula identifies $Rf_{V,*}U'$ with $K\otimes N$; rank-zero twist cancellation
identifies its pair with the old pair. Any two representatives of the same class differ in this
way: normalize both along $p_i$ and use rigidification's uniqueness. The choice of an isomorphism
between representatives is immaterial, since its ambiguity is a scalar from $V$ by Step 1, and
scalars act trivially on the determinant pair. This argument applies also on overlaps where the
two chosen curve sections differ: normalize both representatives using either one section on that
overlap.
Uses: lem-sfb-rank-zero-perfect-determinant-section, lem-sbc-ringed-site-perfect-projection-
formula, sk-prop-picard-pic-split.

6. On each double overlap $V_i\times_PV_j$ the pulled-back complexes are the direct images of the
pulled-back representatives, by perfect coherent base change along the flat chart maps; use Step
5's comparison there. On a triple overlap, composing the representative isomorphisms tensors their
base lines; cancellation for the product twist and functoriality for derived isomorphisms give the
same comparison as going directly. Any residual scalar acts trivially. Thus the lines have a
genuine etale descent datum and the sections agree under it. Line-module descent gives a line
module $\mathcal T$ on $P$; its fully faithful assertion, applied to maps $\mathcal O\to\mathcal
T$, glues the sections to $s_\Theta$. Set $\Theta=Z(s_\Theta)$. This is a real zero-scheme
construction and on each chart it is locally the principal ideal $(\det d)$.
Uses: lem-trf-algebraic-space-invertible-descent, lem-sfb-rank-zero-perfect-determinant-section,
lem-sfb-proper-flat-space-derived-base-change.

7. Fix an algebraically closed geometric field $k$ over $S$, and choose $p\in C(k)$. The geometric
curve is smooth connected, hence integral: its regular local rings are domains, so distinct
irreducible components cannot meet, and connectedness leaves one component. Its degree-zero Picard
space is the Jacobian by representability and uniqueness of representing objects. Translate $P_k$
to that Jacobian by $L\mapsto L(-(g-1)p)$. The Abel-image theorem gives an integral effective
Cartier divisor $W_{g-1}$, of dimension $g-1$, as the scheme-theoretic image. By the determinant-
section lemma, the support of the determinant zero scheme is exactly the locus with
$H^0(C,L)\ne0$, since $\chi(L)=0$. A nonzero section of a line on an integral curve cuts out an
effective Cartier divisor with $L\simeq\mathcal O(D)$; the degree formula makes its degree $g-1$.
Conversely the canonical section of $\mathcal O(D)$ is nonzero. Thus this support is precisely
$W_{g-1}$, which is a proper closed subset of the integral $g$-dimensional Jacobian. The
determinant section is therefore nonzero and its zero scheme is an effective Cartier divisor.
Uses: lem-sc-smooth-regular, thm-sc-jacobian-representability, lem-sfb-symmetric-abel-image-
geometry, lem-sfb-rank-zero-perfect-determinant-section, lem-pc-nonzero-section-integral-cartier,
lem-pc-degree-base-change.

8. Choose an effective divisor $D$ of degree $g-1$ with $h^0(\mathcal O(D))=1$ using the small-
degree-divisor lemma, and put $L=\mathcal O(D)$. Riemann--Roch gives $h^1(L)=1$. Choose nonzero
$s\in H^0(L)$ and $t\in H^0(\omega_C\otimes L^{-1})$ by Serre duality. Their product is a nonzero
canonical differential, since both are nonzero at the generic point of the integral curve. The
perfect Serre pairing between $H^1(\mathcal O_C)$ and $H^0(\omega_C)$ supplies $v$ with $\langle
v,st\rangle\ne0$. The split-thickening Picard cocycle lemma realizes $v$ as a tangent direction at
$L$ in $P_k$. By the first-order-obstruction lemma the induced map $H^0(L)\to H^1(L)$ is nonzero.
Uses: lem-sfb-small-degree-divisor-sections, lem-sc-riemann-roch, thm-sc-serre-duality-curve, lem-
sfb-split-thickening-picard-cocycle, lem-sfb-line-section-first-order-obstruction.

9. At $L$ the equal-rank matrix $d_0$ has one-dimensional kernel and cokernel. In a local
trivialization an $(r-1)$-minor is a unit. Elementary row and column operations using that minor
reduce $d$ to an identity block and one scalar $a$ in the maximal ideal; they change its
determinant by a unit. Along Step 8's dual-number direction $\operatorname{Spec}A\to P_k$, perfect
coherent base change makes the pulled-back two-term free complex a model of $R\Gamma(C_A,L_A)$;
the coefficient of $\epsilon$ in $a$ is the nonzero kernel-to-cokernel obstruction, by the model
comparison of the first-order lemma. Consequently the local equation $\det d$ is not in the square
of the maximal ideal at $L$. For $r=1$ this is the same argument with an empty identity block.
This computes multiplicity at a specified point without assuming any generic smoothness of the
Abel map.
Uses: lem-pc-local-invertible-minor-block, lem-sfb-line-section-first-order-obstruction, lem-sfb-
proper-flat-space-derived-base-change.

10. The geometric Jacobian is smooth, so its local rings are regular, hence unique factorization
domains. Let $h$ be a local prime equation for the integral Cartier divisor $W_{g-1}$. Since Step
7 gives equality of supports, the local determinant equation has no prime factor except $h$, and
so is $u h^n$ with $u$ a unit and $n\ge1$. At Step 8's point, $n>1$ would put this equation in the
square of the maximal ideal, contradicting Step 9. Therefore its order at the generic point of
$W_{g-1}$ is one. At every other point of $W_{g-1}$ the exponent is the same generic order
(localizing at $(h)$ gives the generic DVR), so $n=1$ everywhere. The determinant ideal and the
ideal of $W_{g-1}$ consequently agree at every stalk. This proves equality with the scheme-
theoretic Abel image, including its multiplicity and not just its set of points.
Uses: lem-weil-pbc-smooth-scheme-over-field-regular, lem-trf-regular-local-ufd-boundary-
factorization, lem-per-regular-prime-divisor-local-equations.

11. For an etale scheme chart $V\to P$, the map $V\to S$ is flat and locally finitely presented,
since $P\to S$ is smooth (Step 2). The subscheme $Z(s_\Theta)|_V$ is locally principal. Steps 7--
10 show that its every geometric fibre is an effective Cartier divisor. This also holds over the
residue fields themselves: after a faithfully flat algebraic field extension, injectivity of
multiplication by a local equation reflects back, since tensor with a field extension is faithful.
Apply the local fibre-Cartier criterion at each point. It gives that $\Theta|_V$ is effective
Cartier and flat over $S$. These are exactly the asserted chartwise properties on $P$. A regular
line section gives its divisor line canonically: in a local frame $e$ with $s=a e$, the ideal is
$(a)$ and the identification $\mathcal I^{-1}\simeq\mathcal T$ sends the functional $a\mapsto1$ to
$e$. These identifications agree on changes of frame, and their distinguished section is
$s_\Theta$. Thus $\mathcal T\simeq\mathcal O_P(\Theta)$.
Uses: lem-pc-recd-fibre-cartier-local, def-pc-divisor-line-bundle.

12. Base change restricts the Picard sheaf and preserves fibre degrees, so it preserves $P$, $J$,
the tensor action and the tensor formulas for $\beta_p$. Pulling a section divisor through a base
change preserves it and its line module; hence the reference $\mathcal O((g-1)p)$ also pulls back.
On each representing chart, perfect coherent base change identifies the new direct-image complex
with $Lh^*K$. The canonical-section lemma identifies the resulting determinant pair with the
pulled-back pair, compatibly with changing representatives. By the fully faithful descent of maps
of lines these local comparisons give the global comparison of $(\mathcal T,s_\Theta)$, and hence
of its zero divisor, for arbitrary locally Noetherian base change. In particular the fibre
comparisons used in Steps 7--10 are comparisons of the constructed pair.
Uses: sk-def-picard-pic, lem-pc-degree-base-change, lem-pc-recd-pullback, lem-sfb-proper-flat-
space-derived-base-change, lem-sfb-rank-zero-perfect-determinant-section, lem-trf-algebraic-space-
invertible-descent.

13. For a family isomorphism $u:C\simeq D$, the map $b=(u^{-1})^*:P_C\to P_D$ sends a representing
line $U$ to $(u^{-1})^*U$; pulling it back along $u$ recovers $U$. Since $u$ is an isomorphism,
its inverse-image and direct-image functors are inverse exact equivalences on module sheaves.
Applying them to an injective resolution gives the canonical identification of the two derived
direct images, compatible with identity and composition. The determinant functor and section
transport this identification to $b^*(\mathcal T_D,s_D)\simeq(\mathcal T_C,s_C)$. The same tensor
identities give compatibility for the action and for $\beta_p$ with $p$ transported to $u(p)$. For
two base changes, two family isomorphisms, or their combination, the comparisons on lines are the
functorial ones for pulled-back complexes and rank-zero twists; their identity and composition
laws follow from the corresponding laws of the canonical-section lemma and perfect base change.
Fully faithful line descent checks the same equations globally. No point or degree-$g-1$ class is
selected globally in this construction.
Uses: lem-sfb-rank-zero-perfect-determinant-section, lem-sfb-proper-flat-space-derived-base-
change, lem-trf-algebraic-space-invertible-descent.
-/
theorem relative_degree_gminusone_theta : Nonempty (RelativeThetaSystem.{u, w}) := by
  sorry

end AlgebraicGeometry
