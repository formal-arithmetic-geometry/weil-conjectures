module

public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Sheaf.AlgebraicGeometry.EtaleClosedAmbientAdjoint
public import Sheaf.AlgebraicGeometry.EtaleCompactSupportComparisons
public import Sheaf.AlgebraicGeometry.EtaleTorAmplitude
public import Sheaf.Paper.EtaleCompactSupportCoefficientChange
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
public import WeilConjectures.SixFunctors.Etale.Derived.Dualizing
public import WeilConjectures.SixFunctors.Finite.Exact
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusExact
public import WeilConjectures.Compactification.NagataCompactification
public import Mathlib.AlgebraicGeometry.AffineSpace
public import WeilConjectures.AlgebraicGeometry.AffineSpaceClosedChart
public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.SixFunctors.Etale.Derived.Tensor
import Sheaf.Paper.BoundaryEtaleAdjunctionRestriction
import Sheaf.AlgebraicGeometry.EtaleSupportedKernelAdjunction
import Sheaf.AlgebraicGeometry.AffineFiniteTypeAlgebra
import Sheaf.CategoryTheory.ExactDerivedAdjunctionBounds
import Sheaf.CategoryTheory.RingedSiteModules
import Mathlib.RingTheory.FiniteType
import Mathlib.CategoryTheory.Adjunction.Unique
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology

/-!
# Closed affine charts and normalized dualizing composition

Source: main-20261015, sec-smooth-purity/sk-lem-sp-tower/
lem-coef-finite-dualizing.proof.md, paragraph 2 and the counit sentence of paragraph 3
(blueprint: lem-coef-dualizing-closed-chart).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

/-- Identify closed derived pushforward with compact support on bounded-below objects,
using the identity-open compactification and the recorded refinement comparison.
Source: main-20261015, finite-dualizing proof, paragraph 2
(blueprint: lem-coef-dualizing-closed-chart). -/
def coefClosedChartPlusPushforwardIso
    (R : Type (u + 1)) [CommRing R] [Finite R]
    {Y P : Scheme.{u}} (i : Y ⟶ P) [IsClosedImmersion i] :
    (lowerStar (ModuleCat.{u + 1} R) i).rightDerivedFunctorPlus ≅
      rightDerivedLowerShriekPlus (ModuleCat.{u + 1} R) i :=
  (Functor.leftUnitor _).symm ≪≫
    Functor.isoWhiskerRight
      (Functor.mapDerivedCategoryPlusNatIso
        (openImmersionLowerShriekId (ModuleCat.{u + 1} R) Y) ≪≫
        Functor.mapDerivedCategoryPlusIdIso _).symm _ ≪≫
    rightDerivedLowerShriekOfCompactificationPlusIso R
      (Compactification.ofIsProper i) (HasCompactification.compactification i)

/-- The canonical comparison `F_P Ri_* -> F_Y`, restricted to `D+`. The construction
uses precisely bounded-below compact-support composition, with closed pushforward
normalized by its identity-open compactification; it makes no unbounded composition claim.
Source: main-20261015, finite-dualizing proof, paragraph 2
(blueprint: lem-coef-dualizing-closed-chart). -/
def coefClosedChartComposition
    (R : Type (u + 1)) [CommRing R] [Finite R]
    {Y P s : Scheme.{u}} (i : Y ⟶ P) [IsClosedImmersion i]
    (p : P ⟶ s) (aY : Y ⟶ s) (h : i ≫ p = aY)
    [HasCompactification p] [HasCompactification aY]
    [HasCompactification (i ≫ p)] [QuasiCompact (i ≫ p)] :
    _root_.DerivedCategory.Plus.ι ⋙
        ((lowerStar (ModuleCat.{u + 1} R) i).rightDerivedFunctor ⋙
          rightDerivedLowerShriek (ModuleCat.{u + 1} R) p) ≅
      _root_.DerivedCategory.Plus.ι ⋙
        rightDerivedLowerShriek (ModuleCat.{u + 1} R) aY :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (lowerStar (ModuleCat.{u + 1} R) i).rightDerivedFunctorPlusCompatibility.symm _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _
      (rightDerivedLowerShriekPlusCompatibility (ModuleCat.{u + 1} R) p).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (Functor.isoWhiskerRight (coefClosedChartPlusPushforwardIso R i) _ ≪≫
        rightDerivedLowerShriekPlusCompIso R i p ≪≫
        rightDerivedLowerShriekPlusCongr R h) _ ≪≫
    rightDerivedLowerShriekPlusCompatibility (ModuleCat.{u + 1} R) aY

/-- Transport a closed counit through the canonical bounded-below composition.
This is the actual composite morphism, not an independently supplied comparison.
Source: main-20261015, finite-dualizing proof, paragraph 3
(blueprint: lem-coef-dualizing-closed-chart). -/
def coefClosedChartCompositeCounit
    (R : Type (u + 1)) [CommRing R] [Finite R]
    {Y P s : Scheme.{u}} (i : Y ⟶ P) [IsClosedImmersion i]
    (p : P ⟶ s) (aY : Y ⟶ s) (h : i ≫ p = aY)
    [HasCompactification p] [HasCompactification aY]
    [HasCompactification (i ≫ p)] [QuasiCompact (i ≫ p)]
    (K : _root_.DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R)))
    (L : DerivedCategoryModule R P)
    (f : K.obj ⟶ (lowerStar (ModuleCat.{u + 1} R) i).rightDerivedFunctor.rightAdjoint.obj L) :
    (rightDerivedLowerShriek (ModuleCat.{u + 1} R) aY).obj K.obj ⟶
      (rightDerivedLowerShriek (ModuleCat.{u + 1} R) p).obj L :=
  (coefClosedChartComposition R i p aY h).inv.app K ≫
    (rightDerivedLowerShriek (ModuleCat.{u + 1} R) p).map
      ((lowerStar (ModuleCat.{u + 1} R) i).rightDerivedFunctor.map f) ≫
    (rightDerivedLowerShriek (ModuleCat.{u + 1} R) p).map
      ((Adjunction.ofIsLeftAdjoint
        (lowerStar (ModuleCat.{u + 1} R) i).rightDerivedFunctor).counit.app L)

/-- The closed-chart clauses for one coefficient ring. All objects and adjunctions
are the ordinary small-etale ones. The unique comparison is normalized by the
structural counit through the canonical bounded-below composition comparison.
Source: main-20261015, finite-dualizing proof, paragraph 2 and paragraph 3
(blueprint: lem-coef-dualizing-closed-chart). -/
structure CoefClosedChartProperties
    (R : Type (u + 1)) [CommRing R] [Finite R]
    {Y P s : Scheme.{u}} (i : Y ⟶ P) [IsClosedImmersion i]
    (p : P ⟶ s) (aY : Y ⟶ s) (h : i ≫ p = aY)
    [HasCompactification p] [HasCompactification aY]
    [HasCompactification (i ≫ p)] [QuasiCompact (i ≫ p)] : Prop where
  exact_limits : PreservesFiniteLimits (lowerStar (ModuleCat.{u + 1} R) i)
  exact_colimits : PreservesFiniteColimits (lowerStar (ModuleCat.{u + 1} R) i)
  identity_open : Nonempty
    (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} R)
        (Compactification.ofIsProper i) ≅
      (lowerStar (ModuleCat.{u + 1} R) i).mapDerivedCategory)
  derived_pushforward : Nonempty
    ((lowerStar (ModuleCat.{u + 1} R) i).rightDerivedFunctor ≅
      (lowerStar (ModuleCat.{u + 1} R) i).mapDerivedCategory)
  cohomology : ∀ q : ℤ, Nonempty
    ((lowerStar (ModuleCat.{u + 1} R) i).rightDerivedFunctor ⋙
        _root_.DerivedCategory.homologyFunctor _ q ≅
      _root_.DerivedCategory.homologyFunctor _ q ⋙ lowerStar (ModuleCat.{u + 1} R) i)
  closed_boundedBelow : ∀ L : DerivedCategoryModule R P,
    _root_.DerivedCategory.TStructure.t.plus L →
    _root_.DerivedCategory.TStructure.t.plus
      ((lowerStar (ModuleCat.{u + 1} R) i).rightDerivedFunctor.rightAdjoint.obj L)
  omegaY_boundedBelow : _root_.DerivedCategory.TStructure.t.plus
    (dualizingComplex (ModuleCat.{u + 1} R) aY)
  omegaP_boundedBelow : _root_.DerivedCategory.TStructure.t.plus
    (dualizingComplex (ModuleCat.{u + 1} R) p)
  closed_omegaP_boundedBelow : _root_.DerivedCategory.TStructure.t.plus
    ((lowerStar (ModuleCat.{u + 1} R) i).rightDerivedFunctor.rightAdjoint.obj
      (dualizingComplex (ModuleCat.{u + 1} R) p))

/-- The unique counit-normalized identification of the two representing objects.
The bound is used only to apply the canonical bounded-below composition comparison.
Source: main-20261015, finite-dualizing proof, paragraph 3
(blueprint: lem-coef-dualizing-closed-chart). -/
def CoefClosedChartNormalization
    (R : Type (u + 1)) [CommRing R] [Finite R]
    {Y P s : Scheme.{u}} (i : Y ⟶ P) [IsClosedImmersion i]
    (p : P ⟶ s) (aY : Y ⟶ s) (h : i ≫ p = aY)
    [HasCompactification p] [HasCompactification aY]
    [HasCompactification (i ≫ p)] [QuasiCompact (i ≫ p)]
    (hY : _root_.DerivedCategory.TStructure.t.plus
      (dualizingComplex (ModuleCat.{u + 1} R) aY)) : Prop :=
  ∃! θ : dualizingComplex (ModuleCat.{u + 1} R) aY ≅
      (lowerStar (ModuleCat.{u + 1} R) i).rightDerivedFunctor.rightAdjoint.obj
        (dualizingComplex (ModuleCat.{u + 1} R) p),
    coefClosedChartCompositeCounit R i p aY h
        ⟨dualizingComplex (ModuleCat.{u + 1} R) aY, hY⟩
        (dualizingComplex (ModuleCat.{u + 1} R) p) θ.hom ≫
      (rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} R) p).counit.app
        (constantComplex R s) =
      (rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} R) aY).counit.app
        (constantComplex R s)

/-- Install the coefficient finiteness and compactifications that follow from the
geometric hypotheses, then state the closed-chart clauses. These are consequences,
not extra hypotheses. The coefficient lift is the common small-etale size convention.
Source: main-20261015, finite-dualizing proof, paragraph 2
(blueprint: lem-coef-dualizing-closed-chart). -/
def CoefClosedChartAt
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (j : ℕ) (hj : 1 ≤ j)
    {Y P : Scheme.{u}} (i : Y ⟶ P) [IsClosedImmersion i]
    (k : Type u) [Field k] (p : P ⟶ Spec (.of k)) (aY : Y ⟶ Spec (.of k))
    [IsSeparated p] [LocallyOfFiniteType p] [QuasiCompact p]
    [IsSeparated aY] [LocallyOfFiniteType aY] [QuasiCompact aY]
    (h : i ≫ p = aY) : Prop :=
  letI : Finite (Padic.coefficientExtensionRing l E j) :=
    Padic.finite_coefficientExtensionRing l E j hj
  letI : HasCompactification (i ≫ p) := HasCompactification.of_eq h.symm
  ∃ H : CoefClosedChartProperties
      (ULift.{u + 1} (Padic.coefficientExtensionRing l E j)) i p aY h,
    CoefClosedChartNormalization
      (ULift.{u + 1} (Padic.coefficientExtensionRing l E j)) i p aY h H.omegaY_boundedBelow

/-- The coefficient-theoretic part of the closed-chart construction.

This is the remaining bounded-below compact-support and dualizing comparison argument
after a closed affine-space chart has been chosen. It is split from the geometric
existence theorem so that the two coefficient levels can be proved independently.
Source: main-20261015, sec-smooth-purity/sk-lem-sp-tower/
lem-coef-finite-dualizing.proof.md, paragraphs 2--3
(blueprint: lem-coef-dualizing-closed-chart-properties). -/
theorem coefClosedChartAt_of_closed_chart
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (m n : ℕ) (hm : 1 ≤ m) (hmn : m ≤ n)
    {Y P : Scheme.{u}} (i : Y ⟶ P) [IsClosedImmersion i]
    (k : Type u) [Field k] (p : P ⟶ Spec (.of k)) (aY : Y ⟶ Spec (.of k))
    [IsSeparated p] [LocallyOfFiniteType p] [QuasiCompact p]
    [IsSeparated aY] [LocallyOfFiniteType aY] [QuasiCompact aY]
    (h : i ≫ p = aY) :
    CoefClosedChartAt l E m hm i k p aY h ∧
      CoefClosedChartAt l E n (hm.trans hmn) i k p aY h := by
  sorry

set_option linter.unusedVariables false in
/-- Every affine separated finite-type scheme has a closed affine-space chart with
exact ordinary pushforward and the counit-normalized dualizing composition at both
positive coefficient levels. Both representing objects are independently bounded below.

Source: main-20261015, sec-smooth-purity/sk-lem-sp-tower/
lem-coef-finite-dualizing.proof.md, paragraph 2 and paragraph 3
(blueprint: lem-coef-dualizing-closed-chart).

Proof:
1. Write Y = Spec D. Finite type gives a surjection from a polynomial ring in finitely
   many variables onto D (lem-pc-affine-finite-type-algebra and
   def-weil-pbc-finite-type-algebra). The affine criterion for a closed immersion
   (lem-weil-pbc-closed-immersion-affine-cover-criterion) gives the chart over k.
2. Closed immersions are finite and proper. The polynomial projection is separated
   and finite type. This includes the empty source and zero variables.
3. At each positive coefficient stage, lem-weil-boundary-etale-adjunction-restriction
   supplies Noetherianity, compactifications, and D+-preserving ambient structural
   adjoints. Applying them to the degree-zero coefficient object bounds omegaY and
   omegaP without coefficient change.
4. lem-pur-etale-supported-kernel-adjunction gives exact closed abelian pushforward.
   The forgetful-compatible module direct image, kernels and cokernels transfer this
   to all module sheaves, without constructibility.
5. lem-weil-pbc-exact-functor-derived-factorization identifies unbounded derived
   pushforward with termwise pushforward. The identity-open compactification therefore
   gives Ri! = Ri* = i*, and lem-weil-pbc-exact-functor-complex-cohomology gives the
   natural cohomology isomorphism in every integer degree.
6. By lem-pur-exact-derived-adjunction-bounds(1), the closed right adjoint preserves
   every lower bound, hence D+ and the bound for I omegaP.
7. lem-amb-etale-compact-comparisons supplies the canonical composition on D+.
   Restrict all the ambient adjunctions using the independent bounds just established.
8. Compose adjunctions (def-weil-pbc-composite-adjunction) and use uniqueness of right
   adjoints (det-sp-unique-right-adjoint). Their unique counit-compatible identification
   at the coefficient object is theta. The composite counit is Fp(e) followed by
   epsilonP; transposing through the canonical composition gives the displayed equation.
-/
theorem exists_coefDualizingClosedChart
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (m n : ℕ) (hm : 1 ≤ m) (hmn : m ≤ n)
    (Y : Scheme.{u}) (aY : Y ⟶ Spec (.of D.k))
    [IsAffine Y] [IsSeparated aY] [LocallyOfFiniteType aY] [QuasiCompact aY] :
    ∃ (r : ℕ) (i : Y ⟶ AffineSpace (ULift.{u} (Fin r)) (Spec (.of D.k))),
      IsClosedImmersion i ∧ ∀ [hi : IsClosedImmersion i],
      i ≫ (AffineSpace (ULift.{u} (Fin r)) (Spec (.of D.k)) ↘ Spec (.of D.k)) = aY ∧
      IsFinite i ∧ IsProper i ∧ LocallyOfFiniteType i ∧ QuasiCompact i ∧
      ∀ h : i ≫ (AffineSpace (ULift.{u} (Fin r)) (Spec (.of D.k)) ↘
          Spec (.of D.k)) = aY,
        CoefClosedChartAt l E m hm i D.k
          (AffineSpace (ULift.{u} (Fin r)) (Spec (.of D.k)) ↘ Spec (.of D.k)) aY h ∧
        CoefClosedChartAt l E n (hm.trans hmn) i D.k
          (AffineSpace (ULift.{u} (Fin r)) (Spec (.of D.k)) ↘ Spec (.of D.k)) aY h := by
  obtain ⟨r, i, hi_over, hclosed⟩ :=
    exists_isClosedImmersion_affineSpace_of_isAffine aY
  let P := AffineSpace (ULift.{u} (Fin r)) (Spec (.of D.k))
  let p : P ⟶ Spec (.of D.k) := P ↘ Spec (.of D.k)
  have : IsClosedImmersion i := hclosed
  refine ⟨r, i, hclosed, ?_⟩
  intro hi
  let : IsClosedImmersion i := hi
  have hfinite : IsFinite i := inferInstance
  have hproper : IsProper i := inferInstance
  have hlft : LocallyOfFiniteType i := inferInstance
  have hqc : QuasiCompact i := inferInstance
  refine ⟨hi_over, hfinite, hproper, hlft, hqc, ?_⟩
  intro h
  exact coefClosedChartAt_of_closed_chart l E m n hm hmn i D.k p aY h

end AlgebraicGeometry.Etale
