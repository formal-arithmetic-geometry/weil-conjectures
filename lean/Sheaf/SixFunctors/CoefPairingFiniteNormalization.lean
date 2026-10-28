module

public import Sheaf.SixFunctors.CoefFinitePairingEvaluationData
public import Sheaf.Paper.FiniteCoefficientPoint
import Sheaf.SixFunctors.CoefFiniteEvaluationExistence
import Sheaf.SixFunctors.CoefFiniteProjectionWordEvaluation

/-! # Finite normalization of the system projection-evaluation word

Source: blueprint latest, prop-coef-integral-dualizing.proof.md, paragraph 2;
Stacks 07A6 and 0B56 (blueprint: lem-coef-pairing-finite-normalization).

All point sections take values in ordinary derived categories of towers, before limits.
Index n denotes the positive coefficient exponent n + 1.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option genInjectivity false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local irreducible] CategoryTheory.Functor.leftAdjoint
  CategoryTheory.Functor.mapDerivedCategory CategoryTheory.Functor.rightDerivedFunctor
  HasDerivedCategory.standard

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme SheafOfModules
namespace WeilConjectures.CoefProjectionEvaluation

attribute [local instance 2000] Limits.instHasColimitOfHasColimitsOfShape
  Limits.instHasLimitOfHasLimitsOfShape
attribute [-instance] SemilinearSections.hasDerived SemilinearSections.moduleAbelian
  SemilinearSections.abelianSheafify SemilinearSections.locallyBijective
  SemilinearSections.sequenceSmall SemilinearSections.sliceSmall

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The geometric-point convention is the recorded final-object section functor,
with exactly its sheafification-unit coefficient action. No geometric point is chosen.
Source: blueprint def-weil-finite-coefficient-point, evaluation paragraph
(blueprint: lem-coef-pairing-finite-normalization). -/
def finitePointSectionsConvention (k : Type u) [Field k] (n : ℕ) :
    finiteSections l E (Spec (.of k)) n ≅
      pointFiniteSections k (Padic.coefficientExtensionRing l E (n + 1)) :=
  Iso.refl _

/-- Identification with the recorded intrinsic compact-support functor, using the
ordinary section-normalized proper comparison and adjoint-compatible open comparison.
This is a comparison of the actual functors, independent of their finite evaluations.
Source: Stacks 03DI, 03D2; blueprint paragraph 2
(blueprint: lem-coef-pairing-finite-normalization). -/
def finiteIntrinsicSupport {X Y : Scheme.{u}} {a : X ⟶ Y}
    (c : Compactification a) (n : ℕ) :
    finiteSupport l E c n ≅
      sfIntrinsicCompactSupport c (Padic.coefficientExtensionRing l E (n + 1)) :=
  letI := proEtaleConstantModuleDirectImage_additive c.g
    (Padic.coefficientExtensionRing l E (n + 1))
  Functor.isoWhiskerLeft
    (ProEtale.StrictTower.moduleJ (compactSupportSystemLevel l E n) c.i).mapDerivedCategory
    (Functor.rightDerivedFunctorNatIso
      (compactSupportDirectModel c.g (Padic.coefficientExtensionRing l E (n + 1)))) ≪≫
    Functor.isoWhiskerRight
      (Functor.mapDerivedCategoryNatIso
        (compactSupportOpenModel c.i (Padic.coefficientExtensionRing l E (n + 1))))
      (proEtaleConstantDerivedDirectImage c.g (Padic.coefficientExtensionRing l E (n + 1)))

namespace FiniteEvaluation
variable {l E} {X Y : Scheme.{u}} {a : X ⟶ Y} {c : Compactification a}
  {m : Model l E c} {s : ScalarSpecialization l E m} {n : ℕ}
  (e : FiniteEvaluation l E m s n)

/-- Quotient-linear support sections evaluation, for every system object.
Source: Stacks 0D6E, 0941 (blueprint: lem-coef-pairing-finite-normalization). -/
def quotientSupport (U : coefficientSequenceDerived.{u, u} l E X) :
    (finitePointEvaluation l E n).obj (m.b U) ≅
      e.finite.b ((coefficientSequenceDerivedEvaluation l E X n).obj U) :=
  e.sectionsY.derived.app (m.support.obj U) ≪≫
    (finiteDerivedSections l E Y n).mapIso ((supportEvaluation l E c n).app U)

/-- Integral support evaluation with the actual scalar restriction square.
Source: Stacks 07A6, 0D6E, 0941 (blueprint: lem-coef-pairing-finite-normalization). -/
def support (U : coefficientSequenceDerived.{u, u} l E X) :
    (coefHomPointEvaluation l E n).obj
      ((coefHomPointDerivedRestriction l E).obj (m.b U)) ≅
      (finiteDerivedRestriction l E n).obj
        (e.finite.b ((coefficientSequenceDerivedEvaluation l E X n).obj U)) :=
  (restrictionEvaluation l E n).app (m.b U) ≪≫
    (finiteDerivedRestriction l E n).mapIso (e.quotientSupport U)

/-- The support comparison at K_n, using the prescribed reduction-unit comparison.
Source: Stacks 07A6, 0941 (blueprint: lem-coef-pairing-finite-normalization). -/
def reducedSupport (K : DerivedCategory (scalarReductionSource.{u, u} l E X)) :
    (coefHomPointEvaluation l E n).obj (s.supportTower K) ≅
      (finiteDerivedRestriction l E n).obj
        (e.finite.b ((coefficientFiniteDerivedExtension l E X n).obj K)) :=
  e.support (s.reduced K) ≪≫
    (finiteDerivedRestriction l E n).mapIso
      ((finiteDerivedSections l E Y n).mapIso
        ((finiteSupport l E c n).mapIso ((s.reductionEvaluation n).app K)))

/-- The finite Hom comparison: the full-system scalar-Hom comparison, exact
restriction/evaluation, sections evaluation, closed Hom evaluation, then K_n reduction.
Thus no isomorphism is chosen by reconstructing maps from their finite components.
Source: Stacks 07A6, 08J9, 0941 (blueprint: lem-coef-pairing-finite-normalization). -/
def homComparison (K : DerivedCategory (scalarReductionSource.{u, u} l E X))
    (N : coefficientSequenceDerived.{u, u} l E X) :
    (coefHomPointEvaluation l E n).obj ((coefHomTower l E X).obj (op K, N)) ≅
      (finiteDerivedRestriction l E n).obj
        (e.finite.h ((coefficientFiniteDerivedExtension l E X n).obj K)
          ((coefficientSequenceDerivedEvaluation l E X n).obj N)) :=
  (coefHomPointEvaluation l E n).mapIso (s.comparison.app (op K, N)) ≪≫
    (restrictionEvaluation l E n).app (Model.h (s.reduced K) N) ≪≫
    (finiteDerivedRestriction l E n).mapIso
      (e.sectionsX.derived.app (Model.hom (s.reduced K) N) ≪≫
        (finiteDerivedSections l E X n).mapIso (e.hom K N) ≪≫
        (finiteDerivedSections l E X n).mapIso
          ((coefficientFiniteInternalHom l E X n).mapIso
            (Iso.prod ((s.reductionEvaluation n).app K).symm.op (Iso.refl _))))

/-- The exact evaluated pairing equation at each positive coefficient exponent.
Its right-hand arrow is definitionally the scalar balance followed by the finite
sections/proper/open/evaluation word in FiniteModel.beta.
Source: blueprint paragraph 2; Stacks 07A6, 0B56
(blueprint: lem-coef-pairing-finite-normalization). -/
def PairingEquation : Prop :=
  ∀ (K : DerivedCategory (scalarReductionSource.{u, u} l E X))
    (N : coefficientSequenceDerived.{u, u} l E X),
    (coefHomPointEvaluation l E n).map (s.transported K N) ≫ (e.support N).hom =
      e.integral.derived.hom.app
        ((coefHomTower l E X).obj (op K, N), s.supportTower K) ≫
      e.finite.integralTensor.map
        (Prod.mkHom (e.homComparison K N).hom (e.reducedSupport K).hom) ≫
      e.finite.beta ((coefficientFiniteDerivedExtension l E X n).obj K)
        ((coefficientSequenceDerivedEvaluation l E X n).obj N)

end FiniteEvaluation

/-- Finite evaluation of the already constructed system projection-evaluation pairing.
The comparisons retain the actual quotient actions, pure tensors, normalized derived
units/counits, pullback compositions and sheafified open chain map. The equality is on
ordinary unbounded derived categories of towers before inverse limit, for arbitrary K
and arbitrary second input N; no preservation of K-injectives by evaluation is assumed.

Source: blueprint latest, prop-coef-integral-dualizing.proof.md, paragraph 2;
Stacks 07A6 (adjunction), 0B56 (projection-formula map), 08J9, 0941
(blueprint: lem-coef-pairing-finite-normalization).

Proof: first use the actual constant coefficient and quotient maps to identify the
finite reductions of M with K tensor A_(n+1), including their quotient transitions.
Associativity of scalar extension makes M cartesian, so the cartesian-first-input
Hom evaluation comparison applies to arbitrary N. Its transpose is exactly finite
closed evaluation, giving FiniteEvaluation.hom_normalization. Compose it with the
normalized sections comparison and the full-system scalar-Hom isomorphism to obtain
homComparison. For point sections and proper direct image, evaluate the ordinary
adjunction unit and counit, then use their universal derived normalizations. These
give the displayed unit/counit equations and preserve all transposes. Applying this to the proper
projection transpose gives precisely (epsilon tensor 1) after the strong pullback
comparison. The same argument gives the finite sections projection and the finite
g_X counit. Exact evaluation of the actual pure-tensor open chain map gives finite
gamma, by the recorded open normalization theorem; its chain formula is sheafified
u tensor l mapping to u tensor the restriction of l. The direct-image and pullback
composition comparisons preserve their units and counits, so the compactification
factorization and sections composition yield the displayed composition equations.
On the scalar point square, the ordinary R-to-A_(n+1) adjunction and its tensor
comparison identify the evaluated scalar projection followed by the scalar counit
with finite scalar balancing. Signed totalization preserves the symmetry. Evaluate
the already specified composite Model.beta factor by factor and substitute these
identities in the same order. The proper/open part is the ambient projection word
of def-exchange-projection, with the canonical sheafified open chain factor. Exact
restriction and separately derived proper image give support for arbitrary N;
compose reductionEvaluation to obtain reducedSupport. Finally substitute the exact
full-system Hom transport defining ScalarSpecialization.transported. Functoriality
and naturality cancel consecutive comparison inverses, giving PairingEquation. No
system morphism is reconstructed from compatible finite derived maps, and no step
requires a varying-ring evaluation of a K-injective complex to remain K-injective.
At a geometric finite-field point, finiteSections is evaluation at the final
pro-etale object with its quotient coefficient action, the recorded point convention. -/
theorem pairingFiniteNormalization
    (k : Type u) [Field k] (X Y : Scheme.{u})
    [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    (a : X ⟶ Y) [a.IsOver (Spec (.of k))]
    [IsSeparated a] [LocallyOfFiniteType a] [QuasiCompact a]
    (_hl : IsUnit (l : k)) (c : Compactification a)
    (m : Model l E c) (s : ScalarSpecialization l E m) :
    ∀ n : ℕ, ∃ e : FiniteEvaluation l E m s n, e.PairingEquation := by
  intro n
  obtain ⟨e⟩ := finiteEvaluation_exists l E k X Y a _hl c m s n
  refine ⟨e, ?_⟩
  intro K N
  have hword := finiteProjectionWord_evaluation l E e K N
  have hnat := e.integral.derived.hom.naturality
    (Prod.mkHom (s.comparison.hom.app (op K, N)) (𝟙 (s.supportTower K)))
  dsimp only [Functor.comp_map, Functor.prod_map] at hnat
  simp only [ScalarSpecialization.transported, Functor.map_comp, Category.assoc]
  dsimp only [FiniteEvaluation.support, FiniteEvaluation.quotientSupport]
  rw [hword]
  erw [← Category.assoc, hnat]
  simp only [Category.assoc]
  simp only [FiniteEvaluation.homComparison, Iso.trans_hom, Functor.mapIso_hom,
    Category.assoc]
  rw [← Functor.map_comp_assoc]
  congr 2
  congr 1
  simp [FiniteEvaluation.reducedSupport, FiniteEvaluation.support,
    FiniteEvaluation.quotientSupport, coefHomPointEvaluation, Functor.map_comp, Category.assoc]


end WeilConjectures.CoefProjectionEvaluation
