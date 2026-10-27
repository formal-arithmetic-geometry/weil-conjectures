/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NM
-/
module

public import Sheaf.SixFunctors.CoefSystemProjectionEvaluation
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Sheaf.Paper.CompletedIntegralConstantMapOfUniverses
public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Sheaf.Paper.CoefficientRingedSequenceSite
public import Sheaf.Algebra.Homology.DerivedInternalHomMixedUniverses
public import Sheaf.Paper.CoefficientRingedTensorHomModel
public import WeilConjectures.Compactification.RefinementCategory
public import Sheaf.AlgebraicGeometry.SfIntrinsicCompactSupport
public import Sheaf.Paper.DerivedScalarExtensionRestrictionAdjunction
public import Sheaf.SixFunctors.CoefHomTowerScalarModel
import Sheaf.Paper.ProjectionMateExact
import Sheaf.Paper.CoefSupportOpenTensorModel

/-! # Dinaturality of the system projection-evaluation word

Source: blueprint latest, prop-coef-integral-dualizing.proof.md, paragraph 2;
Stacks Project, Tags 08J9, 07A6 and 0B56
(blueprint: lem-coef-pairing-system-dinaturality).

The maps below are the recorded whole-system maps before any trace or inverse limit.
The natural-number index n of the imported coefficient systems denotes exponent n+1.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.CoefProjectionEvaluation

attribute [-instance] SemilinearSections.hasDerived SemilinearSections.moduleAbelian
  SemilinearSections.abelianSheafify SemilinearSections.locallyBijective
  SemilinearSections.sequenceSmall SemilinearSections.sliceSmall

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The bifunctor h, retaining quotient scalars and the entire tower index.
Source: Stacks 08J9, 0941 (blueprint: lem-coef-pairing-system-dinaturality). -/
def systemHomSections (X : Scheme.{u}) :
    (coefficientSequenceDerived.{u, u} l E X)ᵒᵖ ×
      coefficientSequenceDerived.{u, u} l E X ⥤
        DerivedCategory (coefHomQuotientPointModules.{u, u} l E) :=
  coefficientSequenceInternalHom.{u, u} l E X ⋙ coefHomQuotientDerivedSections.{u, u} l E X

/-- The same Hom-sections bifunctor after exact scalar restriction rho_0*.
Source: Stacks 07A6, 0941 (blueprint: lem-coef-pairing-system-dinaturality). -/
def integralHomSections (X : Scheme.{u}) :
    (coefficientSequenceDerived.{u, u} l E X)ᵒᵖ ×
      coefficientSequenceDerived.{u, u} l E X ⥤
        DerivedCategory (coefHomPointModules.{u, u} l E) :=
  systemHomSections l E X ⋙ coefHomPointDerivedRestriction.{u, u} l E

namespace Model
variable {l E} {X Y : Scheme.{u}} {a : X ⟶ Y} {c : Compactification a}
  (m : Model l E c)

/-- The actual functor B: quotient compact support, point sections, scalar restriction.
Source: blueprint paragraph 2; Stacks 0941
(blueprint: lem-coef-pairing-system-dinaturality). -/
def integralSupport : coefficientSequenceDerived.{u, u} l E X ⥤
    DerivedCategory (coefHomPointModules.{u, u} l E) :=
  m.support ⋙ coefHomQuotientDerivedSections.{u, u} l E Y ⋙
    coefHomPointDerivedRestriction.{u, u} l E

/-- Closed evaluation with U on the left, using the recorded graded symmetry.
Source: Stacks 08J9; blueprint paragraph 2
(blueprint: lem-coef-pairing-system-dinaturality). -/
def leftEvaluation (U N : coefficientSequenceDerived.{u, u} l E X) :
    m.x.data.systemClosed.tensor.obj (U, hom U N) ⟶ N :=
  (m.x.symmetry.toBraidedCategory.braiding U (hom U N)).hom ≫
    m.x.data.systemClosed.evaluation U N

end Model

/-- The recorded full-system derived reduction functor M, with its actual transitions.
Source: Stacks 06YY, 0941 (blueprint: lem-coef-pairing-system-dinaturality). -/
def ScalarSpecialization.reductionFunctor
    {X Y : Scheme.{u}} {a : X ⟶ Y} {c : Compactification a} {m : Model l E c}
    (s : ScalarSpecialization l E m) :
    DerivedCategory (scalarReductionSource.{u, u} l E X) ⥤
      coefficientSequenceDerived.{u, u} l E X :=
  coefHomDerivedConstant.{u, u} l E X ⋙
    SheafOfModules.ScalarDerivedPair.derived.{u + 1, u, u + 1, u + 2}
      (ScalarHomModels.scalar.{u + 1, u, u, u + 2} s.scalar
        (coefHomScalarMap.{u, u} l E X))

/-- The specified word is dinatural in its Hom source and natural in its target,
with closed evaluation and source-counit normalization, and the corresponding
identity after the canonical full-system scalar Hom comparison.
The model arguments name the normalized data supplied by projectionEvaluation;
no naturality of the resulting pairing is assumed in those data.

Source: blueprint latest, prop-coef-integral-dualizing.proof.md, paragraph 2;
Stacks 08J9, 07A6, 0B56 (blueprint: lem-coef-pairing-system-dinaturality).

Proof:
1. Transpose both closed-evaluation composites through the recorded closed
adjunction. Both transpose to RHom(u,N). Target naturality is counit naturality.
Naturality of the prescribed graded symmetry gives the displayed left convention;
degree-zero u and v introduce no additional sign.
2. Apply naturality of the g_X counit and the pullback-composition comparison to
RHom(u,N). Tensor with U and use step 1. This gives the identity for Model.v on
U tensor La* Lg_Y* h(U',N). The same argument applies to the target arrow v.
3. The proper projection mate and the open tensor comparison are natural in both
arguments. Move the maps through these two factors of Model.Pi in their specified
order. This uses no invertibility or finite-Tor hypothesis.
4. Apply two-variable naturality of the sections projection mate, then step 3,
then the counit identities of step 2. This proves both identities for Model.q.
5. Naturality of the restriction projection mate and its scalar-extension counit
gives naturality of Model.balance in both arguments. The point symmetry is natural.
6. Expand Model.beta as balance, symmetry and q. Move the source map through
balance and symmetry, substitute step 4 and move the compact-support map back.
For target naturality, use the second q identity and move the Hom target map
through the same factors. These are equalities of whole-system derived morphisms;
finite evaluations are not used to detect equality.
7. The normalized comparison in coefHomTowerScalarModel is natural in the derived
source K. Thus its component at K followed by H_N(f) equals the h(M(f),N) map
followed by its component at K'. Substitute this square into
ScalarSpecialization.transported and apply step 6 with u=M(f). Tensor
bifunctoriality yields the final identity, before trace or inverse limit. -/
theorem systemPairingDinaturality
    (k : Type u) [Field k] (X Y : Scheme.{u})
    [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    (a : X ⟶ Y) [a.IsOver (Spec (.of k))]
    [IsSeparated a] [LocallyOfFiniteType a] [QuasiCompact a]
    (_hl : IsUnit (l : k)) (c : Compactification a) (m : Model l E c) :
    (∀ (U U' N : coefficientSequenceDerived.{u, u} l E X) (u : U ⟶ U'),
      m.point.rTensor.map
          (Prod.mkHom ((integralHomSections l E X).map (Prod.mkHom u.op (𝟙 N)))
            (𝟙 (m.integralSupport.obj U))) ≫ m.beta U N =
        m.point.rTensor.map
          (Prod.mkHom (𝟙 ((integralHomSections l E X).obj (op U', N)))
            (m.integralSupport.map u)) ≫ m.beta U' N) ∧
    (∀ (U N N' : coefficientSequenceDerived.{u, u} l E X) (v : N ⟶ N'),
      m.beta U N ≫ m.integralSupport.map v =
        m.point.rTensor.map
          (Prod.mkHom ((integralHomSections l E X).map (Prod.mkHom (𝟙 (op U)) v))
            (𝟙 (m.integralSupport.obj U))) ≫ m.beta U N') ∧
    (∀ (U U' N : coefficientSequenceDerived.{u, u} l E X) (u : U ⟶ U'),
      m.x.data.systemClosed.tensor.map
          (Prod.mkHom (𝟙 U)
            ((coefficientSequenceInternalHom.{u, u} l E X).map (Prod.mkHom u.op (𝟙 N)))) ≫
          m.leftEvaluation U N =
        m.x.data.systemClosed.tensor.map (Prod.mkHom u (𝟙 (Model.hom (l := l) (E := E) U' N))) ≫
          m.leftEvaluation U' N) ∧
    (∀ (U U' N : coefficientSequenceDerived.{u, u} l E X) (u : U ⟶ U'),
      m.x.data.systemClosed.tensor.map
          (Prod.mkHom (𝟙 U)
            ((ProEtale.VaryingRing.G.{u} (compactSupportSystemLevel l E)
              (compactSupportSystemQuotient l E) a).map
                (m.gy.left.map ((systemHomSections l E X).map (Prod.mkHom u.op (𝟙 N)))))) ≫
          m.v U N =
        m.x.data.systemClosed.tensor.map
          (Prod.mkHom u
            (𝟙 ((ProEtale.VaryingRing.G.{u} (compactSupportSystemLevel l E)
              (compactSupportSystemQuotient l E) a).obj
                (m.gy.left.obj (Model.h (l := l) (E := E) U' N))))) ≫ m.v U' N) ∧
    (∀ (s : ScalarSpecialization l E m)
      (K K' : DerivedCategory (scalarReductionSource.{u, u} l E X))
      (N : coefficientSequenceDerived.{u, u} l E X) (f : K ⟶ K'),
      m.point.rTensor.map
          (Prod.mkHom ((coefHomTower.{u, u} l E X).map (Prod.mkHom f.op (𝟙 N)))
            (𝟙 (ScalarSpecialization.supportTower.{u} s K))) ≫
          ScalarSpecialization.transported.{u} s K N =
        m.point.rTensor.map
          (Prod.mkHom (𝟙 ((coefHomTower.{u, u} l E X).obj (op K', N)))
            (m.integralSupport.map
              ((ScalarSpecialization.reductionFunctor l E s).map f))) ≫
          ScalarSpecialization.transported.{u} s K' N) := by
  sorry

end WeilConjectures.CoefProjectionEvaluation
