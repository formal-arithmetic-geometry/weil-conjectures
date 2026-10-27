module

public import Sheaf.AlgebraicGeometry.RelativePseudoCoherentComplex
public import Sheaf.AlgebraicGeometry.CoherentFiniteType
public import WeilConjectures.AlgebraicGeometry.DerivedAdjoint
public import WeilConjectures.AlgebraicGeometry.CanonicalPullbackTensorComparison
public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Defs
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.RingTheory.Noetherian.Defs

import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import WeilConjectures.AlgebraicGeometry.AffineDerivedPushforwardTExact
import Sheaf.AlgebraicGeometry.ClosedSupportRelativePseudoCoherence
import WeilConjectures.AlgebraicGeometry.AffinePushforwardResolutionQuasiIso
import WeilConjectures.AlgebraicGeometry.AffineQCohDerivedEquivalence
import WeilConjectures.AlgebraicGeometry.PseudoCoherentComplex
import WeilConjectures.AlgebraicGeometry.AffinePseudoCoherentCriterion
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import WeilConjectures.AlgebraicGeometry.AffineDerivedPullbackModuleModel
import WeilConjectures.AlgebraicGeometry.DerivedTensorStructure
import WeilConjectures.AlgebraicGeometry.AffineDerivedPullbackTensorTilde
import WeilConjectures.AlgebraicGeometry.DerivedDirectImageCompositionUnbounded
import WeilConjectures.AlgebraicGeometry.DerivedPullbackComposition

/-! # Relative sheaf descente on a prescribed Noetherian envelope

Source: agent-formulated sheaf approximation prerequisite for the Kiehl assertion following
Stacks Project, perfect.tex, Tag 0CSD
(blueprint: lem-sfb-prescribed-envelope-relative-sheaf-descente).
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u w

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated MonoidalCategory

namespace AlgebraicGeometry

noncomputable section

variable [∀ S : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings S.toRingedSpace))]

/-- The coefficient sheaf A on Spec R with its specified R-action.
Source: the coefficient M in the agent-formulated prerequisite following Stacks Tag 0CSD
(blueprint: lem-sfb-prescribed-envelope-relative-sheaf-descente). -/
def envelopeCoefficientSheaf {R A : CommRingCat.{u}} (φ : R ⟶ A) :
    SheafOfModules.{u} (moduleRings (Spec R).toRingedSpace) :=
  tilde ((ModuleCat.restrictScalars φ.hom).obj (ModuleCat.of A A))

/-- The coefficient module in degree zero.
Source: the coefficient M in the agent-formulated prerequisite following Stacks Tag 0CSD
(blueprint: lem-sfb-prescribed-envelope-relative-sheaf-descente). -/
def envelopeCoefficient {R A : CommRingCat.{u}} (φ : R ⟶ A) :
    schemeDerivedCategory (Spec R) :=
  (DerivedCategory.singleFunctor _ 0).obj (envelopeCoefficientSheaf φ)

/-- The canonical derived-to-ordinary pullback map on a degree-zero module. This is
constructed from the shared left-derived counit, without any flatness hypothesis.
Source: Stacks Tags 06YJ and 0CSD, the scalar-action construction in the prerequisite
(blueprint: lem-sfb-prescribed-envelope-relative-sheaf-descente). -/
def envelopeSinglePullbackMap {X S : Scheme.{u}} (f : X ⟶ S)
    (N : SheafOfModules.{u} (moduleRings S.toRingedSpace)) :
    (derivedPullback f).obj ((DerivedCategory.singleFunctor _ 0).obj N) ⟶
      (DerivedCategory.singleFunctor _ 0).obj ((Scheme.Modules.tensorPullback f).obj N) :=
  (derivedPullback f).map
      (((DerivedCategory.quotientCompQhIso _).app
        ((CochainComplex.singleFunctor _ 0).obj N)).inv) ≫
    (SingleComplexBaseChange.counit f).app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj
        ((CochainComplex.singleFunctor _ 0).obj N)) ≫
    ((DerivedCategory.quotientCompQhIso
      (SheafOfModules.{u} (moduleRings X.toRingedSpace))).app
      (((Scheme.Modules.tensorPullback f).mapHomologicalComplex (.up ℤ)).obj
        ((CochainComplex.singleFunctor _ 0).obj N))).hom ≫
    (DerivedCategory.Q (C := SheafOfModules.{u} (moduleRings X.toRingedSpace))).map
      ((HomologicalComplex.singleMapHomologicalComplex
        (Scheme.Modules.tensorPullback f) (.up ℤ) 0).app N).hom

/-- The scalar action on successive derived pullback, formed using the two universal
counits and a section-normalized ordinary evaluation. No derived pullback is replaced
by ordinary pullback: the counits here are generally not invertible.
Source: the scalar transpose in the prerequisite following Stacks Tag 0CSD
(blueprint: lem-sfb-prescribed-envelope-relative-sheaf-descente). -/
def envelopeScalarAction {R A : CommRingCat.{u}} {X Z : Scheme.{u}}
    (φ : R ⟶ A) (q : Z ⟶ Spec R) (u : X ⟶ Z)
    (e : (Scheme.Modules.tensorPullback u).obj
      ((Scheme.Modules.tensorPullback q).obj (envelopeCoefficientSheaf φ)) ⟶
        SheafOfModules.unit (moduleRings X.toRingedSpace)) :
    (derivedPullback u).obj ((derivedPullback q).obj (envelopeCoefficient φ)) ⟶
      𝟙_ (schemeDerivedCategory X) :=
  (derivedPullback u).map (envelopeSinglePullbackMap q (envelopeCoefficientSheaf φ)) ≫
    envelopeSinglePullbackMap u
      ((Scheme.Modules.tensorPullback q).obj (envelopeCoefficientSheaf φ)) ≫
    (DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).map e

/-- The derived adjunction Lu^* ⊣ Ru_* is normalized by the ordinary module adjunction:
on a homotopy-category complex M, the transpose of the shared left-derived counit followed
by Q(a) is Q of the ordinary transpose of a, followed by the right-derived unit. This is
the normalization of the recorded derived base-change adjunction; it fixes the adjunction,
so no independent choice of an adjunction enters theta.
Source: Stacks Tag 079W (cohomology.tex, lemma-adjoint), as used in the transpose of the
prerequisite following Stacks Tag 0CSD
(blueprint: lem-sfb-prescribed-envelope-relative-sheaf-descente). -/
def EnvelopeDerivedAdjunctionIsNormalized {X Z : Scheme.{u}} (u : X ⟶ Z)
    (adj : derivedPullback u ⊣ schemeDerivedDirectImage u) : Prop :=
  ∀ (M : HomotopyCategory
      (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) (ComplexShape.up ℤ))
    (K : HomotopyCategory
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) (ComplexShape.up ℤ))
    (a : ((Scheme.Modules.tensorPullback u).mapHomotopyCategory
      (ComplexShape.up ℤ)).obj M ⟶ K),
    adj.homEquiv (DerivedCategory.Qh.obj M) (DerivedCategory.Qh.obj K)
        ((SingleComplexBaseChange.counit u).app M ≫ DerivedCategory.Qh.map a) =
      (DerivedCategory.Qh
        (C := SheafOfModules.{u} (moduleRings Z.toRingedSpace))).map
        (((Classical.choose
          (Scheme.Modules.exists_tensorPullbackAdjunction u)).mapHomotopyCategory
            (ComplexShape.up ℤ)).homEquiv M K a) ≫
        (RingedSpace.moduleDirectImage u.toLRSHom.toShHom).rightDerivedFunctorUnit.app K

/-- The map theta is the derived adjoint, for the normalized derived adjunction, of tensor
comparison followed by scalar action and the transpose of gamma, then the derived tensor
unitor.
Source: the displayed transpose in the prerequisite following Stacks Tag 0CSD
(blueprint: lem-sfb-prescribed-envelope-relative-sheaf-descente). -/
def envelopeTheta {R A : CommRingCat.{u}} {X Z : Scheme.{u}}
    (φ : R ⟶ A) (q : Z ⟶ Spec R) (u : X ⟶ Z)
    (e : (Scheme.Modules.tensorPullback u).obj
      ((Scheme.Modules.tensorPullback q).obj (envelopeCoefficientSheaf φ)) ⟶
        SheafOfModules.unit (moduleRings X.toRingedSpace))
    (τ : ∀ K L : schemeDerivedCategory Z,
      (derivedPullback u).obj (K ⊗ L) ⟶
        (derivedPullback u).obj K ⊗ (derivedPullback u).obj L)
    (adj : derivedPullback u ⊣ schemeDerivedDirectImage u)
    (F : schemeDerivedCategory Z) (E : schemeDerivedCategory X)
    (γ : F ⟶ (schemeDerivedDirectImage u).obj E) :
    (derivedPullback q).obj (envelopeCoefficient φ) ⊗ F ⟶
      (schemeDerivedDirectImage u).obj E :=
  adj.homEquiv _ _
    (τ _ _ ≫ (envelopeScalarAction φ q u e ⊗ₘ (adj.homEquiv _ _).symm γ) ≫ (λ_ E).hom)

/-- The ordinary evaluation is pinned by its values on all global coefficient sections.
The adjunction turns it into a map from tilde A to q_* u_* O_X. These sections generate
that associated sheaf, so this specifies the evaluation uniquely, including over zero rings.
Source: scalar action in the prerequisite following Stacks Tag 0CSD; tilde, Tag 01IB
(blueprint: lem-sfb-prescribed-envelope-relative-sheaf-descente). -/
def EnvelopeEvaluationIsScalar {R A : CommRingCat.{u}} {X Z : Scheme.{u}}
    (φ : R ⟶ A) (q : Z ⟶ Spec R) (u : X ⟶ Z) (s : X ⟶ Spec A)
    (e : (Scheme.Modules.tensorPullback u).obj
      ((Scheme.Modules.tensorPullback q).obj (envelopeCoefficientSheaf φ)) ⟶
        SheafOfModules.unit (moduleRings X.toRingedSpace)) : Prop :=
  ∀ a : A,
    (((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction q)).comp
      (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction u))).homEquiv _ _ e).val.app
        (.op ⊤)
      ((tilde.toOpen ((ModuleCat.restrictScalars φ.hom).obj (ModuleCat.of A A)) ⊤) a) =
        s.appTop ((Scheme.ΓSpecIso A).inv a)

/-- Geometric output data, with the base-changed k specified by its two projections.
The projection equations uniquely specify that comparison; they do not choose an
unconstrained map. The last equation is k_A j' = j on the prescribed ambient model.
Source: the geometric factorization in the prerequisite following Stacks Tag 0CSD
(blueprint: lem-sfb-prescribed-envelope-relative-sheaf-descente). -/
structure PrescribedEnvelopeModel {B A : CommRingCat.{u}} (φ : B ⟶ A)
    {Y : Scheme.{u}} (p : Y ⟶ Spec B) {X : Scheme.{u}}
    (j : X ⟶ pullback p (Spec.map φ)) where
  ring : CommRingCat.{u}
  fromBase : B ⟶ ring
  toA : ring ⟶ A
  factorization : fromBase ≫ toA = φ
  finiteType : fromBase.hom.FiniteType
  noetherian : IsNoetherianRing ring
  Z : Scheme.{u}
  k : Z ⟶ pullback p (Spec.map fromBase)
  closed_k : IsClosedImmersion k
  j' : X ⟶ pullback (k ≫ pullback.snd p (Spec.map fromBase)) (Spec.map toA)
  closed_j' : IsClosedImmersion j'
  comparison :
    pullback (k ≫ pullback.snd p (Spec.map fromBase)) (Spec.map toA) ⟶
      pullback p (Spec.map φ)
  comparison_fst : comparison ≫ pullback.fst p (Spec.map φ) =
    pullback.fst (k ≫ pullback.snd p (Spec.map fromBase)) (Spec.map toA) ≫
      k ≫ pullback.fst p (Spec.map fromBase)
  comparison_snd : comparison ≫ pullback.snd p (Spec.map φ) =
    pullback.snd (k ≫ pullback.snd p (Spec.map fromBase)) (Spec.map toA)
  factor_j : j' ≫ comparison = j

/-- The structure morphism q of the chosen closed envelope over the coefficient stage.
Source: prerequisite following Stacks Tag 0CSD
(blueprint: lem-sfb-prescribed-envelope-relative-sheaf-descente). -/
def PrescribedEnvelopeModel.q {B A : CommRingCat.{u}} {φ : B ⟶ A}
    {Y : Scheme.{u}} {p : Y ⟶ Spec B} {X : Scheme.{u}}
    {j : X ⟶ pullback p (Spec.map φ)} (D : PrescribedEnvelopeModel φ p j) :
    D.Z ⟶ Spec D.ring :=
  D.k ≫ pullback.snd p (Spec.map D.fromBase)

/-- The morphism u is j' followed by the coefficient projection.
Source: prerequisite following Stacks Tag 0CSD
(blueprint: lem-sfb-prescribed-envelope-relative-sheaf-descente). -/
def PrescribedEnvelopeModel.u {B A : CommRingCat.{u}} {φ : B ⟶ A}
    {Y : Scheme.{u}} {p : Y ⟶ Spec B} {X : Scheme.{u}}
    {j : X ⟶ pullback p (Spec.map φ)} (D : PrescribedEnvelopeModel φ p j) : X ⟶ D.Z :=
  D.j' ≫ pullback.fst D.q (Spec.map D.toA)

/-- Relative sheaf descente with prescribed ambient model and arbitrary coefficient maps.
The tensor comparison is fixed by its K-flat normalization; the scalar evaluation is
fixed on every coefficient section, the derived adjunction is fixed by its ordinary
normalization, and theta is the explicit derived-adjoint map above.

Source: agent-formulated prerequisite for the Kiehl assertion following Stacks Tag 0CSD,
perfect.tex, lemma-flat-proper-pseudo-coherent-direct-image-general. That paragraph does
not itself state or prove this lemma; the primary Kiehl (1972) source is WANTED.
(blueprint: lem-sfb-prescribed-envelope-relative-sheaf-descente).

Proof plan from the node:
1. Put K = Rj_* E on Y_A. Affine derived pushforward gives quasi-coherence, and
   closed-support invariance gives relative pseudo-coherence in every integer degree.
2. Use the coefficient-window proposition P(W), retaining every finite coefficient stage
   in its quantifiers. Its empty-open case uses the same stage, F = 0 and gamma = 0.
3. On affines, associated sheaves identify pushforward with restriction of scalars.
   The affine pushforward resolution lemma extends this identification to unbounded
   complexes, with no flatness assumption.
4. For an affine W = Spec R, use a finite polynomial presentation over the coefficient
   stage. The all-affine-charts relative criterion and the affine pseudo-coherence
   criterion identify a pseudo-coherent polynomial-ring complex. Apply the affine
   coefficient-window lift; the finite coefficient stage is Noetherian.
5. Sheafify its bounded finite-cohomology lift. Finite modules over a Noetherian ring
   give coherent sheaves. The affine derived tensor comparison identifies T and theta
   with the lift's derived scalar-extension map, by the scalar-times-section formula.
6. Induct on a finite affine cover. Separatedness makes the affine intersections affine;
   the two-open locality lemma combines P(U), P(V) and P(U intersection V). This gives
   P(Y), including for empty Y.
7. Apply P(Y) at the initial stage B. Take Z = Y_{B'}, k = identity and j' = j under
   the canonical base-change comparison. Composition of derived direct images
   transports gamma to Ru_* E. The lift F has bounded coherent cohomology.
8. Pull back the scalar transpose and use the A-linearity of the adjunction counit.
   It is exactly envelopeTheta, since its ordinary evaluation sends a to s-sharp(a).
   Hence its cone is the supplied quasi-coherent cone, vanishing in every degree i >= a.
   The bound is on sheaves on Z, before any derived global sections. -/
theorem prescribedEnvelope_relative_sheaf_descente
    {B A : CommRingCat.{u}} [IsNoetherianRing B] (φ : B ⟶ A)
    {Y : Scheme.{u}} (p : Y ⟶ Spec B) [IsSeparated p] [LocallyOfFiniteType p]
    [QuasiCompact p] {X : Scheme.{u}} (j : X ⟶ pullback p (Spec.map φ))
    [IsClosedImmersion j] (E : schemeDerivedCategory X)
    (hE : schemeDerivedQCohProperty X E)
    (hrel : Scheme.IsPseudoCoherentRelativeTo
      (j ≫ pullback.snd p (Spec.map φ)) E) (a : ℤ) :
    ∃ D : PrescribedEnvelopeModel φ p j,
      ∃ F : schemeDerivedCategory D.Z,
      (∀ i : ℤ, RingedSpace.IsCoherent D.Z.toRingedSpace
        ((DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (moduleRings D.Z.toRingedSpace)) i).obj F)) ∧
      (∃ l r : ℤ, ∀ i : ℤ, i < l ∨ r < i → IsZero
        ((DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (moduleRings D.Z.toRingedSpace)) i).obj F)) ∧
      ∃ γ : F ⟶ (schemeDerivedDirectImage D.u).obj E,
      ∃ e : (Scheme.Modules.tensorPullback D.u).obj
        ((Scheme.Modules.tensorPullback D.q).obj (envelopeCoefficientSheaf D.toA)) ⟶
          SheafOfModules.unit (moduleRings X.toRingedSpace),
      EnvelopeEvaluationIsScalar D.toA D.q D.u
        (D.j' ≫ pullback.snd D.q (Spec.map D.toA)) e ∧
      ∃ τ : ∀ K L : schemeDerivedCategory D.Z,
        (derivedPullback D.u).obj (K ⊗ L) ⟶
          (derivedPullback D.u).obj K ⊗ (derivedPullback D.u).obj L,
      IsCanonicalPullbackTensorComparison D.u τ ∧
      ∃ adj : derivedPullback D.u ⊣ schemeDerivedDirectImage D.u,
      EnvelopeDerivedAdjunctionIsNormalized D.u adj ∧
      ∃ (C : schemeDerivedCategory D.Z)
        (v : (schemeDerivedDirectImage D.u).obj E ⟶ C)
        (w : C ⟶ ((derivedPullback D.q).obj (envelopeCoefficient D.toA) ⊗ F)⟦(1 : ℤ)⟧),
      Triangle.mk (envelopeTheta D.toA D.q D.u e τ adj F E γ) v w ∈
        distTriang (schemeDerivedCategory D.Z) ∧
      schemeDerivedQCohProperty D.Z C ∧
      ∀ i : ℤ, a ≤ i → IsZero ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings D.Z.toRingedSpace)) i).obj C) := by
  sorry

end
end AlgebraicGeometry
