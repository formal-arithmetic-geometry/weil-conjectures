/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q61
-/
module

public import Sheaf.Paper.PbcActualStrictPullback
public import Sheaf.Paper.CompletedTowerPullback
public import Sheaf.Paper.CompletedPullbackReduction
public import Sheaf.CategoryTheory.LocalizedModuleExactIndependent
public import Sheaf.Paper.CompletedRlimFunctor
public import Sheaf.Paper.ConstantCompletionEquivalence
public import Sheaf.AlgebraicGeometry.ProEtaleConstantRingMap
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctoriality
public import Mathlib.CategoryTheory.Adjunction.Mates
import Sheaf.Algebra.Homology.DiagramKFlatReplacements
import Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Sheaf.Algebra.Homology.KFlat
import Sheaf.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf

public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import Sheaf.AlgebraicGeometry.ProEtaleInverseImage
import Sheaf.CategoryTheory.LocalizedModuleExactForSystems
import Sheaf.Paper.AdicCoefficientDatum
import Sheaf.Paper.LocalizeRingedSiteMorphismGeneral
import Sheaf.Paper.PbcQbarCompletedPullback
/-!
# Counit-normalized transport of adic pullback presentations

Source: blueprint main-20261015, sec-six-functors-basics/sk-prop-sf-cbc,
lem-cbc-completed-extension-zero-comparison.proof.md; Stacks Tags 05S7 and 03DI.
(blueprint: lem-cbc-adic-pullback-presentation-transport).

The coefficient uniqueness statement first identifies both presentations with the published
coefficient map. The subsequent statements use these identifications to write both universal
pairs over the same ordinary functor. No invertibility of the completed coefficient map is used.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

variable {X Y : Scheme.{u}} (g : X ⟶ Y) {A : Type (u + 1)} [CommRing A]
  (d : AdicCoefficientDatum A)

/-- Projection-normalized coefficient presentations are the published coefficient map;
finite constant-section maps commute with every quotient transition, including identities.
Source: blueprint CBC presentation argument, Step 1; Stacks 05S7
(blueprint: lem-cbc-adic-pullback-presentation-transport).
Proof: completion is the limit of the finite coefficient sheaves, so its projections
are jointly monic. The prescribed components are those of completedCoefficientMap.
For the quotient square, take adjuncts: both maps on the constant presheaf send a scalar
to its quotient constant section. Sheafification and the inverse-image adjunction identify
them. This also applies to the empty scheme and the zero quotient ring. -/
theorem adic_pullback_coefficient_presentations
    (c₁ c₂ : (proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj
      (pbcAdicCompletion Y d) ⟶ pbcAdicCompletion X d)
    (h₁ : ∀ n : ℕ, c₁ ≫ pbcAdicProjection X d n = completedCoefficientComponent g d n)
    (h₂ : ∀ n : ℕ, c₂ ≫ pbcAdicProjection X d n = completedCoefficientComponent g d n) :
    c₁ = c₂ ∧ c₁ = completedCoefficientMap g d ∧
      ∀ (b a : ℕ) (hab : a ≤ b),
        completedFiniteCoefficientMap g d b ≫ pbcAdicQuotient X d b a hab =
          (proEtaleSheafInverseImage g CommRingCat.{u + 1}).map
            (pbcAdicQuotient Y d b a hab) ≫ completedFiniteCoefficientMap g d a := by
  sorry

/-- Module pullback for a specified coefficient presentation, using the existing sheaf tensor.
Source: blueprint CBC presentation argument, Step 2
(blueprint: lem-cbc-adic-pullback-presentation-transport). -/
def adicPresentationPullback
    (c : (proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj
      (pbcAdicCompletion Y d) ⟶ pbcAdicCompletion X d) :=
  proEtaleModuleInverseImage g (pbcAdicCompletion Y d) ⋙ reductionChange X c

/-- The identity on balanced tensors is equality transport along coefficient uniqueness.
Its inverse is the same identity formula. Source: blueprint CBC argument, Step 2
(blueprint: lem-cbc-adic-pullback-presentation-transport). -/
def adicPresentationIdentity
    (c₁ c₂ : (proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj
      (pbcAdicCompletion Y d) ⟶ pbcAdicCompletion X d)
    (h₁ : ∀ n : ℕ, c₁ ≫ pbcAdicProjection X d n = completedCoefficientComponent g d n)
    (h₂ : ∀ n : ℕ, c₂ ≫ pbcAdicProjection X d n = completedCoefficientComponent g d n) :
    adicPresentationPullback g d c₁ ≅ adicPresentationPullback g d c₂ :=
  eqToIso (congrArg (adicPresentationPullback g d)
    (adic_pullback_coefficient_presentations g d c₁ c₂ h₁ h₂).1)

/-- Proof that the published ordinary pair is a universal left-derived pair.
Source: blueprint CBC argument, Step 3; Stacks 05S7
(blueprint: lem-cbc-adic-pullback-presentation-transport).
Proof: completedOrdinaryPullback_exists constructs this very counited pair by the
one-object K-flat resolving class. Its first property is precisely the assertion. -/
theorem adicPresentationOrdinaryUniversal_proof :
    (completedOrdinaryPullback g d).IsLeftDerivedFunctor
      (completedOrdinaryPullbackCounit g d)
      (HomotopyCategory.quasiIso (pbcModules Y (pbcAdicCompletion Y d)) (.up ℤ)) := by
  sorry

/-- The published ordinary pair carries its universal left-derived structure.
Source: blueprint CBC argument, Step 3; Stacks 05S7
(blueprint: lem-cbc-adic-pullback-presentation-transport). -/
instance adicPresentationOrdinaryUniversal :
    (completedOrdinaryPullback g d).IsLeftDerivedFunctor
      (completedOrdinaryPullbackCounit g d)
      (HomotopyCategory.quasiIso (pbcModules Y (pbcAdicCompletion Y d)) (.up ℤ)) :=
  adicPresentationOrdinaryUniversal_proof g d

/-- Proof that the published strict-tower pair is a universal left-derived pair.
Source: blueprint CBC argument, Step 3; Stacks 05S7
(blueprint: lem-cbc-adic-pullback-presentation-transport).
Proof: completedTowerPullback_exists constructs this pair by strict diagram K-flat
replacements. Its first property is precisely the universal derived property. -/
theorem adicPresentationTowerUniversal_proof :
    (completedTowerPullback g d).IsLeftDerivedFunctor
      (completedTowerPullbackCounit g d)
      (HomotopyCategory.quasiIso (pbcTowers Y (pbcAdicCompletion Y d)) (.up ℤ)) := by
  sorry

/-- The published strict-tower pair carries its universal left-derived structure.
Source: blueprint CBC argument, Step 3; Stacks 05S7
(blueprint: lem-cbc-adic-pullback-presentation-transport). -/
instance adicPresentationTowerUniversal :
    (completedTowerPullback g d).IsLeftDerivedFunctor
      (completedTowerPullbackCounit g d)
      (HomotopyCategory.quasiIso (pbcTowers Y (pbcAdicCompletion Y d)) (.up ℤ)) :=
  adicPresentationTowerUniversal_proof g d

section Ordinary
variable (L : DerivedCategory (pbcModules Y (pbcAdicCompletion Y d)) ⥤
    DerivedCategory (pbcModules X (pbcAdicCompletion X d)))
  (ε : DerivedCategory.Qh ⋙ L ⟶
    (completedModulePullback g d).mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
  [L.IsLeftDerivedFunctor ε
    (HomotopyCategory.quasiIso (pbcModules Y (pbcAdicCompletion Y d)) (.up ℤ))]

/-- The universal counit fixes the comparison to the published ordinary pair.
Source: blueprint CBC argument, Step 3; Stacks 05S7
(blueprint: lem-cbc-adic-pullback-presentation-transport). -/
def adicPresentationOrdinaryIso : L ≅ completedOrdinaryPullback g d :=
  Functor.leftDerivedUnique (completedOrdinaryPullback g d) L ε
    (completedOrdinaryPullbackCounit g d)
    (HomotopyCategory.quasiIso (pbcModules Y (pbcAdicCompletion Y d)) (.up ℤ))
end Ordinary

section Tower
variable (L : DerivedCategory (pbcTowers Y (pbcAdicCompletion Y d)) ⥤
    DerivedCategory (pbcTowers X (pbcAdicCompletion X d)))
  (ε : DerivedCategory.Qh ⋙ L ⟶
    (completedTowerModulePullback g d).mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
  [L.IsLeftDerivedFunctor ε
    (HomotopyCategory.quasiIso (pbcTowers Y (pbcAdicCompletion Y d)) (.up ℤ))]

/-- The universal counit fixes the comparison to the published strict-tower pair.
Source: blueprint CBC argument, Step 3; Stacks 05S7
(blueprint: lem-cbc-adic-pullback-presentation-transport). -/
def adicPresentationTowerIso : L ≅ completedTowerPullback g d :=
  Functor.leftDerivedUnique (completedTowerPullback g d) L ε
    (completedTowerPullbackCounit g d)
    (HomotopyCategory.quasiIso (pbcTowers Y (pbcAdicCompletion Y d)) (.up ℤ))
end Tower

section Pairs
variable
  (L₁ L₂ : DerivedCategory (pbcModules Y (pbcAdicCompletion Y d)) ⥤
    DerivedCategory (pbcModules X (pbcAdicCompletion X d)))
  (ε₁ : DerivedCategory.Qh ⋙ L₁ ⟶
    (completedModulePullback g d).mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
  (ε₂ : DerivedCategory.Qh ⋙ L₂ ⟶
    (completedModulePullback g d).mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
  [L₁.IsLeftDerivedFunctor ε₁
    (HomotopyCategory.quasiIso (pbcModules Y (pbcAdicCompletion Y d)) (.up ℤ))]
  [L₂.IsLeftDerivedFunctor ε₂
    (HomotopyCategory.quasiIso (pbcModules Y (pbcAdicCompletion Y d)) (.up ℤ))]
  (T₁ T₂ : DerivedCategory (pbcTowers Y (pbcAdicCompletion Y d)) ⥤
    DerivedCategory (pbcTowers X (pbcAdicCompletion X d)))
  (τ₁ : DerivedCategory.Qh ⋙ T₁ ⟶
    (completedTowerModulePullback g d).mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
  (τ₂ : DerivedCategory.Qh ⋙ T₂ ⟶
    (completedTowerModulePullback g d).mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
  [T₁.IsLeftDerivedFunctor τ₁
    (HomotopyCategory.quasiIso (pbcTowers Y (pbcAdicCompletion Y d)) (.up ℤ))]
  [T₂.IsLeftDerivedFunctor τ₂
    (HomotopyCategory.quasiIso (pbcTowers Y (pbcAdicCompletion Y d)) (.up ℤ))]

/-- Both derived comparisons are uniquely determined by their displayed counit equations.
The coefficients have first been identified by adic_pullback_coefficient_presentations,
so the balanced-tensor comparison is the identity in these common coordinates.
Source: blueprint CBC argument, Step 3; Stacks 05S7
(blueprint: lem-cbc-adic-pullback-presentation-transport).
Proof: use the universal left-derived lift with the first counit and the second
universal pair, and repeat in reverse. Uniqueness makes the two composites identities.
The same proof in the abelian strict-tower category gives the second assertion. -/
theorem adic_pullback_presentation_transport :
    (∃! e : L₁ ≅ L₂, Functor.whiskerLeft DerivedCategory.Qh e.hom ≫ ε₂ = ε₁) ∧
    (∃! e : T₁ ≅ T₂, Functor.whiskerLeft DerivedCategory.Qh e.hom ≫ τ₂ = τ₁) := by
  sorry

end Pairs

section NormalizedPair
variable
  (L : DerivedCategory (pbcModules Y (pbcAdicCompletion Y d)) ⥤
    DerivedCategory (pbcModules X (pbcAdicCompletion X d)))
  (ε : DerivedCategory.Qh ⋙ L ⟶
    (completedModulePullback g d).mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
  [hL : L.IsLeftDerivedFunctor ε
    (HomotopyCategory.quasiIso (pbcModules Y (pbcAdicCompletion Y d)) (.up ℤ))]
  (T : DerivedCategory (pbcTowers Y (pbcAdicCompletion Y d)) ⥤
    DerivedCategory (pbcTowers X (pbcAdicCompletion X d)))
  (τ : DerivedCategory.Qh ⋙ T ⟶
    (completedTowerModulePullback g d).mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
  [hT : T.IsLeftDerivedFunctor τ
    (HomotopyCategory.quasiIso (pbcTowers Y (pbcAdicCompletion Y d)) (.up ℤ))]

/-- Constant-tower comparison for any universal pair, transported through the unique
counit-preserving identifications with the published pairs. Source: CBC Step 4; Stacks 05S7
(blueprint: lem-cbc-adic-pullback-presentation-transport). -/
def adicPresentationConstantIso :
    L ⋙ completedDerivedConstant d X ≅ completedDerivedConstant d Y ⋙ T :=
  Functor.isoWhiskerRight (adicPresentationOrdinaryIso g d L ε)
      (completedDerivedConstant d X) ≪≫
    completedPullbackConstantIso g d ≪≫
    Functor.isoWhiskerLeft (completedDerivedConstant d Y)
      (adicPresentationTowerIso g d T τ).symm

/-- The generalized representative normalization retains both universal counits.
Source: CBC Step 4; Stacks 05S7
(blueprint: lem-cbc-adic-pullback-presentation-transport). -/
def HasAdicPresentationConstantNormalization
    (b : L ⋙ completedDerivedConstant d X ≅ completedDerivedConstant d Y ⋙ T) : Prop :=
  ∀ P : CochainComplex (pbcModules Y (pbcAdicCompletion Y d)) ℤ,
    CochainComplex.IsKFlatIndependentCoefficients (R := pbcAdicCompletion Y d) P →
    (completedDerivedConstant d X).map
        (Functor.leftDerivedCounitOnComplex (completedModulePullback g d) L ε P) ≫
      ((completedTowerConstant d X).mapDerivedCategoryFactors).hom.app
        (((completedModulePullback g d).mapHomologicalComplex (.up ℤ)).obj P) ≫
      DerivedCategory.Q.map (eqToHom (completedPullbackConstantComplex_eq g d P)) =
    b.hom.app (DerivedCategory.Q.obj P) ≫
      T.map (((completedTowerConstant d Y).mapDerivedCategoryFactors).hom.app P) ≫
      Functor.leftDerivedCounitOnComplex (completedTowerModulePullback g d) T τ
        (((completedTowerConstant d Y).mapHomologicalComplex (.up ℤ)).obj P)

/-- The transported constant comparison is the unique counit-normalized one.
Source: CBC Step 4; Stacks 05S7
(blueprint: lem-cbc-adic-pullback-presentation-transport).
Proof: substitute the two counit-preserving universal comparisons in the published
constant comparison's normalization. This gives the displayed representative equation.
Both counits are invertible on constant K-flat representatives. Diagram resolutions of
arrows give naturality; resolving roofs and then inverting quasi-isomorphisms gives
uniqueness on the derived category. -/
theorem adicPresentationConstantIso_normalized :
    HasAdicPresentationConstantNormalization g d L ε T τ
      (adicPresentationConstantIso g d L ε T τ) ∧
    ∀ b : L ⋙ completedDerivedConstant d X ≅ completedDerivedConstant d Y ⋙ T,
      HasAdicPresentationConstantNormalization g d L ε T τ b →
        b = adicPresentationConstantIso g d L ε T τ := by
  sorry

/-- Evaluation and levelwise pullback give the identical complex.
Source: CBC Step 4; Stacks 015F
(blueprint: lem-cbc-adic-pullback-presentation-transport).
Proof: in every complex degree both sides are the pullback of the same tower level,
with the same pulled differential. Componentwise extensionality gives the equality. -/
theorem adicPresentationEvaluationComplex_eq (n : ℕ)
    (P : CochainComplex (pbcTowers Y (pbcAdicCompletion Y d)) ℤ) :
    (((CategoryTheory.evaluation ℕᵒᵖ (pbcModules X (pbcAdicCompletion X d))).obj
      (op n)).mapHomologicalComplex (.up ℤ)).obj
        (((completedTowerModulePullback g d).mapHomologicalComplex (.up ℤ)).obj P) =
    ((completedModulePullback g d).mapHomologicalComplex (.up ℤ)).obj
      ((((CategoryTheory.evaluation ℕᵒᵖ (pbcModules Y (pbcAdicCompletion Y d))).obj
        (op n)).mapHomologicalComplex (.up ℤ)).obj P) := by
  sorry

/-- Evaluation comparison normalized by the actual counits on strict K-flat diagrams.
Source: CBC Step 4; Stacks 05S7 and 015F
(blueprint: lem-cbc-adic-pullback-presentation-transport). -/
def HasAdicPresentationEvaluationNormalization (n : ℕ)
    (v : T ⋙ pbcTowerEvaluation X (pbcAdicCompletion X d) n ≅
      pbcTowerEvaluation Y (pbcAdicCompletion Y d) n ⋙ L) : Prop :=
  ∀ P : CochainComplex (pbcTowers Y (pbcAdicCompletion Y d)) ℤ,
    (∀ k : ℕ, CochainComplex.IsKFlatIndependentCoefficients (R := pbcAdicCompletion Y d)
      ((((CategoryTheory.evaluation ℕᵒᵖ (pbcModules Y (pbcAdicCompletion Y d))).obj
        (op k)).mapHomologicalComplex (.up ℤ)).obj P)) →
    (pbcTowerEvaluation X (pbcAdicCompletion X d) n).map
        (Functor.leftDerivedCounitOnComplex (completedTowerModulePullback g d) T τ P) ≫
      ((CategoryTheory.evaluation ℕᵒᵖ (pbcModules X (pbcAdicCompletion X d))).obj
        (op n)).mapDerivedCategoryFactors.hom.app
          (((completedTowerModulePullback g d).mapHomologicalComplex (.up ℤ)).obj P) ≫
      DerivedCategory.Q.map (eqToHom (adicPresentationEvaluationComplex_eq g d n P)) =
    v.hom.app (DerivedCategory.Q.obj P) ≫
      L.map (((CategoryTheory.evaluation ℕᵒᵖ (pbcModules Y (pbcAdicCompletion Y d))).obj
        (op n)).mapDerivedCategoryFactors.hom.app P) ≫
      Functor.leftDerivedCounitOnComplex (completedModulePullback g d) L ε
        ((((CategoryTheory.evaluation ℕᵒᵖ (pbcModules Y (pbcAdicCompletion Y d))).obj
          (op n)).mapHomologicalComplex (.up ℤ)).obj P)

include hL hT in
/-- Evaluation commutes with arbitrary universal pullback pairs in one normalized way.
Source: CBC Step 4; Stacks 05S7 and 015F
(blueprint: lem-cbc-adic-pullback-presentation-transport).
Proof: evaluate a strict objectwise K-flat resolution. Exact evaluation and both
counits identify the two sides with the identical evaluated pullback complex. Resolve
arrows simultaneously to get naturality, then descend roofs through localization.
The invertible representative counits force uniqueness and invertibility. -/
theorem adicPresentationEvaluationIso_exists (n : ℕ) :
    ∃! v : T ⋙ pbcTowerEvaluation X (pbcAdicCompletion X d) n ≅
      pbcTowerEvaluation Y (pbcAdicCompletion Y d) n ⋙ L,
      HasAdicPresentationEvaluationNormalization g d L ε T τ n v := by
  sorry

/-- The unique evaluation comparison, including all maps of strict diagrams.
Source: CBC Step 4; Stacks 015F
(blueprint: lem-cbc-adic-pullback-presentation-transport). -/
def adicPresentationEvaluationIso (n : ℕ) :
    T ⋙ pbcTowerEvaluation X (pbcAdicCompletion X d) n ≅
      pbcTowerEvaluation Y (pbcAdicCompletion Y d) n ⋙ L :=
  (adicPresentationEvaluationIso_exists g d L ε T τ n).exists.choose

/-- Finite-reduction comparison for any universal tower pair. The published comparison
is uniquely fixed by its tensor generators and actual resolving counits, rather than
chosen from the earlier bare Nonempty interface. Source: CBC Step 5; Stacks 099L
(blueprint: lem-cbc-adic-pullback-presentation-transport). -/
def adicPresentationFiniteIso (n : ℕ) :
    completedReductionTower Y d ⋙ T ⋙ pbcTowerEvaluation X (pbcAdicCompletion X d) n ≅
      completedReductionFiniteTarget g d n ⋙
        pbcDerivedRestrict (completedReductionProjection X d n) :=
  Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft (completedReductionTower Y d)
        (adicPresentationTowerIso g d T τ))
      (pbcTowerEvaluation X (pbcAdicCompletion X d) n) ≪≫
    completedReductionFiniteEvaluation g d n
end NormalizedPair

section CompletionTransport
/-- The strict reduction completion computed from a chosen tower presentation.
Source: blueprint CBC argument, Steps 6--8; Stacks 08TC
(blueprint: lem-cbc-adic-pullback-presentation-transport). -/
def adicPresentationCompletion
    (T : DerivedCategory (pbcTowers Y (pbcAdicCompletion Y d)) ⥤
      DerivedCategory (pbcTowers X (pbcAdicCompletion X d)))
    (K : DerivedCategory (pbcModules Y (pbcAdicCompletion Y d))) :
    DerivedCategory (pbcModules X (pbcAdicCompletion X d)) :=
  (completedTowerRlim d X).obj
    (T.obj ((completedReductionTower Y d).obj K))

/-- The quotient augmentation unit for a chosen presentation and its constant-tower
comparison. The augmentation is the canonical strict reduction unit, so every quotient
transition is retained. Source: blueprint CBC argument, Steps 6 and 8; Stacks 08TC
(blueprint: lem-cbc-adic-pullback-presentation-transport). -/
def adicPresentationUnit
    (L : DerivedCategory (pbcModules Y (pbcAdicCompletion Y d)) ⥤
      DerivedCategory (pbcModules X (pbcAdicCompletion X d)))
    (T : DerivedCategory (pbcTowers Y (pbcAdicCompletion Y d)) ⥤
      DerivedCategory (pbcTowers X (pbcAdicCompletion X d)))
    (b : L ⋙ completedDerivedConstant d X ≅
      completedDerivedConstant d Y ⋙ T)
    (K : DerivedCategory (pbcModules Y (pbcAdicCompletion Y d))) :
    L.obj K ⟶ adicPresentationCompletion d T K :=
  (completedConstantRlimUnit d X).app (L.obj K) ≫
    (completedTowerRlim d X).map
      (b.hom.app K ≫ T.map ((completedReductionTowerUnit d Y).app K))

/-- The natural comparison of the two completed strict presentations. It is obtained by
applying the functorial derived inverse limit to the strict-tower comparison. Source:
blueprint CBC argument, Steps 3 and 7; Stacks 08TC
(blueprint: lem-cbc-adic-pullback-presentation-transport). -/
def adicPresentationLimitComparison
    (T₁ T₂ : DerivedCategory (pbcTowers Y (pbcAdicCompletion Y d)) ⥤
      DerivedCategory (pbcTowers X (pbcAdicCompletion X d)))
    (e : T₁ ≅ T₂) (K : DerivedCategory (pbcModules Y (pbcAdicCompletion Y d))) :
    adicPresentationCompletion d T₁ K ≅ adicPresentationCompletion d T₂ K :=
  (completedTowerRlim d X).mapIso
    ((Functor.isoWhiskerLeft (completedReductionTower Y d) e).app K)

end CompletionTransport

section TransportSquares
variable
  (L₁ L₂ : DerivedCategory (pbcModules Y (pbcAdicCompletion Y d)) ⥤
    DerivedCategory (pbcModules X (pbcAdicCompletion X d)))
  (ε₁ : DerivedCategory.Qh ⋙ L₁ ⟶
    (completedModulePullback g d).mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
  (ε₂ : DerivedCategory.Qh ⋙ L₂ ⟶
    (completedModulePullback g d).mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
  [L₁.IsLeftDerivedFunctor ε₁
    (HomotopyCategory.quasiIso (pbcModules Y (pbcAdicCompletion Y d)) (.up ℤ))]
  [L₂.IsLeftDerivedFunctor ε₂
    (HomotopyCategory.quasiIso (pbcModules Y (pbcAdicCompletion Y d)) (.up ℤ))]
  (T₁ T₂ : DerivedCategory (pbcTowers Y (pbcAdicCompletion Y d)) ⥤
    DerivedCategory (pbcTowers X (pbcAdicCompletion X d)))
  (τ₁ : DerivedCategory.Qh ⋙ T₁ ⟶
    (completedTowerModulePullback g d).mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
  (τ₂ : DerivedCategory.Qh ⋙ T₂ ⟶
    (completedTowerModulePullback g d).mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
  [T₁.IsLeftDerivedFunctor τ₁
    (HomotopyCategory.quasiIso (pbcTowers Y (pbcAdicCompletion Y d)) (.up ℤ))]
  [T₂.IsLeftDerivedFunctor τ₂
    (HomotopyCategory.quasiIso (pbcTowers Y (pbcAdicCompletion Y d)) (.up ℤ))]
  (e : L₁ ≅ L₂) (et : T₁ ≅ T₂)
  (hε : Functor.whiskerLeft DerivedCategory.Qh e.hom ≫ ε₂ = ε₁)
  (hτ : Functor.whiskerLeft DerivedCategory.Qh et.hom ≫ τ₂ = τ₁)

include hε hτ in
/-- The unique presentation comparisons respect both constant towers and evaluation.
These squares are conclusions of counit normalization. Source: CBC Step 4; Stacks 05S7
(blueprint: lem-cbc-adic-pullback-presentation-transport).
Proof: on objectwise K-flat resolutions insert the two displayed counit equations.
Both paths become the identical constant or evaluated tensor map. The normalization
of each comparison and uniqueness after localization give the two squares. -/
theorem adicPresentationComparison_squares :
    Functor.whiskerRight e.hom (completedDerivedConstant d X) ≫
        (adicPresentationConstantIso g d L₂ ε₂ T₂ τ₂).hom =
      (adicPresentationConstantIso g d L₁ ε₁ T₁ τ₁).hom ≫
        Functor.whiskerLeft (completedDerivedConstant d Y) et.hom ∧
    ∀ n : ℕ,
      Functor.whiskerRight et.hom (pbcTowerEvaluation X (pbcAdicCompletion X d) n) ≫
          (adicPresentationEvaluationIso g d L₂ ε₂ T₂ τ₂ n).hom =
        (adicPresentationEvaluationIso g d L₁ ε₁ T₁ τ₁ n).hom ≫
          Functor.whiskerLeft (pbcTowerEvaluation Y (pbcAdicCompletion Y d) n) e.hom := by
  sorry

include hτ in
/-- Every finite reduction comparison is unchanged by the unique presentation transport.
Source: CBC Step 5; Stacks 099L
(blueprint: lem-cbc-adic-pullback-presentation-transport).
Proof: uniqueness of the universal tower comparison makes its composites to the
published pair equal. Whisker by strict reduction and exact evaluation, and compose
with the published generator-normalized finite comparison. -/
theorem adicPresentationFiniteIso_transport (n : ℕ) :
    Functor.whiskerRight
        (Functor.whiskerLeft (completedReductionTower Y d) et.hom)
        (pbcTowerEvaluation X (pbcAdicCompletion X d) n) ≫
      (adicPresentationFiniteIso g d T₂ τ₂ n).hom =
        (adicPresentationFiniteIso g d T₁ τ₁ n).hom := by
  sorry

/-- Finite comparisons retain every quotient arrow, including equal indices.
Source: CBC Step 5; Stacks 099L
(blueprint: lem-cbc-adic-pullback-presentation-transport).
Proof: on strict resolutions the ordinary finite comparison sends each pure tensor
to its quotient class. Quotienting either before or after the comparison gives the
same tensor. The normalized target transition is the descent of that very quotient
map. Naturality of the universal tower comparison transports this square to T₁.
The restriction-composition comparison is identity on underlying sections. -/
theorem adicPresentationFiniteIso_transition
    (K : DerivedCategory (pbcModules Y (pbcAdicCompletion Y d)))
    (a b : ℕ) (h : a ≤ b) :
    (adicPresentationFiniteIso g d T₁ τ₁ b).hom.app K ≫
        (pbcDerivedRestrict (completedReductionProjection X d b)).map
          ((completedReductionTargetTransition g d a b h).app K) ≫
        (pbcDerivedRestrictComp (completedReductionProjection X d b)
          (reductionCoefficientMap X d b a h) (completedReductionProjection X d a)
          (completedReductionProjection_comp X d b a h)).hom.app
            ((completedReductionFiniteTarget g d a).obj K) =
      (pbcTowerTransition X (pbcAdicCompletion X d) b a h).app
          (T₁.obj ((completedReductionTower Y d).obj K)) ≫
        (adicPresentationFiniteIso g d T₁ τ₁ a).hom.app K := by
  sorry

include hε hτ in
/-- Completion units commute with the unique presentation comparisons, using the
counit-normalized constant comparisons; no compatibility square is assumed.
Source: CBC Steps 6--8; Stacks 05S7 and 08TC
(blueprint: lem-cbc-adic-pullback-presentation-transport).
Proof: the constant square follows from adicPresentationComparison_squares. Apply
naturality of et to the canonical strict reduction augmentation, then functorial
Rlim. Naturality of the constant/Rlim unit moves e through the limit, giving exactly
the displayed equality. Strict quotient transitions are retained before taking Rlim. -/
theorem adicPresentationCompletion_transport :
    ∀ K : DerivedCategory (pbcModules Y (pbcAdicCompletion Y d)),
      adicPresentationUnit d L₁ T₁ (adicPresentationConstantIso g d L₁ ε₁ T₁ τ₁) K ≫
          (adicPresentationLimitComparison d T₁ T₂ et K).hom =
        e.hom.app K ≫
          adicPresentationUnit d L₂ T₂ (adicPresentationConstantIso g d L₂ ε₂ T₂ τ₂) K := by
  sorry
end TransportSquares

section OpenMateTransport
variable (U : Y.ProEt) [hU : IsOpenImmersion U.hom] (n : ℕ)

/-- Finite pullback on the cartesian open square in slice-site coordinates: extend
from U, apply the finite tensor pullback, and restrict to g⁻¹U. This is the canonical
local inverse image; the localized comparison below retains its open counit.
Source: CBC Step 9; Stacks 04J0, 03DI, 09AE
(blueprint: lem-cbc-adic-pullback-presentation-transport). -/
def adicPresentationLocalizedFinitePull :=
  SheafOfModules.localizedModuleExtension (reductionCoefficient Y d n) U ⋙
    completedReductionFiniteModules g d n ⋙
      SheafOfModules.localizedModuleRestriction (reductionCoefficient X d n)
        ((proEtaleBaseChange g).obj U)

/-- The actual restriction/pullback comparison on the cartesian open square. Its
components are finite pullback of the sheafified open counit, followed by restriction.
Source: CBC Step 9; Stacks 04J0 and 03DI
(blueprint: lem-cbc-adic-pullback-presentation-transport). -/
def adicPresentationLocalizedComparison :
    SheafOfModules.localizedModuleRestriction (reductionCoefficient Y d n) U ⋙
        adicPresentationLocalizedFinitePull g d U n ⟶
      completedReductionFiniteModules g d n ⋙
        SheafOfModules.localizedModuleRestriction (reductionCoefficient X d n)
          ((proEtaleBaseChange g).obj U) :=
  (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight
      (SheafOfModules.localizedModuleAdjunctionIndependent
        (reductionCoefficient Y d n) U).counit _ ≫
    (Functor.leftUnitor _).hom

include hU in
/-- The finite localized comparison is invertible, including the empty open.
Source: CBC Step 9; Stacks 04J0 and 09AE
(blueprint: lem-cbc-adic-pullback-presentation-transport).
Proof: identify the open pro-etale site with its slice by weaklyEtale_localization.
An inverse-image test object over g⁻¹U has only the summands factoring through U.
The sheafified open counit is identity on those summands; its finite tensor pullback
and restriction therefore give inverse identity-on-generator maps. This is precisely
the restricted coefficient map and localized tensor comparison of 04J0. -/
theorem adicPresentationLocalizedComparison_isIso :
    IsIso (adicPresentationLocalizedComparison g d U n) := by
  sorry

/-- The inverse open mate uses the actual sheafified presheaf extension and its
uniquely generator-normalized adjunctions, with the canonical finite localized map.
Source: CBC Steps 9--10; Stacks 03DI and 04J0
(blueprint: lem-cbc-adic-pullback-presentation-transport). -/
def adicPresentationInverseMate :=
  (mateEquiv
    (SheafOfModules.localizedModuleAdjunctionIndependent (reductionCoefficient Y d n) U)
    (SheafOfModules.localizedModuleAdjunctionIndependent (reductionCoefficient X d n)
      ((proEtaleBaseChange g).obj U))).symm
    (TwoSquare.mk _ _ _ _ (adicPresentationLocalizedComparison g d U n))

/-- The specified inverse mate is the finite pullback followed by the target open
counit, since the localized pullback was constructed by extension and restriction.
Source: CBC Step 10; Stacks 03DI
(blueprint: lem-cbc-adic-pullback-presentation-transport).
Proof: expand the inverse-mate formula. Naturality moves the source unit across
finite pullback, and the source triangle identity cancels it against the localized
comparison's source counit. The remaining factor is the displayed target counit. -/
theorem adicPresentationInverseMate_counit :
    (adicPresentationInverseMate g d U n).natTrans =
      (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft
          (SheafOfModules.localizedModuleExtension (reductionCoefficient Y d n) U ⋙
            completedReductionFiniteModules g d n)
          (SheafOfModules.localizedModuleAdjunctionIndependent (reductionCoefficient X d n)
            ((proEtaleBaseChange g).obj U)).counit ≫
        (Functor.rightUnitor _).hom := by
  sorry

include hU in
/-- Both finite open mates are determined by the same localized comparison, with
j_! definitionally the sheafified extensionByZeroPresheaf on each slice. The square
is the pullback of U.hom along g, and the finite functor is the published tensor pullback.
Source: CBC Steps 9--10; Stacks 03DI, 03DJ and 04J0
(blueprint: lem-cbc-adic-pullback-presentation-transport).
Proof: Step 1 fixes the completed ring map and all finite maps. Step 5 retains their
quotient comparisons. The localized finite map is therefore the same specified
adicPresentationLocalizedComparison. The normalized open units insert summand
generators and the counits evaluate them. Substitute these identical three factors
into the inverse-mate formula to obtain equality with the stated canonical mate. -/
theorem adicPresentationInverseMate_eq
    (m₁ m₂ : TwoSquare (adicPresentationLocalizedFinitePull g d U n)
      (SheafOfModules.localizedModuleExtension (reductionCoefficient Y d n) U)
      (SheafOfModules.localizedModuleExtension (reductionCoefficient X d n)
        ((proEtaleBaseChange g).obj U)) (completedReductionFiniteModules g d n))
    (h₁ : mateEquiv
      (SheafOfModules.localizedModuleAdjunctionIndependent (reductionCoefficient Y d n) U)
      (SheafOfModules.localizedModuleAdjunctionIndependent (reductionCoefficient X d n)
        ((proEtaleBaseChange g).obj U)) m₁ =
          TwoSquare.mk _ _ _ _ (adicPresentationLocalizedComparison g d U n))
    (h₂ : mateEquiv
      (SheafOfModules.localizedModuleAdjunctionIndependent (reductionCoefficient Y d n) U)
      (SheafOfModules.localizedModuleAdjunctionIndependent (reductionCoefficient X d n)
        ((proEtaleBaseChange g).obj U)) m₂ =
          TwoSquare.mk _ _ _ _ (adicPresentationLocalizedComparison g d U n)) :
    m₁ = adicPresentationInverseMate g d U n ∧
      m₂ = adicPresentationInverseMate g d U n := by
  sorry
end OpenMateTransport

end AlgebraicGeometry.Scheme
