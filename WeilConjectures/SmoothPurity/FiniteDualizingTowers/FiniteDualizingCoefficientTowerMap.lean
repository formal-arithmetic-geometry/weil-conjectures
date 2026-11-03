/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.FiniteFreeCoefficients.Sites.FiniteFreeCoefficientExtensionData
public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.SixFunctors.Finite.Dualizing.FiniteDualizingData
public import WeilConjectures.Algebra.Homology.System.SystemSingletonScalarBasic
public import WeilConjectures.Algebra.Homology.System.SystemDerivedTransition
public import WeilConjectures.Algebra.Homology.System.SystemDerivedSubsequence
public import WeilConjectures.Algebra.Homology.System.SystemEvaluationNormalizationData
public import WeilConjectures.Algebra.Homology.System.SystemScalarCoherence
public import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteModuleIntrinsicComparison
import WeilConjectures.SixFunctors.Integral.IntegralDualizing
import WeilConjectures.SixFunctors.Finite.FiniteDualizing
import WeilConjectures.SixFunctors.FiniteFreeCoefficients.Sites.FiniteFreeCoefficientExtensionData
import WeilConjectures.AlgebraicGeometry.FiniteCoefficientAdjoints.FiniteCoefficientAdjointData
import WeilConjectures.SixFunctors.FiniteFreeCoefficients.NormalizedStageCoefficientCalculus
import WeilConjectures.SixFunctors.FiniteFreeCoefficients.CoefficientMapDirectGeometry
import WeilConjectures.SixFunctors.FiniteFreeCoefficients.CoefficientMapHomGeometry
import WeilConjectures.SixFunctors.FiniteFreeCoefficients.CoefficientMapClosedGeometry
import WeilConjectures.SixFunctors.DncCoefficientTransport.SectionScalarBaseChange
import WeilConjectures.SixFunctors.FiniteFreeCoefficients.CoefficientExceptionalGeometryOfCube
import WeilConjectures.SixFunctors.FiniteFreeCoefficients.ProScalarPullNormalization
import WeilConjectures.AlgebraicGeometry.Finite.Coefficient.FiniteCoefficientDirectImage
import WeilConjectures.SixFunctors.FiniteFreeCoefficients.CoefficientMapProClosedGeometry
import WeilConjectures.SixFunctors.FiniteFreeCoefficients.NormalizedProScalarTensorGeometricSquare
import WeilConjectures.SixFunctors.FiniteFreeCoefficients.CoefficientMapProHomGeometry
import WeilConjectures.CategoryTheory.ProperBaseChange.ExchangeMateCube
import Mathlib.CategoryTheory.Adjunction.Mates
import WeilConjectures.AlgebraicGeometry.Etale.Scalar.EtaleScalarPullbackUnitCoherence
import WeilConjectures.SixFunctors.FiniteFreeCoefficients.CoefficientMapProOmegaGeometry
import WeilConjectures.SixFunctors.Integral.IntegralDualizingFiniteBounds
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.Algebra.Homology.DerivedCategory.Fractions
import Mathlib.CategoryTheory.MorphismProperty.Comma
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantInd
import WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantPro
import Mathlib.CategoryTheory.Products.Basic
import Mathlib.CategoryTheory.Limits.Types.ColimitType
import Mathlib.CategoryTheory.Localization.CalculusOfFractions
import Mathlib.CategoryTheory.Adjunction.Basic
import WeilConjectures.Algebra.Homology.SixFunctors.OrdinaryDerivedChangeOfRings
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.SequentialDerived.SequentialSemilinearDerivedDiagrams
import WeilConjectures.Algebra.Homology.Module.ModulePullbackPushforwardAdjunctionSupplement
import WeilConjectures.AlgebraicGeometry.Finite.FiniteStageVerdierBiduality
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Mathlib.CategoryTheory.Triangulated.TStructure.Basic

/-! # Coherent finite dualizing coefficient comparisons

Source: current blueprint, sec-smooth-purity/sk-lem-sp-tower/
lem-coef-integral-finite-extension.proof.md, paragraphs 3--4 and final paragraph
(blueprint: lem-sf-finite-dualizing-coefficient-tower-map).

Positive level n+1 is indexed by n : ℕ. `Stage` retains the base uniformizer:
its upper-field quotient is S/t^(n+1)S, including ramified extensions.
The sequence-site module category is the existing exact presentation of strict
quotient-semilinear towers, and its derived category is the ordinary localization.
The coordinate helpers below extend the recorded intrinsic realization to coefficients
already in universe u+1; they do not identify the site and coefficient universes.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.FiniteCoefficientAdjoints

namespace WeilConjectures.FiniteDualizingTowers

/-- The finite constant ring sheaf in the native finite-free coefficient universe.
Source: blueprint paragraph 3 (blueprint: lem-sf-finite-dualizing-coefficient-tower-map). -/
def constantRing (X : Scheme.{u}) (A : Type (u + 1)) [CommRing A] :
    Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1} :=
  (constantSheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}).obj (.of A)

/-- The scalar-unit map into the associated constant ring sheaf.
Source: blueprint paragraph 3 (blueprint: lem-sf-finite-dualizing-coefficient-tower-map). -/
def scalarUnit (X : Scheme.{u}) (A : Type (u + 1)) [CommRing A] :
    (Functor.const X.ProEtᵒᵖ).obj (RingCat.of A) ⟶
      ((sheafCompose (Scheme.ProEt.topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (constantRing X A)).obj :=
  Functor.whiskerRight
    (toSheafify (Scheme.ProEt.topology X)
      ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of A)))
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})

/-- The actual associated-module-sheaf realization, with constant scalars fixed by the unit.
Source: blueprint paragraph 3 (blueprint: lem-sf-finite-dualizing-coefficient-tower-map). -/
def realization (X : Scheme.{u}) (A : Type (u + 1)) [CommRing A] :
    Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A) ⥤
      SemilinearSections.Mod (Scheme.ProEt.topology X) (constantRing X A) :=
  sheafToPresheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A) ⋙
    ProEtale.finiteCoefficientModulePresheaf X.ProEt A ⋙
      PresheafOfModules.sheafification.{u + 1} (scalarUnit X A)

/-- The constant-sheaf image of a coefficient homomorphism.
Source: paragraph 3 (blueprint: lem-sf-finite-dualizing-coefficient-tower-map). -/
def constantMap (X : Scheme.{u}) {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) : constantRing X A ⟶ constantRing X B :=
  (constantSheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}).map (CommRingCat.ofHom φ)

/-- Ordinary restriction for the actual constant-ring map.
Source: paragraph 3 (blueprint: lem-sf-finite-dualizing-coefficient-tower-map). -/
abbrev res (X : Scheme.{u}) {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) :=
  SheafOfModules.restrictScalars.{u + 1}
    ((sheafCompose (Scheme.ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map (constantMap X φ))

/-- The generating section of the associated module sheaf.
Source: paragraph 3 (blueprint: lem-sf-finite-dualizing-coefficient-tower-map). -/
def unitSection (X : Scheme.{u}) (A : Type (u + 1)) [CommRing A]
    (M : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A))
    (W : X.ProEtᵒᵖ) (x : M.obj.obj W) : ((realization X A).obj M).val.obj W :=
  (((PresheafOfModules.sheafificationAdjunction (scalarUnit X A)).unit.app
    ((ProEtale.finiteCoefficientModulePresheaf X.ProEt A).obj M.obj)).app W) x

/-- The realization/restriction square is uniquely fixed on the scalar-unit sections.
Source: paragraph 3 (blueprint: lem-sf-finite-dualizing-coefficient-tower-map).
Proof: naturality of the constant-scalar units gives the ring square. The identity on
its constant generating sections extends uniquely through module sheafification in
both directions. These extensions are inverse and natural. The generating sections
are locally surjective, proving uniqueness, including on the empty object. -/
theorem restriction_existsUnique (X : Scheme.{u})
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B) :
    ∃! e : realization X B ⋙ res X φ ≅
      Sheaf.restrictScalars (Scheme.ProEt.topology X) φ ⋙ realization X A,
      ∀ (M : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} B))
        (W : X.ProEtᵒᵖ) (x : M.obj.obj W),
        HEq ((e.hom.app M).val.app W (unitSection X B M W x))
          (unitSection X A ((Sheaf.restrictScalars (Scheme.ProEt.topology X) φ).obj M) W x)
    := by
  sorry

/-- The section-normalized restriction comparison, chosen from its unique characterization.
Source: paragraph 3 (blueprint: lem-sf-finite-dualizing-coefficient-tower-map). -/
def restriction (X : Scheme.{u}) {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) : realization X B ⋙ res X φ ≅
      Sheaf.restrictScalars (Scheme.ProEt.topology X) φ ⋙ realization X A :=
  (restriction_existsUnique X φ).choose

/-- Its exact derived localization; source: paragraph 3
(blueprint: lem-sf-finite-dualizing-coefficient-tower-map). -/
def derivedRestriction (X : Scheme.{u}) {A B : Type (u + 1)}
    [CommRing A] [CommRing B] (φ : A →+* B) :
    (realization X B).mapDerivedCategory ⋙ (res X φ).mapDerivedCategory ≅
      Sheaf.derivedRestrictScalars (Scheme.ProEt.topology X) φ ⋙
        (realization X A).mapDerivedCategory :=
  Functor.mapDerivedCategorySquareIso (restriction X φ)

variable {l : ℕ} [Fact l.Prime] {E : Type (u + 1)} [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The same field and base embedding at positive level n+1.
Source: paragraph 3 (blueprint: lem-sf-finite-dualizing-coefficient-tower-map). -/
def atLevel (s : Stage l E) (n : ℕ) : Stage l E :=
  { s with exponent := ⟨n + 1, Nat.succ_pos n⟩ }

/-- The actual quotient arrow between two levels of one coefficient field.
Source: paragraph 3 (blueprint: lem-sf-finite-dualizing-coefficient-tower-map). -/
def quotient (s : Stage l E) {m n : ℕ} (h : n ≤ m) : Arrow (atLevel s m) (atLevel s n) :=
  ⟨AlgHom.id (Padic l) s.field, by ext x; rfl, Nat.add_le_add_right h 1⟩

/-- Finite constant quotient ring sheaves, retaining the image of the base uniformizer.
Source: paragraph 3 (blueprint: lem-sf-finite-dualizing-coefficient-tower-map). -/
def rings (X : Scheme.{u}) (s : Stage l E) :
    ℕᵒᵖ ⥤ Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1} :=
  Functor.ofOpSequence (X := fun n ↦ constantRing X (atLevel s n).ring)
    (fun n ↦ constantMap X (quotient s (Nat.le_succ n)).ringMap)

/-- The ordinary derived category of the existing ringed sequence-site module category.
Source: paragraphs 3--4 (blueprint: lem-sf-finite-dualizing-coefficient-tower-map). -/
abbrev Tower (X : Scheme.{u}) (s : Stage l E) :=
  DerivedCategory (SheafOfModules.systemSequenceModules.{u + 1, u, u + 1} (rings X s))

/-- Exact level evaluation, localized at quasi-isomorphisms.
Source: paragraph 4 (blueprint: lem-sf-finite-dualizing-coefficient-tower-map). -/
abbrev evaluation (X : Scheme.{u}) (s : Stage l E) (n : ℕ) :=
  (SheafOfModules.systemSequenceEvaluation.{u + 1, u, u + 1} (rings X s) n).mapDerivedCategory

/-- The field embedding at a fixed quotient level.
Source: paragraph 3 (blueprint: lem-sf-finite-dualizing-coefficient-tower-map). -/
def levelArrow {s t : Stage l E} (a : Arrow s t) (n : ℕ) :
    Arrow (atLevel s n) (atLevel t n) :=
  ⟨a.embedding, a.over_base, le_refl _⟩

/-- Naturality of the genuine quotient maps under a coefficient embedding.
Source: paragraph 3 (blueprint: lem-sf-finite-dualizing-coefficient-tower-map).
Proof: the two composites send each residue of an integer to the residue of its image
under the same field embedding. Quotient induction and naturality of constant
sheafification identify them. -/
theorem ringMap_naturality (X : Scheme.{u}) {s t : Stage l E} (a : Arrow s t)
    {m n : ℕ} (f : op m ⟶ op n) :
    (rings X s).map f ≫ constantMap X (levelArrow a n).ringMap =
      constantMap X (levelArrow a m).ringMap ≫ (rings X t).map f := by
  sorry

/-- The canonical map of quotient coefficient diagrams.
Source: paragraph 3 (blueprint: lem-sf-finite-dualizing-coefficient-tower-map). -/
def ringMap (X : Scheme.{u}) {s t : Stage l E} (a : Arrow s t) :
    rings X s ⟶ rings X t where
  app n := constantMap X (levelArrow a n.unop).ringMap
  naturality _ _ f := ringMap_naturality X a f

/-- The finite dualizing term in intrinsic module coordinates, using the recorded
compactification-based exceptional image of the coefficient unit.
Source: paragraph 3 (blueprint: lem-sf-finite-dualizing-coefficient-tower-map). -/
def omega (D : FiniteFieldDatum.{u}) (X : Scheme.{u})
    [X.Over (Spec (.of D.k))] [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]
    (s : Stage l E) (n : ℕ) :=
  (realization X (atLevel s n).ring).mapDerivedCategory.obj
    (FiniteFreeCoefficients.Sites.omega true (atLevel s n).ring
      (finiteDualizingCompactification D X))

/-- The prescribed finite counit mate, transposed into scalar restriction and realized.
This formula applies both to coefficient extension and to quotient transitions.
Source: paragraph 3 (blueprint: lem-sf-finite-dualizing-coefficient-tower-map). -/
def counitAdjunctMap (D : FiniteFieldDatum.{u}) (X : Scheme.{u})
    [X.Over (Spec (.of D.k))] [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) :
    (realization X A).mapDerivedCategory.obj
        (FiniteFreeCoefficients.Sites.omega true A (finiteDualizingCompactification D X)) ⟶
      (res X φ).mapDerivedCategory.obj
        ((realization X B).mapDerivedCategory.obj
          (FiniteFreeCoefficients.Sites.omega true B (finiteDualizingCompactification D X))) :=
  (realization X A).mapDerivedCategory.map
    ((Adjunction.ofIsRightAdjoint
      (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology X) φ)).homEquiv _ _
      (FiniteFreeCoefficients.Sites.proOmegaMap φ (finiteDualizingCompactification D X))) ≫
    (derivedRestriction X φ).inv.app
      (FiniteFreeCoefficients.Sites.omega true B (finiteDualizingCompactification D X))

/-- The fixed counit mate for the given coefficient arrow.
Source: paragraph 3 (blueprint: lem-sf-finite-dualizing-coefficient-tower-map). -/
abbrev counitAdjunct (D : FiniteFieldDatum.{u}) (X : Scheme.{u})
    [X.Over (Spec (.of D.k))] [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]
    {s t : Stage l E} (a : Arrow s t) := counitAdjunctMap D X a.ringMap

/-- The identity field embedding, retaining the given coefficient stage.
Source: final paragraph (blueprint: lem-sf-finite-dualizing-coefficient-tower-map). -/
def identity (s : Stage l E) : Arrow s s :=
  ⟨AlgHom.id (Padic l) s.field, by ext x; rfl, le_refl _⟩

/-- The composite of the actual field embeddings, over the common base field.
Source: final paragraph (blueprint: lem-sf-finite-dualizing-coefficient-tower-map). -/
def composite {s t v : Stage l E} (a : Arrow s t) (b : Arrow t v) : Arrow s v :=
  ⟨b.embedding.comp a.embedding,
    AlgHom.ext (fun x ↦ (congrArg b.embedding (DFunLike.congr_fun a.over_base x)).trans
      (DFunLike.congr_fun b.over_base x)), b.level.trans a.level⟩

/-- The sequence coefficient map of the identity embedding is the identity.
Source: final paragraph (blueprint: lem-sf-finite-dualizing-coefficient-tower-map).
Proof: each component sends a residue class to itself. Quotient induction, constant
sheafification, and the componentwise sequence-ring construction prove the equality. -/
theorem sequenceMap_identity (X : Scheme.{u}) (s : Stage l E) :
    SheafOfModules.singletonSequenceRingMap.{u + 1, u, u + 1} (ringMap X (identity s)) = 𝟙 _ := by
  sorry

/-- The sequence coefficient map of the composite is the composite coefficient map.
Source: final paragraph (blueprint: lem-sf-finite-dualizing-coefficient-tower-map).
Proof: each composite sends an integer residue to the residue of its image under
b.embedding.comp a.embedding. Quotient induction gives equality before sheafification;
apply the constant-sheaf and ringed sequence-site functors. -/
theorem sequenceMap_composite (X : Scheme.{u}) {s t v : Stage l E}
    (a : Arrow s t) (b : Arrow t v) :
    SheafOfModules.singletonSequenceRingMap.{u + 1, u, u + 1} (ringMap X (composite a b)) =
      SheafOfModules.singletonSequenceRingMap.{u + 1, u, u + 1} (ringMap X a) ≫
        SheafOfModules.singletonSequenceRingMap.{u + 1, u, u + 1} (ringMap X b) := by
  sorry

variable (D : FiniteFieldDatum.{u}) (X : Scheme.{u})
  [X.Over (Spec (.of D.k))] [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]

/-- Evaluation after the exact sequence-site equivalence, with its canonical compositor.
Source: paragraph 4 (blueprint: lem-sf-finite-dualizing-coefficient-tower-map). -/
def evaluationBridge (s : Stage l E) (n : ℕ) :
    (SheafOfModules.strictSystemSequenceEquivalence.{u + 1, u, u + 1} (rings X
      s)).inverse.mapDerivedCategory ⋙
      SheafOfModules.derivedSystemEvaluation.{u + 1, u, u + 1} (rings X s) n ≅ evaluation X s n :=
  (Functor.mapDerivedCategoryCompIso
    (SheafOfModules.strictSystemSequenceEquivalence.{u + 1, u, u + 1} (rings X s)).inverse
    (SheafOfModules.systemEvaluation.{u + 1, u, u + 1} (rings X s) n)).symm

/-- Simultaneous realization with its specified finite terms and counit transitions.
`HEq` only transports the equality between the adjacent map of `ofOpSequence` and
its given quotient map; it does not weaken the transition equation.
Source: paragraphs 3--4 (blueprint: lem-sf-finite-dualizing-coefficient-tower-map). -/
structure Realization (s : Stage l E) where
  obj : Tower X s
  level : ∀ n : ℕ, (evaluation X s n).obj obj ≅ omega D X s n
  transition : ∀ n : ℕ,
    HEq ((SheafOfModules.systemDerivedTransition.{u + 1, u, u + 1} (rings X s) (Nat.le_succ n)).app
        ((SheafOfModules.strictSystemSequenceEquivalence.{u + 1, u, u + 1} (rings X
          s)).inverse.mapDerivedCategory.obj
          obj) ≫
      (SheafOfModules.systemRestriction.{u + 1, u, u + 1} (rings X s) (Nat.le_succ
        n)).mapDerivedCategory.map
        ((evaluationBridge X s n).hom.app obj ≫ (level n).hom))
      ((evaluationBridge X s (n + 1)).hom.app obj ≫ (level (n + 1)).hom ≫
        counitAdjunct D X (quotient s (Nat.le_succ n)))

/-- The level identification in the equivalent strict-system coordinates.
Source: paragraph 4 (blueprint: lem-sf-finite-dualizing-coefficient-tower-map). -/
def strictLevel {s : Stage l E} (P : Realization D X s) (n : ℕ) :=
  (evaluationBridge X s n).app P.obj ≪≫ P.level n

/-- A comparison is normalized by the *specified* finite dualizing counit mate.
The formula uses the tensor/restriction adjunction, so it fixes the evaluation of
coefficient extension without choosing an arbitrary evaluation isomorphism.
Source: paragraph 4 (blueprint: lem-sf-finite-dualizing-coefficient-tower-map). -/
def IsComparison {s t : Stage l E} (a : Arrow s t)
    (A : SheafOfModules.SystemScalarModel.{u + 1, u, u + 1}
      (SheafOfModules.singletonSequenceRingMap.{u + 1, u, u + 1} (ringMap X a)))
    (P : Realization D X s) (Q : Realization D X t)
    (f : A.model.T.obj P.obj ⟶ Q.obj) : Prop :=
  ∀ n : ℕ,
    HEq ((evaluation X s n).map (A.adjunction.homEquiv P.obj Q.obj f) ≫
      (SheafOfModules.singletonDerivedRestrictionEvaluation.{u + 1, u, u + 1} (ringMap X a)
        n).hom.app Q.obj ≫
      (SheafOfModules.singletonLevelRestriction.{u + 1, u, u + 1} (ringMap X a)
        n).mapDerivedCategory.map
        (Q.level n).hom)
      ((P.level n).hom ≫ counitAdjunct D X (levelArrow a n))

/-- The prescribed identification of two simultaneous resolutions.
Source: final paragraph (blueprint: lem-sf-finite-dualizing-coefficient-tower-map). -/
def IsIdentification {s : Stage l E} (P Q : Realization D X s) (i : P.obj ≅ Q.obj) : Prop :=
  ∀ n : ℕ, (evaluation X s n).map i.hom ≫ (Q.level n).hom = (P.level n).hom

/-- The ramification subsequence on zero-based indices: level n+1 becomes e(n+1).
Source: paragraph 3 (blueprint: lem-sf-finite-dualizing-coefficient-tower-map). -/
def ramificationIndices (e : ℕ+) : ℕ ↪o ℕ :=
  OrderEmbedding.ofStrictMono (fun n : ℕ ↦ (e : ℕ) * n + ((e : ℕ) - 1))
    (fun _ _ h ↦ Nat.add_lt_add_right (Nat.mul_lt_mul_of_pos_left h e.pos) _)

/-- The selected exponent is exactly e(n+1).
Source: paragraph 3 (blueprint: lem-sf-finite-dualizing-coefficient-tower-map).
Proof: expand the definition of the selected index, distribute multiplication over
n+1, and cancel the predecessor with the successor using e>0. -/
theorem ramificationIndices_exponent (e : ℕ+) (n : ℕ) :
    ramificationIndices e n + 1 = (e : ℕ) * (n + 1) := by
  sorry

/-- Restriction to the full upper-uniformizer tower at levels e(n+1), through the
residue-preserving quotient-ring identifications. The latter are fixed, not arbitrary.
Source: paragraph 3 (blueprint: lem-sf-finite-dualizing-coefficient-tower-map). -/
def IsFullUniformizerRestriction (s : Stage l E) (P : Realization D X s) : Prop :=
  ∃ (e : ℕ+)
    (h : ∀ n : ℕ, (atLevel s n).ideal =
      (atLevel (baseStage (l := l) (E := s.field) 1) (ramificationIndices e n)).ideal)
    (Q : Realization D X (baseStage (l := l) (E := s.field) 1))
    (ζ : rings X s ≅ SheafOfModules.selectedSystemRings
      (rings X (baseStage (l := l) (E := s.field) 1)) (ramificationIndices e)),
    (∀ n : ℕ, ζ.hom.app (op n) =
      constantMap X (Ideal.quotEquivOfEq (h n)).toRingHom) ∧
    ∃ i : ((SheafOfModules.strictSystemSequenceEquivalence.{u + 1, u, u + 1}
        (rings X s)).inverse.mapDerivedCategory.obj P.obj) ≅
      (SheafOfModules.systemNormalizationRestriction.{u + 1, u, u + 1}
        ζ.hom).mapDerivedCategory.obj
        ((SheafOfModules.derivedSystemSubsequence.{u + 1, u, u + 1}
          (rings X (baseStage (l := l) (E := s.field) 1)) (ramificationIndices e)).obj
          ((SheafOfModules.strictSystemSequenceEquivalence.{u + 1, u, u + 1}
            (rings X (baseStage (l := l) (E := s.field) 1))).inverse.mapDerivedCategory.obj
              Q.obj)),
      ∀ n : ℕ, HEq
        ((SheafOfModules.derivedSystemEvaluation.{u + 1, u, u + 1}
          (rings X s) n).map i.hom ≫
          (SheafOfModules.systemNormalizationDerivedRestrictionEvaluation.{u + 1, u, u + 1}
            ζ.hom n).hom.app _ ≫
          (SheafOfModules.singletonLevelRestriction.{u + 1, u, u + 1}
            ζ.hom n).mapDerivedCategory.map
            ((SheafOfModules.systemDerivedSubsequenceEvaluation.{u + 1, u, u + 1}
              (rings X (baseStage (l := l) (E := s.field) 1))
                (ramificationIndices e) n).hom.app _ ≫
              (strictLevel D X Q (ramificationIndices e n)).hom))
        ((strictLevel D X P n).hom ≫
          counitAdjunctMap D X (Ideal.quotEquivOfEq (h n)).toRingHom)

/-- All clauses of the coherent comparison on the common base-uniformizer towers.
For three stages the final tower is U/t^(n+1)U, so the composition equation already
uses the common levels. Its associator is the normalized balanced derived tensor map.
Source: paragraphs 3--4 and final paragraph
(blueprint: lem-sf-finite-dualizing-coefficient-tower-map). -/
structure ComparisonData where
  towers : ∀ s : Stage l E, Realization D X s
  fullUniformizer : ∀ s : Stage l E, IsFullUniformizerRestriction D X s (towers s)
  scalar : ∀ {s t : Stage l E} (a : Arrow s t),
    SheafOfModules.SystemScalarModel.{u + 1, u, u + 1} (SheafOfModules.singletonSequenceRingMap.{u
      + 1, u, u + 1} (ringMap X a))
  exact : ∀ {s t : Stage l E} (a : Arrow s t),
    PreservesFiniteLimits (scalar a).model.E ∧ PreservesFiniteColimits (scalar a).model.E
  finiteFree : ∀ {s t : Stage l E} (a : Arrow s t) (n : ℕ),
    (levelArrow a n).IsFiniteFree
  exactDerived : ∀ {s t : Stage l E} (a : Arrow s t),
    ∃ (hlim : PreservesFiniteLimits (scalar a).model.E)
      (hcolim : PreservesFiniteColimits (scalar a).model.E),
      letI := hlim
      letI := hcolim
      ∃ θ : (scalar a).model.T ≅ (scalar a).model.E.mapDerivedCategory,
        ∀ K : CochainComplex (SheafOfModules.systemSequenceModules.{u + 1, u, u + 1}
          (rings X s)) ℤ,
          (scalar a).model.ε.app K = θ.hom.app (DerivedCategory.Q.obj K) ≫
            (scalar a).model.E.mapDerivedCategoryFactors.hom.app K
  comparison : ∀ {s t : Stage l E} (a : Arrow s t),
    (scalar a).model.T.obj (towers s).obj ≅ (towers t).obj
  normalized : ∀ {s t : Stage l E} (a : Arrow s t),
    IsComparison D X a (scalar a) (towers s) (towers t) (comparison a).hom
  unique : ∀ {s t : Stage l E} (a : Arrow s t)
    (f : (scalar a).model.T.obj (towers s).obj ⟶ (towers t).obj),
    IsComparison D X a (scalar a) (towers s) (towers t) f → f = (comparison a).hom
  unit : ∀ s : Stage l E, (comparison (identity s)).hom =
    (SheafOfModules.systemScalarModelDerivedUnit.{u + 1, u, u + 1} (sequenceMap_identity X s)
      (scalar (identity s))).hom.app (towers s).obj
  composition : ∀ {s t v : Stage l E} (a : Arrow s t) (b : Arrow t v),
    (SheafOfModules.systemScalarModelDerivedComposition.{u + 1, u, u + 1} (sequenceMap_composite X
      a b)
      (scalar a) (scalar b) (scalar (composite a b))).hom.app (towers s).obj ≫
        (comparison (composite a b)).hom =
      (scalar b).model.T.map (comparison a).hom ≫ (comparison b).hom
  identification : ∀ (s : Stage l E) (P Q : Realization D X s),
    ∃! i : P.obj ≅ Q.obj, IsIdentification D X P Q i
  replacement : ∀ {s t : Stage l E} (a : Arrow s t)
    (P : Realization D X s) (Q : Realization D X t)
    (i : P.obj ≅ (towers s).obj) (j : Q.obj ≅ (towers t).obj),
    IsIdentification D X P (towers s) i → IsIdentification D X Q (towers t) j →
    ∀ f : (scalar a).model.T.obj P.obj ⟶ Q.obj,
      IsComparison D X a (scalar a) P Q f →
      (scalar a).model.T.map i.hom ≫ (comparison a).hom = f ≫ j.hom

/-- The finite dualizing counit comparisons lift to coherent isomorphisms in the
ordinary unbounded derived category of quotient-semilinear module towers.
Source: current blueprint, sec-smooth-purity/sk-lem-sp-tower/
lem-coef-integral-finite-extension.proof.md, paragraphs 3--4 and final paragraph
(blueprint: lem-sf-finite-dualizing-coefficient-tower-map).
Proof: choose a dimension bound for X. Finite dualizing bounds give a common lower
cohomological bound. Transpose the counit-defined quotient comparisons under the
scalar adjunction and apply sequentialSemilinearDerivedDiagrams, first for the base
tower and for each full upper-uniformizer tower, then restrict to ramification levels.
A free integer-ring basis descends compatibly to each finite quotient, so ordinary
levelwise scalar extension is exact. The finite-free coefficient theorem identifies
its counit mates and their quotient squares, giving a compatible family of maps.
For adjacent levels, scalar adjunction and quotient comparison identify the negative
Hom group with Hom(omega,omega[-1]). Finite Verdier biduality turns this into
Hom(unit[1],unit), which is zero by standard t-structure orthogonality. The sequential
mapping exact sequence therefore lifts the family uniquely to a tower morphism.
Joint conservativity of evaluations makes it invertible. The finite unit and
composition formulas lift to the displayed equations by the same uniqueness.
Lifting the identity families likewise gives the unique canonical identifications of
any two simultaneous resolutions, and uniqueness gives the replacement equation. -/
theorem finiteDualizingCoefficientTowerMap
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (E : Type (u + 1)) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))] :
    Nonempty (ComparisonData (l := l) (E := E) D X) := by
  sorry

end WeilConjectures.FiniteDualizingTowers
