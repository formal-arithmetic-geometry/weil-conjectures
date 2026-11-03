/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.FiniteDualizingTowers.FiniteDualizingCoefficientTowerMap
public import WeilConjectures.AlgebraicGeometry.GeneralFieldFiniteDualizingCoefficientChange
public import WeilConjectures.CategoryTheory.RingedSiteModules
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import WeilConjectures.Compactification.NagataCompactification

/-! # Data for coherent finite dualizing towers over general fields

Source: current blueprint, `literature/blueprint/latest/blueprint/sec-smooth-purity/sk-lem-sp-tower/
lem-coef-integral-finite-extension.proof.md`, paragraphs 3--4 and final paragraph
(blueprint: def-sf-general-field-finite-dualizing-tower-data).

The quotient-tower categories, scalar models and ramification subsequences are the
published constructions. The finite terms below instead use the general-field
etale dualizing object and its exact pro-etale site transport. Their transition
maps are precisely the adjoints of the published general-field counit comparisons.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.FiniteCoefficientAdjoints
open WeilConjectures.FiniteDualizingTowers

namespace WeilConjectures.GeneralFieldFiniteDualizingTowers

variable (k : Type u) [Field k] (X : Scheme.{u})
  [X.Over (Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
  [QuasiCompact (X ↘ Spec (.of k))] [IsSeparated (X ↘ Spec (.of k))]

/-- One compactification of the structural morphism, for all coefficient levels.
Source: blueprint paragraph 3 and Nagata compactification
(blueprint: def-sf-general-field-finite-dualizing-tower-data). -/
def compactification : Compactification (X ↘ Spec (.of k)) :=
  letI := hasCompactification_of_finiteType_over_field k X (Spec (.of k))
    (X ↘ Spec (.of k))
  HasCompactification.compactification (X ↘ Spec (.of k))

/-- The finite dualizing object is the exact pro-etale realization of the ordinary
etale exceptional image of the regular coefficient unit.
Source: blueprint paragraph 3 and the general-field finite coefficient lemma
(blueprint: def-sf-general-field-finite-dualizing-tower-data). -/
def finiteOmega (A : Type (u + 1)) [CommRing A] [Finite A] :=
  letI := (compactification k X).hasCompactification
  (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.obj
    (Etale.dualizingComplex A (X ↘ Spec (.of k)))

/-- The actual general-field finite counit comparison, transposed under derived
scalar extension/restriction and transported to intrinsic ring-sheaf coordinates.
It applies to both quotient homomorphisms and coefficient extensions.
Source: blueprint paragraph 3 and the general-field finite coefficient lemma
(blueprint: def-sf-general-field-finite-dualizing-tower-data). -/
def counitAdjunctMap {A B : Type (u + 1)} [CommRing A] [CommRing B]
    [Finite A] [Finite B] (φ : A →+* B) :
    (realization X A).mapDerivedCategory.obj (finiteOmega k X A) ⟶
      (res X φ).mapDerivedCategory.obj
        ((realization X B).mapDerivedCategory.obj (finiteOmega k X B)) :=
  letI := (compactification k X).hasCompactification
  let adj := @FiniteCoefficientOrdinary.scalarAdjunction.{u} X.ProEt inferInstance
    (essentiallySmallSelf.{0, u, u + 1} _) (Scheme.ProEt.topology X) A B
    inferInstance inferInstance φ
  (realization X A).mapDerivedCategory.map
      (adj.homEquiv _ _ (Etale.generalFieldFiniteProDualizingMap φ
        (X ↘ Spec (.of k)))) ≫
    (derivedRestriction X φ).inv.app (finiteOmega k X B)

variable {l : ℕ} [Fact l.Prime] {E : Type (u + 1)} [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The prescribed finite dualizing term at positive level n+1.
Source: blueprint paragraph 3
(blueprint: def-sf-general-field-finite-dualizing-tower-data). -/
def omega (s : Stage l E) (n : ℕ) :=
  (realization X (atLevel s n).ring).mapDerivedCategory.obj
    (finiteOmega k X (atLevel s n).ring)

/-- The counit-normalized arrow at a fixed quotient stage.
Source: blueprint paragraph 3
(blueprint: def-sf-general-field-finite-dualizing-tower-data). -/
abbrev counitAdjunct {s t : Stage l E} (a : Arrow s t) :=
  counitAdjunctMap k X a.ringMap

/-- Simultaneous realization with its specified finite terms and counit transitions.
`HEq` only transports the equality between the adjacent map of `ofOpSequence` and
its given quotient map; it does not weaken the transition equation.
Source: paragraphs 3--4 (blueprint: def-sf-general-field-finite-dualizing-tower-data). -/
structure Realization (s : Stage l E) where
  obj : Tower X s
  level : ∀ n : ℕ, (evaluation X s n).obj obj ≅ omega k X s n
  transition : ∀ n : ℕ,
    HEq ((SheafOfModules.systemDerivedTransition.{u + 1, u, u + 1} (rings X s) (Nat.le_succ n)).app
        ((SheafOfModules.strictSystemSequenceEquivalence.{u + 1, u, u + 1} (rings X
          s)).inverse.mapDerivedCategory.obj
          obj) ≫
      (SheafOfModules.systemRestriction.{u + 1, u, u + 1} (rings X s) (Nat.le_succ
        n)).mapDerivedCategory.map
        ((evaluationBridge X s n).hom.app obj ≫ (level n).hom))
      ((evaluationBridge X s (n + 1)).hom.app obj ≫ (level (n + 1)).hom ≫
        counitAdjunct k X (quotient s (Nat.le_succ n)))

/-- The level identification in the equivalent strict-system coordinates.
Source: paragraph 4 (blueprint: def-sf-general-field-finite-dualizing-tower-data). -/
def strictLevel {s : Stage l E} (P : Realization k X s) (n : ℕ) :=
  (evaluationBridge X s n).app P.obj ≪≫ P.level n

/-- A comparison is normalized by the *specified* finite dualizing counit mate.
The formula uses the tensor/restriction adjunction, so it fixes the evaluation of
coefficient extension without choosing an arbitrary evaluation isomorphism.
Source: paragraph 4 (blueprint: def-sf-general-field-finite-dualizing-tower-data). -/
def IsComparison {s t : Stage l E} (a : Arrow s t)
    (A : SheafOfModules.SystemScalarModel.{u + 1, u, u + 1}
      (SheafOfModules.singletonSequenceRingMap.{u + 1, u, u + 1} (ringMap X a)))
    (P : Realization k X s) (Q : Realization k X t)
    (f : A.model.T.obj P.obj ⟶ Q.obj) : Prop :=
  ∀ n : ℕ,
    HEq ((evaluation X s n).map (A.adjunction.homEquiv P.obj Q.obj f) ≫
      (SheafOfModules.singletonDerivedRestrictionEvaluation.{u + 1, u, u + 1} (ringMap X a)
        n).hom.app Q.obj ≫
      (SheafOfModules.singletonLevelRestriction.{u + 1, u, u + 1} (ringMap X a)
        n).mapDerivedCategory.map
        (Q.level n).hom)
      ((P.level n).hom ≫ counitAdjunct k X (levelArrow a n))

/-- The prescribed identification of two simultaneous resolutions.
Source: final paragraph (blueprint: def-sf-general-field-finite-dualizing-tower-data). -/
def IsIdentification {s : Stage l E} (P Q : Realization k X s) (i : P.obj ≅ Q.obj) : Prop :=
  ∀ n : ℕ, (evaluation X s n).map i.hom ≫ (Q.level n).hom = (P.level n).hom

/-- Restriction to the full upper-uniformizer tower at levels e(n+1), through the
residue-preserving quotient-ring identifications. The latter are fixed, not arbitrary.
Source: paragraph 3 (blueprint: def-sf-general-field-finite-dualizing-tower-data). -/
def IsFullUniformizerRestriction (s : Stage l E) (P : Realization k X s) : Prop :=
  ∃ (e : ℕ+)
    (h : ∀ n : ℕ, (atLevel s n).ideal =
      (atLevel (baseStage (l := l) (E := s.field) 1) (ramificationIndices e n)).ideal)
    (Q : Realization k X (baseStage (l := l) (E := s.field) 1))
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
              (strictLevel k X Q (ramificationIndices e n)).hom))
        ((strictLevel k X P n).hom ≫
          counitAdjunctMap k X (Ideal.quotEquivOfEq (h n)).toRingHom)

/-- All clauses of the coherent comparison on the common base-uniformizer towers.
For three stages the final tower is U/t^(n+1)U, so the composition equation already
uses the common levels. Its associator is the normalized balanced derived tensor map.
Source: paragraphs 3--4 and final paragraph
(blueprint: def-sf-general-field-finite-dualizing-tower-data). -/
structure ComparisonData where
  towers : ∀ s : Stage l E, Realization k X s
  fullUniformizer : ∀ s : Stage l E, IsFullUniformizerRestriction k X s (towers s)
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
    IsComparison k X a (scalar a) (towers s) (towers t) (comparison a).hom
  unique : ∀ {s t : Stage l E} (a : Arrow s t)
    (f : (scalar a).model.T.obj (towers s).obj ⟶ (towers t).obj),
    IsComparison k X a (scalar a) (towers s) (towers t) f → f = (comparison a).hom
  unit : ∀ s : Stage l E, (comparison (identity s)).hom =
    (SheafOfModules.systemScalarModelDerivedUnit.{u + 1, u, u + 1} (sequenceMap_identity X s)
      (scalar (identity s))).hom.app (towers s).obj
  composition : ∀ {s t v : Stage l E} (a : Arrow s t) (b : Arrow t v),
    (SheafOfModules.systemScalarModelDerivedComposition.{u + 1, u, u + 1} (sequenceMap_composite X
      a b)
      (scalar a) (scalar b) (scalar (composite a b))).hom.app (towers s).obj ≫
        (comparison (composite a b)).hom =
      (scalar b).model.T.map (comparison a).hom ≫ (comparison b).hom
  identification : ∀ (s : Stage l E) (P Q : Realization k X s),
    ∃! i : P.obj ≅ Q.obj, IsIdentification k X P Q i
  replacement : ∀ {s t : Stage l E} (a : Arrow s t)
    (P : Realization k X s) (Q : Realization k X t)
    (i : P.obj ≅ (towers s).obj) (j : Q.obj ≅ (towers t).obj),
    IsIdentification k X P (towers s) i → IsIdentification k X Q (towers t) j →
    ∀ f : (scalar a).model.T.obj P.obj ⟶ Q.obj,
      IsComparison k X a (scalar a) P Q f →
      (scalar a).model.T.map i.hom ≫ (comparison a).hom = f ≫ j.hom


end WeilConjectures.GeneralFieldFiniteDualizingTowers
