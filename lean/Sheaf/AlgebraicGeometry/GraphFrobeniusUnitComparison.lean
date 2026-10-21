/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q17
-/
module

public import Sheaf.SixFunctors.SelectedSchemeGaloisComparison
public import Sheaf.Paper.TraceFormulaCoefficientConventions
public import Sheaf.AlgebraicGeometry.FiniteOrdinaryPullback
public import Sheaf.AlgebraicGeometry.ProEtaleConstantModuleUnit
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
import Sheaf.Paper.IntegralFinitePullbackComposition
import Sheaf.Paper.OrdinaryCompactWeilCohomology
import Sheaf.Paper.SfDerivedDirectImage
import Sheaf.AlgebraicGeometry.ProEtaleConstantDerivedDirectImage
import Sheaf.Paper.SfIntegralReductionTower
import Sheaf.Paper.DerivedScalarExtensionRestrictionAdjunction
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
import Sheaf.AlgebraicGeometry.FrobeniusTrivializationPullback
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Sheaf.AlgebraicGeometry.ProEtaleConstantRingMap
import Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.CategoryTheory.Localization.Predicate
import Mathlib.CategoryTheory.Sites.Sheafification
import Sheaf.AlgebraicGeometry.FrobeniusFactorization
import Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations
import Sheaf.AlgebraicGeometry.ProEtaleUnitLerayChainFormula

/-!
# Constant normalization and ordinary sections of the Frobenius comparison

Source: main-20261015 blueprint, sec-trace-formula/sk-d-weil,
prop-trf-graph-frobenius-operator.proof.md, Step 1
(blueprint: lem-trf-graph-frobenius-unit-comparison).

The existential presentation retains the sectionwise relative-Frobenius normalization
of the recorded scheme--Galois comparison. Thus the witnesses describe its canonical
comparison, including its action on constants. The cohomology arrows below are built
from the recorded derived adjunction on finiteOrdinarySections = Fib_s composed with Ra_Y*.
The canonical comparison to absolute sections is supplied with its pullback compatibility
in def-trf-finite-ordinary-pullback; no cohomology model is silently substituted.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry.Scheme

/-- The constant-coefficient module map to its direct image is the scalar structure map.
Source: blueprint Step 1, normalization on constant coefficients; Stacks Tag 03D1
(blueprint: lem-trf-graph-frobenius-unit-comparison). -/
def graphFrobeniusConstantDirectImage (A : Type u) [CommRing A]
    {X Y : Scheme.{u}} (h : X ⟶ Y) :
    proEtaleConstantModule Y A ⟶
      (proEtaleConstantRingPushforward A h).obj (proEtaleConstantModule X A) := by
  dsimp only [proEtaleConstantModule, proEtaleConstantRingPushforward,
    proEtaleRingModuleDirectImage]
  exact SheafOfModules.unitToPushforwardObjUnit _

/-- The ordinary canonical identification of pulled-back constant modules, as the adjunct
of the constant-section scalar structure map. Source: blueprint Step 1; Stacks Tag 03D1
(blueprint: lem-trf-graph-frobenius-unit-comparison). -/
def graphFrobeniusConstantPullback (A : Type u) [CommRing A]
    {X Y : Scheme.{u}} (h : X ⟶ Y) :
    (proEtaleConstantRingPullback A h).obj (proEtaleConstantModule Y A) ⟶
      proEtaleConstantModule X A :=
  ((proEtaleConstantRingAdjunction A h).homEquiv _ _).symm
    (graphFrobeniusConstantDirectImage A h)

/-- The same constant identification in degree zero of the derived category.
Source: blueprint Step 1, d_h; Stacks Section 0735
(blueprint: lem-trf-graph-frobenius-unit-comparison). -/
def graphFrobeniusDerivedConstantPullback (A : Type u) [CommRing A]
    {X Y : Scheme.{u}} (h : X ⟶ Y) :
    (proEtaleConstantRingDerivedPullback A h).obj
        ((DerivedCategory.singleFunctor _ 0).obj (proEtaleConstantModule Y A)) ⟶
      (DerivedCategory.singleFunctor _ 0).obj (proEtaleConstantModule X A) :=
  ((proEtaleConstantRingPullback A h).mapDerivedCategorySingleFunctor 0).hom.app
      (proEtaleConstantModule Y A) ≫
    (DerivedCategory.singleFunctor _ 0).map (graphFrobeniusConstantPullback A h)

end AlgebraicGeometry.Scheme

namespace WeilConjectures.TraceFormulaCoefficientConventions
open AlgebraicGeometry.Scheme

/-- The geometric fibre has its specified structure morphism to the geometric point.
Source: blueprint finite-field fibre (blueprint: lem-trf-graph-frobenius-unit-comparison). -/
instance graphFrobeniusGeometricOver (T : TraceFormulaCoefficientConventions.{u}) :
    T.geometricBaseChange.Over (Spec (.of T.datum.k)) := ⟨T.structureMap⟩

/-- The ordinary unit pullback on precisely the recorded finiteOrdinarySections objects.
The scalar prime, extension field and positive level are those of T.
Source: blueprint Step 1 (blueprint: lem-trf-graph-frobenius-unit-comparison). -/
def graphFrobeniusOrdinaryPullback (T : TraceFormulaCoefficientConventions.{u})
    (h : T.geometricBaseChange ⟶ T.geometricBaseChange)
    (M : proEtaleDerivedCategory T.geometricBaseChange T.coefficientRing) :
    finiteOrdinarySections T.datum T.coefficients.l T.coefficientField
        T.geometricBaseChange T.level T.level_pos M ⟶
      finiteOrdinarySections T.datum T.coefficients.l T.coefficientField
        T.geometricBaseChange T.level T.level_pos
          ((proEtaleConstantRingDerivedPullback T.coefficientRing h).obj M) :=
  finiteOrdinaryPullback T.datum T.coefficientRing h M

/-- The canonical Frobenius comparison fixes the constant coefficient object and
identifies the ordinary derived cohomology pullbacks, naturally in the coefficient complex.
The witnesses r, tau and w specify exactly the relative-Frobenius normalization and
factorization of the recorded comparison; kappa is their prescribed derived composite.

Source: main-20261015 blueprint, sec-trace-formula/sk-d-weil,
prop-trf-graph-frobenius-operator.proof.md, Step 1
(blueprint: lem-trf-graph-frobenius-unit-comparison).

Proof:
1. Put F = Fr_Y^(am), P = Phi^m and G = g^m. The Frobenius factorization and inverse
   arithmetic/geometric Galois automorphisms give P = F followed by G. The normalized
   relative-Frobenius site isomorphism r gives the module trivialization tau as its
   adjoint; its unit equation is the sectionwise equation displayed below.
2. On a K-flat representative with flat terms (lem-pc-kflat-resolution), canonical
   derived composition is termwise module composition. The absolute-Frobenius
   trivialization is the exact termwise descent of tau. Localization uniqueness
   (lem-weil-pbc-localization-universal-property) identifies their composite with kappa.
3. Restriction along r inverse preserves every constant scalar, including 1. The
   constant-presheaf/sheafification universal property identifies its coefficient map
   with prop-weil-pbc-proetale-constant-ring-map. Taking adjuncts using
   lem-weil-pbc-conjugate-iso-unit-equation gives tau_A = d_F.
4. The scalar structure map for P = FG is the composite of the two structure maps,
   by the same sheafification uniqueness. Naturality of tau with d_G therefore yields
   kappa_A followed by d_G = d_P, first on modules and then in degree zero. The
   canonical d maps are invertible: under scalar transport their inverse is the
   tensor-unit map a to 1 tensor a; the balancing relation gives both identities.
5. A section s of N is the module map A_Y to N sending 1 to s. Its ordinary unit
   pullback is h*(s) after d_h inverse. Naturality of the module comparison and step 4
   identify these section maps for P and G, in every degree of a complex.
6. Choose a K-injective representative I and a K-injective resolution j_G of G*I
   (prop-pur-kinjective-resolutions-exist). Use j_P = theta_I followed by j_G as the
   common target resolution of P*I. Apply lem-trf-proetale-unit-leray-chain-formula
   to both maps; step 5 identifies the representative section maps. Cancel RGamma(j_G)
   to get the second equality below. Naturality follows from the units, Leray and kappa.
   Apply finiteOrdinaryPullback_absolute_compatibility from
   def-trf-finite-ordinary-pullback to P and G. Its point-section normalization and a_Y
   Leray comparison identify the absolute chain calculation with the recorded
   finiteOrdinarySections objects. Naturality of that comparison at kappa and cancellation
   of its target isomorphism give the equality in Fib_s composed with Ra_Y* below.
   Step 4 proves preservation of the canonical constant section 1, without a scalar choice.
-/
theorem graphFrobenius_unit_comparison
    (T : TraceFormulaCoefficientConventions.{u}) [IsProper T.X₀.hom]
    (m : ℕ) (hm : 1 ≤ m) :
    ∃ r : 𝟭 T.geometricBaseChange.ProEt ≅ proEtaleBaseChange
        (T.geometricBaseChange.iterateFrobenius T.datum.prime
          (T.datum.model_characteristic
            (pullback.fst T.X₀.hom
              (Spec.map (CommRingCat.ofHom (algebraMap T.datum.k₀ T.datum.k))) ≫ T.X₀.hom))
          (T.datum.a * m)),
    ∃ τ : proEtaleConstantRingPullback T.coefficientRing
        (T.geometricBaseChange.iterateFrobenius T.datum.prime
          (T.datum.model_characteristic
            (pullback.fst T.X₀.hom
              (Spec.map (CommRingCat.ofHom (algebraMap T.datum.k₀ T.datum.k))) ≫ T.X₀.hom))
          (T.datum.a * m)) ≅ 𝟭 _,
      (∀ V : T.geometricBaseChange.ProEt,
        ∃ hV : (T.datum.p : Γ(V.left, ⊤)) = 0,
          (r.hom.app V).left ≫ pullback.fst V.hom
              (T.geometricBaseChange.iterateFrobenius T.datum.prime
                (T.datum.model_characteristic
                  (pullback.fst T.X₀.hom
                    (Spec.map (CommRingCat.ofHom (algebraMap T.datum.k₀ T.datum.k))) ≫
                      T.X₀.hom)) (T.datum.a * m)) =
            V.left.iterateFrobenius T.datum.prime hV (T.datum.a * m)) ∧
      (∀ (N : proEtaleRingModules T.geometricBaseChange
            (proEtaleConstantRing T.geometricBaseChange T.coefficientRing))
          (V : T.geometricBaseChange.ProEt) (s : N.val.obj (Opposite.op V)),
        ((proEtaleConstantRingAdjunction T.coefficientRing
            (T.geometricBaseChange.iterateFrobenius T.datum.prime
              (T.datum.model_characteristic
                (pullback.fst T.X₀.hom
                  (Spec.map (CommRingCat.ofHom (algebraMap T.datum.k₀ T.datum.k))) ≫
                    T.X₀.hom)) (T.datum.a * m))).unit.app N ≫
          (proEtaleConstantRingPushforward T.coefficientRing
            (T.geometricBaseChange.iterateFrobenius T.datum.prime
              (T.datum.model_characteristic
                (pullback.fst T.X₀.hom
                  (Spec.map (CommRingCat.ofHom (algebraMap T.datum.k₀ T.datum.k))) ≫
                    T.X₀.hom)) (T.datum.a * m))).map (τ.hom.app N)).val.app
                      (Opposite.op V) s = N.val.map (r.inv.app V).op s) ∧
      ∃ w : T.datum.schemeFrobeniusIterate T.X₀ m =
          T.geometricBaseChange.iterateFrobenius T.datum.prime
            (T.datum.model_characteristic
              (pullback.fst T.X₀.hom
                (Spec.map (CommRingCat.ofHom (algebraMap T.datum.k₀ T.datum.k))) ≫ T.X₀.hom))
            (T.datum.a * m) ≫
              HPow.hPow (α := End T.geometricBaseChange)
                (T.datum.geometricGaloisFrobenius T.X₀) m,
      ∃ κ : proEtaleConstantRingDerivedPullback T.coefficientRing
          (T.datum.schemeFrobeniusIterate T.X₀ m) ≅
        proEtaleConstantRingDerivedPullback T.coefficientRing
          (HPow.hPow (α := End T.geometricBaseChange)
            (T.datum.geometricGaloisFrobenius T.X₀) m),
        κ.hom = eqToHom (congrArg (proEtaleConstantRingDerivedPullback T.coefficientRing) w) ≫
          (proEtaleConstantRingPullbackComposition
            (T.geometricBaseChange.iterateFrobenius T.datum.prime
              (T.datum.model_characteristic
                (pullback.fst T.X₀.hom
                  (Spec.map (CommRingCat.ofHom (algebraMap T.datum.k₀ T.datum.k))) ≫
                    T.X₀.hom)) (T.datum.a * m))
            (HPow.hPow (α := End T.geometricBaseChange)
              (T.datum.geometricGaloisFrobenius T.X₀) m) T.coefficientRing).inv ≫
          Functor.whiskerLeft
            (proEtaleConstantRingDerivedPullback T.coefficientRing
              (HPow.hPow (α := End T.geometricBaseChange)
                (T.datum.geometricGaloisFrobenius T.X₀) m))
            (proEtaleFrobeniusDerivedIso T.coefficientRing τ).hom ≫
          (Functor.rightUnitor _).hom ∧
        IsIso (graphFrobeniusDerivedConstantPullback T.coefficientRing
          (T.datum.schemeFrobeniusIterate T.X₀ m)) ∧
        IsIso (graphFrobeniusDerivedConstantPullback T.coefficientRing
          (HPow.hPow (α := End T.geometricBaseChange)
            (T.datum.geometricGaloisFrobenius T.X₀) m)) ∧
        (κ.hom.app ((DerivedCategory.singleFunctor _ 0).obj
            (proEtaleConstantModule T.geometricBaseChange T.coefficientRing)) ≫
          graphFrobeniusDerivedConstantPullback T.coefficientRing
            (HPow.hPow (α := End T.geometricBaseChange)
              (T.datum.geometricGaloisFrobenius T.X₀) m) =
          graphFrobeniusDerivedConstantPullback T.coefficientRing
            (T.datum.schemeFrobeniusIterate T.X₀ m)) ∧
        (∀ M : T.boundedConstructibleFiniteTor.FullSubcategory,
          (graphFrobeniusOrdinaryPullback T
              (T.datum.schemeFrobeniusIterate T.X₀ m) M.obj) ≫
            (finiteOrdinarySectionsFunctor T.datum T.coefficientRing T.geometricBaseChange).map
              (κ.hom.app M.obj) =
          (graphFrobeniusOrdinaryPullback T
            (HPow.hPow (α := End T.geometricBaseChange)
              (T.datum.geometricGaloisFrobenius T.X₀) m) M.obj)) := by
  sorry

end WeilConjectures.TraceFormulaCoefficientConventions
