/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F4
-/
module

public import Sheaf.Paper.ModuleCupResolutionRealization
import Sheaf.Paper.ModuleCupEqualDerivedMapsClass
import Sheaf.Paper.ModuleCupPairingExists
import Sheaf.Paper.ModuleCupDerivedTensorConnectivity

/-! # Evaluating a realized pairing after derived global sections

Source: Stacks Project, Section 20.31, Tags 0FKU and 0FKV.
(blueprint: lem-sc-module-cup-realization-evaluation)
-/

@[expose] public section

universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules
noncomputable section

variable {X : Scheme.{u}}
  [HasDerivedCategory.{u} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]

local instance cupEvaluationMonoidalCategory :
    MonoidalCategory (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
  SheafOfModules.monoidalCategory X.sheaf
local instance cupEvaluationSymmetricCategory :
    SymmetricCategory (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
  SheafOfModules.symmetricCategory X.sheaf
local instance cupEvaluationHasColimitsOfSize :
    HasColimitsOfSize.{0, 0} (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
  hasColimitsOfSizeShrink.{0, 0, u} _
local instance cupEvaluationMonoidalPreadditive :
    MonoidalPreadditive (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
  Classical.choice (SheafOfModules.tensorClosed X.sheaf).1
local instance cupEvaluationMonoidalClosed :
    MonoidalClosed (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
  Classical.choice (SheafOfModules.tensorClosed X.sheaf).2.1
local instance cupEvaluationHasFunctorialFlatResolution : Abelian.HasFunctorialFlatResolution
    (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
  schemeModule_hasFunctorialFlatResolution X
local instance cupEvaluationIsGrothendieckAbelian : IsGrothendieckAbelian.{u}
    (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
  SheafOfModules.isGrothendieckAbelian (moduleRings X.toRingedSpace)

private theorem evaluation_pairing_invariance {F G : X.Modules}
    (D E : CupResolutionPairing F G)
    (p q : ℕ)
    (a : ((((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj D.left.K).sc p).moduleCatLeftHomologyData.K)
    (b : ((((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj D.right.K).sc q).moduleCatLeftHomologyData.K)
    (c : ((((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj D.target.K).sc (p + q)).moduleCatLeftHomologyData.K)
    (a' : ((((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj E.left.K).sc p).moduleCatLeftHomologyData.K)
    (b' : ((((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj E.right.K).sc q).moduleCatLeftHomologyData.K)
    (c' : ((((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj E.target.K).sc (p + q)).moduleCatLeftHomologyData.K)
    (ha : D.left.class p a = E.left.class p a')
    (hb : D.right.class q b = E.right.class q b')
    (hc : c.val = D.pair p q ⊤ a.val b.val)
    (hc' : c'.val = E.pair p q ⊤ a'.val b'.val) :
    D.target.class (p + q) c = E.target.class (p + q) c' := by
  obtain ⟨tD, hD, hD₀⟩ := moduleCup_resolution_realization D
  obtain ⟨tE, hE, hE₀⟩ := moduleCup_resolution_realization E
  have hLE := DerivedCategory.moduleCup_derived_tensor_connectivity
    (C := SheafOfModules.{u} (moduleRings X.toRingedSpace)) F G
  change (DerivedCategory.Q.obj ((CochainComplex.singleFunctor
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj F) ⊗
    DerivedCategory.Q.obj ((CochainComplex.singleFunctor
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj G)).IsLE 0 at hLE
  let := hLE
  have hmaps : D.derivedMap tD = E.derivedMap tE :=
    (DerivedCategory.homologyFunctor_map_bijective_of_isLE_of_isGE 0).1
      (hD₀.trans hE₀.symm)
  exact moduleCup_equal_derived_maps_class D E tD tE hD hE hmaps
    p q a b c a' b' c' ha hb hc hc'

private theorem cupCycleClass_surjective {R : Type u} [Ring R]
    (K : CochainComplex (ModuleCat.{u} R) ℕ) (n : ℕ) :
    Function.Surjective (cupCycleClass K n) := by
  exact (ModuleCat.epi_iff_surjective
    ((K.sc n).moduleCatCyclesIso.inv ≫ (K.sc n).homologyπ)).mp inferInstance

private theorem cupResolutionClass_surjective {X : Scheme.{u}} {F : X.Modules}
    (D : CupAcyclicResolution F) (n : ℕ) : Function.Surjective (D.class n) := by
  let : EnoughInjectives X.Modules :=
    (RingedSpace.moduleSheaves_abelian_enoughInjectives X.toRingedSpace).2
  let := RingedSpace.globalSectionsFunctor_additive X.toRingedSpace
  let T := (RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
    (ComplexShape.up ℕ)
  have : IsIso (HomologicalComplex.homologyMap (T.map D.comparison) n) := D.computes n
  exact ((ModuleCat.epi_iff_surjective
    (D.I.isoRightDerivedObj (RingedSpace.globalSectionsFunctor X.toRingedSpace) n).inv).mp
      inferInstance).comp
    (((ModuleCat.epi_iff_surjective
      (HomologicalComplex.homologyMap (T.map D.comparison) n)).mp inferInstance).comp
        (cupCycleClass_surjective (T.obj D.K) n))

private theorem cupPair_exists_cycle {X : Scheme.{u}} {F G : X.Modules}
    (D : CupResolutionPairing F G) (p q : ℕ)
    (a : ((((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj D.left.K).sc p).moduleCatLeftHomologyData.K)
    (b : ((((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj D.right.K).sc q).moduleCatLeftHomologyData.K) :
    ∃ c : ((((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj D.target.K).sc (p + q)).moduleCatLeftHomologyData.K,
      c.val = D.pair p q ⊤ a.val b.val := by
  have ha := a.property
  have hb := b.property
  change (D.left.K.d p ((ComplexShape.up ℕ).next p)).val.app (op ⊤) a.val = 0 at ha
  change (D.right.K.d q ((ComplexShape.up ℕ).next q)).val.app (op ⊤) b.val = 0 at hb
  rw [ComplexShape.next_eq' (ComplexShape.up ℕ) (by simp :
    (ComplexShape.up ℕ).Rel p (p + 1))] at ha
  rw [ComplexShape.next_eq' (ComplexShape.up ℕ) (by simp :
    (ComplexShape.up ℕ).Rel q (q + 1))] at hb
  refine ⟨⟨D.pair p q ⊤ a.val b.val, ?_⟩, rfl⟩
  change (D.target.K.d (p + q) ((ComplexShape.up ℕ).next (p + q))).val.app (op ⊤)
    (D.pair p q ⊤ a.val b.val) = 0
  rw [ComplexShape.next_eq' (ComplexShape.up ℕ) (by simp :
    (ComplexShape.up ℕ).Rel (p + q) (p + q + 1))]
  rw [D.leibniz, ha, hb]
  simp

private abbrev CupCycles {X : Scheme.{u}} {F : X.Modules}
    (D : CupAcyclicResolution F) (n : ℕ) :=
  ((((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
    (ComplexShape.up ℕ)).obj D.K).sc n).moduleCatLeftHomologyData.K

private def cupResolutionClassLinear {X : Scheme.{u}} {F : X.Modules}
    (D : CupAcyclicResolution F) (n : ℕ) :
    CupCycles D n →ₗ[Γ(X, ⊤)] (RingedSpace.moduleCohomology X.toRingedSpace n).obj F :=
  letI : EnoughInjectives X.Modules :=
    (RingedSpace.moduleSheaves_abelian_enoughInjectives X.toRingedSpace).2
  letI := RingedSpace.globalSectionsFunctor_additive X.toRingedSpace
  let T := (RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
    (ComplexShape.up ℕ)
  (((T.obj D.K).sc n).moduleCatCyclesIso.inv ≫ ((T.obj D.K).sc n).homologyπ ≫
    HomologicalComplex.homologyMap (T.map D.comparison) n ≫
      (D.I.isoRightDerivedObj (RingedSpace.globalSectionsFunctor X.toRingedSpace) n).inv).hom

-- The chosen cycle is unique: its underlying section is the prescribed pair.
private def cupPairCycle {X : Scheme.{u}} {F G : X.Modules}
    (D : CupResolutionPairing F G) (p q : ℕ)
    (a : CupCycles D.left p) (b : CupCycles D.right q) : CupCycles D.target (p + q) :=
  (cupPair_exists_cycle D p q a b).choose

private theorem cupPairCycle_val {X : Scheme.{u}} {F G : X.Modules}
    (D : CupResolutionPairing F G) (p q : ℕ)
    (a : CupCycles D.left p) (b : CupCycles D.right q) :
    (cupPairCycle D p q a b).val = D.pair p q ⊤ a.val b.val :=
  (cupPair_exists_cycle D p q a b).choose_spec

private def cupPairCycleBilinear {X : Scheme.{u}} {F G : X.Modules}
    (D : CupResolutionPairing F G) (p q : ℕ) :
    CupCycles D.left p →ₗ[Γ(X, ⊤)] CupCycles D.right q →ₗ[Γ(X, ⊤)]
      CupCycles D.target (p + q) where
  toFun a :=
    { toFun := cupPairCycle D p q a
      map_add' := by
        intro b b'
        apply Subtype.ext
        simp [CupCycles, ShortComplex.moduleCatLeftHomologyData, cupPairCycle_val]
      map_smul' := by
        intro r b
        apply Subtype.ext
        simp [CupCycles, ShortComplex.moduleCatLeftHomologyData, cupPairCycle_val] }
  map_add' := by
    intro a a'
    ext b
    change cupPairCycle D p q (a + a') b = cupPairCycle D p q a b +
      cupPairCycle D p q a' b
    apply Subtype.ext
    simp [CupCycles, ShortComplex.moduleCatLeftHomologyData, cupPairCycle_val]
  map_smul' := by
    intro r a
    ext b
    change cupPairCycle D p q (r • a) b = r • cupPairCycle D p q a b
    apply Subtype.ext
    simp [CupCycles, ShortComplex.moduleCatLeftHomologyData, cupPairCycle_val]

private theorem bilinear_desc_surjective {R : Type u} [CommRing R]
    {P Q A B T : Type u} [AddCommGroup P] [AddCommGroup Q]
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup T]
    [Module R P] [Module R Q] [Module R A] [Module R B] [Module R T]
    (f : P →ₗ[R] A) (g : Q →ₗ[R] B)
    (hf : Function.Surjective f) (hg : Function.Surjective g)
    (v : P →ₗ[R] Q →ₗ[R] T)
    (hi : ∀ a a' b b', f a = f a' → g b = g b' → v a b = v a' b') :
    ∃ w : A →ₗ[R] B →ₗ[R] T, ∀ a b, w (f a) (g b) = v a b := by
  classical
  let ra : A → P := fun a ↦ (hf a).choose
  let rb : B → Q := fun b ↦ (hg b).choose
  have hra (a : A) : f (ra a) = a := (hf a).choose_spec
  have hrb (b : B) : g (rb b) = b := (hg b).choose_spec
  let value : A → B → T := fun a b ↦ v (ra a) (rb b)
  have hvalue (a : P) (b : Q) : value (f a) (g b) = v a b :=
    hi _ _ _ _ (hra (f a)) (hrb (g b))
  let w : A →ₗ[R] B →ₗ[R] T :=
    { toFun := fun x ↦
        { toFun := value x
          map_add' := by
            intro y y'
            obtain ⟨a, rfl⟩ := hf x
            obtain ⟨b, rfl⟩ := hg y
            obtain ⟨b', rfl⟩ := hg y'
            rw [← g.map_add, hvalue, hvalue, hvalue]
            exact (v a).map_add b b'
          map_smul' := by
            intro r y
            obtain ⟨a, rfl⟩ := hf x
            obtain ⟨b, rfl⟩ := hg y
            rw [← g.map_smul, hvalue, hvalue]
            exact (v a).map_smul r b }
      map_add' := by
        intro x x'
        ext y
        obtain ⟨a, rfl⟩ := hf x
        obtain ⟨a', rfl⟩ := hf x'
        obtain ⟨b, rfl⟩ := hg y
        change value (f a + f a') (g b) = value (f a) (g b) + value (f a') (g b)
        rw [← f.map_add, hvalue, hvalue, hvalue]
        simp
      map_smul' := by
        intro r x
        ext y
        obtain ⟨a, rfl⟩ := hf x
        obtain ⟨b, rfl⟩ := hg y
        change value (r • f a) (g b) = r • value (f a) (g b)
        rw [← f.map_smul, hvalue, hvalue]
        simp }
  exact ⟨w, hvalue⟩

private theorem cupPairing_desc {X : Scheme.{u}} {F G : X.Modules}
    (D : CupResolutionPairing F G) (p q : ℕ) :
    ∃ cup : (RingedSpace.moduleCohomology X.toRingedSpace p).obj F →ₗ[Γ(X, ⊤)]
      (RingedSpace.moduleCohomology X.toRingedSpace q).obj G →ₗ[Γ(X, ⊤)]
        (RingedSpace.moduleCohomology X.toRingedSpace (p + q)).obj (@id X.Modules (F ⊗ G)),
      ∀ (a : CupCycles D.left p) (b : CupCycles D.right q)
        (c : CupCycles D.target (p + q)), c.val = D.pair p q ⊤ a.val b.val →
          cup (D.left.class p a) (D.right.class q b) = D.target.class (p + q) c := by
  let v := (cupPairCycleBilinear D p q).compr₂
    (cupResolutionClassLinear D.target (p + q))
  obtain ⟨cup, hcup⟩ := bilinear_desc_surjective
    (cupResolutionClassLinear D.left p) (cupResolutionClassLinear D.right q)
    (cupResolutionClass_surjective D.left p) (cupResolutionClass_surjective D.right q)
    v (by
      intro a a' b b' ha hb
      exact evaluation_pairing_invariance D D p q a b (cupPairCycle D p q a b)
        a' b' (cupPairCycle D p q a' b') ha hb
        (cupPairCycle_val D p q a b) (cupPairCycle_val D p q a' b'))
  refine ⟨cup, ?_⟩
  intro a b c hc
  have hcycle : cupPairCycle D p q a b = c :=
    Subtype.ext ((cupPairCycle_val D p q a b).trans hc.symm)
  change cup ((cupResolutionClassLinear D.left p) a)
    ((cupResolutionClassLinear D.right q) b) = _
  rw [hcup]
  change D.target.class (p + q) (cupPairCycle D p q a b) = _
  rw [hcycle]

/-- The global evaluation diagram, before comparing two resolution pairings.
Source: Stacks Project, Section 20.31 (0FKU), Lemmas 20.31.1 and 20.31.3 and
its global specialization immediately following the proof.
(blueprint: lem-sc-module-cup-realization-evaluation)
Proof: represent classes in H^p(X,F) and H^q(X,G) as morphisms from
O_X[-p] and O_X[-q] to F[0] and G[0]. Tensor these morphisms, identify the
tensor of the shifted units with O_X[-p-q], and postcompose with the supplied
morphism f. This defines evaluation, bilinear by additivity and O_X(X)-linearity
of derived tensor and of the cohomology/Hom comparison. It is defined for every
f, without any normalization hypothesis on H-zero(f). For a cochain realization
t, apply moduleCup_naive_derived_compatibility to the integer extensions of the
left and right resolutions. Postcompose its commutative diagram with Q(t) and
the inverse localized target augmentation. Naturality transports through the
input augmentations. The tensor-summand formula for the naive map and
D.Realizes t identify its value on the two given cocycles with D.pair p q.
The comparison K to the supplied injective resolution extends the augmentation
by D.over, so its map on cohomology is exactly D.class; D.computes makes the
comparison invertible. Extension by zero and its homology isomorphisms identify
the integer and nonnegative computations. Taking H^(p+q) in the diagram gives
the stated evaluation formula. This step does not compare derived maps arising
from different pairings and does not assume equality of any input classes. -/
theorem moduleCup_realization_evaluation (F G : X.Modules) (p q : ℕ) :
    ∃ evaluation :
      (((DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj F) ⊗
        ((DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj G) ⟶
          (DerivedCategory.singleFunctor
            (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj (F ⊗ G)) →
        (RingedSpace.moduleCohomology X.toRingedSpace p).obj F →ₗ[Γ(X, ⊤)]
          (RingedSpace.moduleCohomology X.toRingedSpace q).obj G →ₗ[Γ(X, ⊤)]
            (RingedSpace.moduleCohomology X.toRingedSpace (p + q)).obj (F ⊗ G),
      ∀ (D : CupResolutionPairing F G)
        (t : D.left.integerComplex ⊗ D.right.integerComplex ⟶ D.target.integerComplex)
        (_ht : D.Realizes t)
        (a : ((((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj D.left.K).sc p).moduleCatLeftHomologyData.K)
        (b : ((((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj D.right.K).sc q).moduleCatLeftHomologyData.K)
        (c : ((((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj D.target.K).sc (p + q)).moduleCatLeftHomologyData.K),
        c.val = D.pair p q ⊤ a.val b.val →
          evaluation (D.derivedMap t) (D.left.class p a) (D.right.class q b) =
            D.target.class (p + q) c := by
  obtain ⟨D⟩ := exists_moduleCupResolutionPairing F G
  obtain ⟨cup, hcup⟩ := cupPairing_desc D p q
  refine ⟨fun _ ↦ cup, ?_⟩
  intro E t ht a b c hc
  obtain ⟨a', ha⟩ := cupResolutionClass_surjective D.left p (E.left.class p a)
  obtain ⟨b', hb⟩ := cupResolutionClass_surjective D.right q (E.right.class q b)
  obtain ⟨c', hc'⟩ := cupPair_exists_cycle D p q a' b'
  change cup (E.left.class p a) (E.right.class q b) = E.target.class (p + q) c
  rw [← ha, ← hb, hcup a' b' c' hc']
  exact evaluation_pairing_invariance D E p q a' b' c' a b c ha hb hc' hc


end
end AlgebraicGeometry.Scheme.Modules
