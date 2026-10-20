/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF groups T1 and P3
-/
module

public import Sheaf.Paper.ModuleCupResolutionData
public import Sheaf.AlgebraicGeometry.ModuleCechComparison
public import WeilConjectures.Topology.Sheaves.CechComparison
import Sheaf.Paper.ModuleCupPairingExists
import Sheaf.Paper.ModuleCupResolutionInvariance

/-! # Cup products computed by acyclic resolutions

Source: Stacks Project, Cohomology, section-cup-product and Tag 0FKV
(blueprint: def-sc-module-cohomology-cup-product).
The characterization uses resolutions with a sectionwise bilinear chain pairing.
It determines the derived cup product; Godement resolutions supply such pairings.
-/

@[expose] public section

universe uM
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open CategoryTheory.MonoidalCategory
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section

/-- The sheaf cup product is the bilinear pairing computed by every acyclic resolution
pairing extending the tensor of sections. This is the usual derived cup product:
resolve by Godement complexes, apply the naive signed tensor pairing, and identify
cohomology through the resolution comparison. Conversely, for any such pairing the
map from the derived tensor of F and G to F tensor G is determined by its degree-zero
augmentation, so it gives the same product.
Source: Stacks, section-cup-product and Tag 0FKV
(blueprint: def-sc-module-cohomology-cup-product). -/
def IsModuleCupProduct {X : Scheme.{uM}} (F G : X.Modules) (p q : ℕ)
    (cup : (RingedSpace.moduleCohomology X.toRingedSpace p).obj F →ₗ[Γ(X, ⊤)]
      (RingedSpace.moduleCohomology X.toRingedSpace q).obj G →ₗ[Γ(X, ⊤)]
        (RingedSpace.moduleCohomology X.toRingedSpace (p + q)).obj
          (@id X.Modules (F ⊗ G))) : Prop :=
  ∀ (D : CupResolutionPairing F G)
    (a : ((((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj D.left.K).sc p).moduleCatLeftHomologyData.K)
    (b : ((((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj D.right.K).sc q).moduleCatLeftHomologyData.K)
    (c : ((((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj D.target.K).sc (p + q)).moduleCatLeftHomologyData.K),
    c.val = D.pair p q ⊤ a.val b.val →
      cup (D.left.class p a) (D.right.class q b) = D.target.class (p + q) c

private theorem cupCycleClass_surjective {R : Type uM} [Ring R]
    (K : CochainComplex (ModuleCat.{uM} R) ℕ) (n : ℕ) :
    Function.Surjective (cupCycleClass K n) := by
  exact (ModuleCat.epi_iff_surjective
    ((K.sc n).moduleCatCyclesIso.inv ≫ (K.sc n).homologyπ)).mp inferInstance

private theorem cupResolutionClass_surjective {X : Scheme.{uM}} {F : X.Modules}
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

private theorem cupPair_exists_cycle {X : Scheme.{uM}} {F G : X.Modules}
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

private abbrev CupCycles {X : Scheme.{uM}} {F : X.Modules}
    (D : CupAcyclicResolution F) (n : ℕ) :=
  ((((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
    (ComplexShape.up ℕ)).obj D.K).sc n).moduleCatLeftHomologyData.K

private def cupResolutionClassLinear {X : Scheme.{uM}} {F : X.Modules}
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
private def cupPairCycle {X : Scheme.{uM}} {F G : X.Modules}
    (D : CupResolutionPairing F G) (p q : ℕ)
    (a : CupCycles D.left p) (b : CupCycles D.right q) : CupCycles D.target (p + q) :=
  (cupPair_exists_cycle D p q a b).choose

private theorem cupPairCycle_val {X : Scheme.{uM}} {F G : X.Modules}
    (D : CupResolutionPairing F G) (p q : ℕ)
    (a : CupCycles D.left p) (b : CupCycles D.right q) :
    (cupPairCycle D p q a b).val = D.pair p q ⊤ a.val b.val :=
  (cupPair_exists_cycle D p q a b).choose_spec

private def cupPairCycleBilinear {X : Scheme.{uM}} {F G : X.Modules}
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

private theorem bilinear_desc_surjective {R : Type uM} [CommRing R]
    {P Q A B T : Type uM} [AddCommGroup P] [AddCommGroup Q]
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

private theorem cupPairing_desc {X : Scheme.{uM}} {F G : X.Modules}
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
      exact moduleCup_resolution_invariance D D p q a b (cupPairCycle D p q a b)
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

/-- The acyclic-resolution characterization defines a unique sheaf cup product.
Source: Stacks, section-cup-product and Tag 0FKV
(blueprint: def-sc-module-cohomology-cup-product).
Proof: take a computing pairing from exists_moduleCupResolutionPairing. The class
map of each resolution is surjective: the projection from cycles to homology is
an epimorphism and both subsequent comparison maps are isomorphisms. Leibniz
constructs the product cocycle, and its fixed underlying section determines it
uniquely. Bilinearity descends through the two surjective class maps because
moduleCup_resolution_invariance with D = E makes the product independent of
representatives. The same invariance theorem with arbitrary E proves the
characterization for every pairing. Finally, lift any two cohomology classes to
cycles for D; both candidate products are equal to the class of their paired
cycle. Extensionality of bilinear maps gives uniqueness. -/
theorem exists_unique_moduleCupProduct {X : Scheme.{uM}} (F G : X.Modules) (p q : ℕ) :
    ∃! cup : (RingedSpace.moduleCohomology X.toRingedSpace p).obj F →ₗ[Γ(X, ⊤)]
      (RingedSpace.moduleCohomology X.toRingedSpace q).obj G →ₗ[Γ(X, ⊤)]
        (RingedSpace.moduleCohomology X.toRingedSpace (p + q)).obj (@id X.Modules (F ⊗ G)),
      IsModuleCupProduct F G p q cup := by
  obtain ⟨D⟩ := exists_moduleCupResolutionPairing F G
  obtain ⟨cup, hcup⟩ := cupPairing_desc D p q
  refine ⟨cup, ?_, ?_⟩
  · intro E a b c hc
    obtain ⟨a', ha⟩ := cupResolutionClass_surjective D.left p (E.left.class p a)
    obtain ⟨b', hb⟩ := cupResolutionClass_surjective D.right q (E.right.class q b)
    obtain ⟨c', hc'⟩ := cupPair_exists_cycle D p q a' b'
    rw [← ha, ← hb, hcup a' b' c' hc']
    exact moduleCup_resolution_invariance D E p q a' b' c' a b c ha hb hc' hc
  · intro other hother
    ext x y
    obtain ⟨a, rfl⟩ := cupResolutionClass_surjective D.left p x
    obtain ⟨b, rfl⟩ := cupResolutionClass_surjective D.right q y
    obtain ⟨c, hc⟩ := cupPair_exists_cycle D p q a b
    exact (hother D a b c hc).trans (hcup a b c hc).symm

end
end AlgebraicGeometry.Scheme.Modules
