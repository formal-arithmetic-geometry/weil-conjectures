/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityFiniteSetting
public import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityNormalizedTowers
public import WeilConjectures.AlgebraicGeometry.SpTowerShriek.SmoothPurityTowerShriekLevels
public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicCoefficientTwistsUnrestricted
public import WeilConjectures.Algebra.Homology.Signed.SignedLineScalarTensorTower
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityCoefficientTowers
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.Compactification.RefinementCategory
public import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityCoefficientTowersAbelian
import all WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityCoefficientTowers
import WeilConjectures.AlgebraicGeometry.Pur.PurTwistSheafLocallyFree

/-! # Ground-field retagging of ordinary strict-tower operations

Source: blueprint main-20261015, sec-smooth-purity,
sk-prop-sp-tower-geometric-gamma.proof.md, clauses (2)--(3), and
thm-pur-weil-equivariance-of-purity-and-trace, proof Step 1
(blueprint: lem-pur-tower-operations-ground-field-retagging).

Retagging is postcomposition of the structure map, not pullback of the scheme.
The equalities below concern entire strict systems and entire derived functors.
The parameters b and o fix the published, representative-normalized operations once
on the underlying schemes; they are not new geometric or normalization hypotheses.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures

namespace AlgebraicGeometry.ProEtale

/-- Postcompose the structural map with Spec(sigma), retaining the scheme and every arrow.
Source: blueprint gamma proof (2)--(3), underlying-site part of equivariance Step 1
(blueprint: lem-pur-tower-operations-ground-field-retagging). -/
def spGroundFieldRetag (P : PurityFiniteSetting.{u})
    (σ : P.field.k ≃ₐ[P.field.k₀] P.field.k) :
    Over (Spec (CommRingCat.of P.field.k)) ⥤ Over (Spec (CommRingCat.of P.field.k)) :=
  Over.map (Spec.map (CommRingCat.ofHom σ.toRingHom))

/-- The same ordinary compactification after retagging the base structure maps.
Its ambient scheme is over k through p followed by the retagged structure map of Y.
Source: blueprint gamma proof (2)--(3), same-compactification argument
(blueprint: lem-pur-tower-operations-ground-field-retagging). -/
def spGroundFieldRetagCompactification (P : PurityFiniteSetting.{u})
    (σ : P.field.k ≃ₐ[P.field.k₀] P.field.k)
    {X Y : Over (Spec (CommRingCat.of P.field.k))} {f : X ⟶ Y}
    (c : Compactification f.left) :
    Compactification ((spGroundFieldRetag P σ).map f).left := c

/-- The actual ell-power quotient in commutative ring sheaves. Forgetting commutativity
recovers spCoefficientConstantQuotient; no coefficient action is changed by retagging.
Source: blueprint gamma proof (2), actual quotient coefficients
(blueprint: lem-pur-tower-operations-ground-field-retagging). -/
def spEllTwistQuotient (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (T : Scheme.{u}) (n : ℕ) :
    purTwistIntegralConstant T l E ⟶ SpTowerShriek.B l E T n :=
  (constantSheaf (ProEt.topology T) CommRingCat.{u + 1}).map
    (CommRingCat.ofHom (ULift.ringEquiv.symm.toRingHom.comp
      ((Ideal.Quotient.mk (spEllIdeal l E ^ (n + 1))).comp ULift.ringEquiv.toRingHom)))

/-- The ell-power quotient of the published integral Tate line, using the actual
constant quotient map. This is O_E(1) tensor_{O_E} O_E/ell^(n+1), before signed powers.
Source: blueprint gamma proof (2), coefficient twists and quotient transitions
(blueprint: lem-pur-tower-operations-ground-field-retagging). -/
def spEllTwistOne (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (T : Scheme.{u}) (n : ℕ) :=
  SheafOfModules.changeOfRingsOfUniverses.{u, u + 1, u + 1, u + 1}
    (spEllTwistQuotient l E T n) (purTwistIntegralOne T l E)

/-- Signed finite Tate lines at the ell-power levels of the strict tower. Positive
powers and internal duals are exactly those of the recorded coefficient-twist definition.
Source: blueprint gamma proof (2), signed Tate twists
(blueprint: lem-pur-tower-operations-ground-field-retagging). -/
def spEllTwistLine (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (T : Scheme.{u})
    (n : ℕ) (m : ℤ) :=
  coefficientTwistLine T (R := SpTowerShriek.B l E T n) (spEllTwistOne l E T n) m

/-- The family of actual scalar-extension comparisons between adjacent signed lines.
Source: blueprint gamma proof (2), signed quotient transitions
(blueprint: lem-pur-tower-operations-ground-field-retagging). -/
abbrev SpEllTwistComparisons (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (T : Scheme.{u}) (n : ℕ) :=
  ∀ m : ℤ, SheafOfModules.changeOfRingsOfUniverses.{u, u + 1, u + 1, u + 1}
    (SpTowerShriek.tau l E T n)
    (spEllTwistLine l E T (n + 1) m) ≅ spEllTwistLine l E T n m

/-- The quotient comparisons are fixed at exponent one on ordinary local pure tensors;
all other signed powers use the published tensor/dual normalization. In particular the
negative formula precomposes with the inverse positive comparison, rather than dualizing
in the wrong direction.
Source: blueprint gamma proof (2), signed-line quotient construction
(blueprint: lem-pur-tower-operations-ground-field-retagging). -/
def SpEllTwistComparisonsNormalized (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (T : Scheme.{u}) (n : ℕ)
    (B : SpEllTwistComparisons l E T n) : Prop :=
  (∀ (U : T.ProEtᵒᵖ) (s : (SpTowerShriek.B l E T n).obj.obj U)
    (t : (SpTowerShriek.B l E T (n + 1)).obj.obj U)
    (x : (purTwistIntegralOne T l E).val.obj U),
    (B 1).hom.val.app U
      (SheafOfModules.scalarExtensionSection.{u + 1, u, u + 1, u + 1}
        (SpTowerShriek.tau l E T n)
        (spEllTwistOne l E T (n + 1)) U s
        (SheafOfModules.scalarExtensionSection.{u + 1, u, u + 1, u + 1}
        (spEllTwistQuotient l E T (n + 1))
          (purTwistIntegralOne T l E) U t x)) =
      SheafOfModules.scalarExtensionSection.{u + 1, u, u + 1, u + 1}
        (spEllTwistQuotient l E T n)
        (purTwistIntegralOne T l E) U
        (s * (SpTowerShriek.tau l E T n).hom.app U t) x) ∧
  SheafOfModules.SignedLineComparisonNormalized.{u + 1, u, u + 1}
    (SpTowerShriek.tau l E T n) (spEllTwistOne l E T (n + 1))
    (spEllTwistOne l E T n) (B 1) B

/-- The actual semilinear quotient transition, obtained from its scalar-extension
comparison by the canonical scalar unit. These are maps of sheaves, before derivation.
Source: blueprint gamma proof (2), strict quotient transitions
(blueprint: lem-pur-tower-operations-ground-field-retagging). -/
def spEllTwistTransition (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (T : Scheme.{u}) (n : ℕ)
    (B : SpEllTwistComparisons l E T n) (m : ℤ) :=
  SheafOfModules.scalarExtensionEmbedding.{u + 1, u, u + 1, u + 1}
    (SpTowerShriek.tau l E T n)
      (spEllTwistLine l E T (n + 1) m) ≫
    (SheafOfModules.restrictScalars.{u + 1}
      ((sheafCompose (ProEt.topology T) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
        (SpTowerShriek.tau l E T n))).map (B m).hom

/-- All signed multiplication/contraction maps on a finite Tate line. They encode the
reassociations used in twisting an arbitrary tower, with mixed signs and the unit cases.
Source: blueprint gamma proof (2), twist reassociations
(blueprint: lem-pur-tower-operations-ground-field-retagging). -/
abbrev SpEllTwistProducts (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (T : Scheme.{u}) (n : ℕ) :=
  ∀ a b : ℤ, (SheafOfModules.siteSheafTensorRight.{u, u + 1, u + 1, u + 1}
    (spEllTwistLine l E T n b)).obj
    (spEllTwistLine l E T n a) ≅ spEllTwistLine l E T n (a + b)

private theorem signedComparison_ext (T : Scheme.{u})
    {R S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (α : R ⟶ S)
    (L : SheafOfModules.{u + 1}
      ((sheafCompose (ProEt.topology T) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R))
    (K : SheafOfModules.{u + 1}
      ((sheafCompose (ProEt.topology T) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S))
    (B C : ∀ m : ℤ,
      SheafOfModules.changeOfRingsOfUniverses.{u, u + 1, u + 1, u + 1}
        α (SheafOfModules.signedLinePower.{u + 1, u, u + 1} L m) ≅
        SheafOfModules.signedLinePower.{u + 1, u, u + 1} K m)
    (hB : SheafOfModules.SignedLineComparisonNormalized.{u + 1, u, u + 1}
      α L K (B 1) B)
    (hC : SheafOfModules.SignedLineComparisonNormalized.{u + 1, u, u + 1}
      α L K (C 1) C) (h1 : B 1 = C 1) : B = C := by
  have hpos (n : ℕ) : B (.ofNat n) = C (.ofNat n) := by
    induction n using Nat.twoStepInduction with
    | zero => exact Iso.ext (hB.1.trans hC.1.symm)
    | one => exact h1
    | more n _ih ih =>
      apply Iso.ext
      apply SheafOfModules.scalarExtension_tensor_hom_ext.{u + 1, u, u + 1} α
        (SheafOfModules.scalarTensorPower.{u + 1, u, u + 1} R L (n + 1)) L
      intro U s x y
      erw [hB.2.2.1 n U s x y, hC.2.2.1 n U s x y]
      rw [ih, h1]
  funext m
  cases m with
  | ofNat n => exact hpos n
  | negSucc n =>
    apply Iso.ext
    rw [hB.2.2.2 n, hC.2.2.2 n, hpos (n + 1)]

private theorem ellComparison_ext (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (T : Scheme.{u}) (n : ℕ)
    (B C : SpEllTwistComparisons l E T n)
    (hB : SpEllTwistComparisonsNormalized l E T n B)
    (hC : SpEllTwistComparisonsNormalized l E T n C) : B = C := by
  have h1 : B 1 = C 1 := by
    apply Iso.ext
    apply SheafOfModules.scalarExtensionTower_hom_ext.{u + 1, u, u + 1, u + 1}
      (spEllTwistQuotient l E T (n + 1)) (SpTowerShriek.tau l E T n)
      (purTwistIntegralOne T l E)
    intro U s t x
    exact (hB.1 U s t x).trans (hC.1 U s t x).symm
  apply signedComparison_ext T (SpTowerShriek.tau l E T n)
    (spEllTwistOne l E T (n + 1)) (spEllTwistOne l E T n) B C hB.2 hC.2 h1

private theorem ellTwist_rank (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (T : Scheme.{u}) (n : ℕ)
    [∀ x : T, Invertible (l : T.residueField x)] :
    (spEllTwistOne l E T n).IsFiniteLocallyFreeOfRank 1 := by
  obtain ⟨e, he, hell⟩ := spEllIdeal_eq_uniformizer_pow l E
  have hpos : 1 ≤ e * (n + 1) :=
    (Nat.succ_pos n).trans_le (Nat.le_mul_of_pos_left (n + 1) he)
  have hpow : spEllIdeal l E ^ (n + 1) =
      Padic.coefficientExtensionIdeal l E (e * (n + 1) - 1 + 1) := by
    rw [Nat.sub_add_cancel hpos]
    unfold Padic.coefficientExtensionIdeal
    rw [hell, pow_mul]
  let M (I : Ideal (Padic.coefficientExtensionIntegers l E)) :=
    SheafOfModules.changeOfRingsOfUniverses.{u, u + 1, u + 1, u + 1}
      ((constantSheaf (ProEt.topology T) CommRingCat.{u + 1}).map
        (CommRingCat.ofHom (ULift.ringEquiv.{u, u + 1}.symm.toRingHom.comp
          ((Ideal.Quotient.mk I).comp ULift.ringEquiv.{u, u + 1}.toRingHom))))
      (purTwistIntegralOne T l E)
  change (M (spEllIdeal l E ^ (n + 1))).IsFiniteLocallyFreeOfRank 1
  rw [hpow]
  exact ((pur_twist_sheaf_locally_free.{u, 0} T l E).2.2.1.2.2.2
    (e * (n + 1) - 1)).2.1

private theorem ellTwist_cover (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (T : Scheme.{u}) (n : ℕ)
    [∀ x : T, Invertible (l : T.residueField x)] :
    ∃ (I : Type (u + 1)) (U : I → T.ProEt), (ProEt.topology T).CoversTop U ∧
      ∀ i, Nonempty ((spEllTwistOne l E T n).over (U i) ≅ SheafOfModules.unit.{u, u + 1, u + 1}
        (((sheafCompose (ProEt.topology T) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
          (SpTowerShriek.B l E T n)).over (U i))) := by
  classical
  let := ellTwist_rank l E T n
  obtain ⟨I, U, hU, e⟩ :=
    (SheafOfModules.isFiniteLocallyFreeOfRank_iff_exists_over_iso_free.{u + 1, u, u + 1}
      (M := spEllTwistOne l E T n) (r := 1)).mp inferInstance
  exact ⟨I, U, hU, fun i ↦
    ⟨(e i).some ≪≫ SheafOfModules.freeUniqueIso.{u + 1, u, u + 1} _⟩⟩

/-- All ordinary strict-tower constructions are identified by ground-field retagging.
The two geometrical inputs are separated finite-type k-schemes and a smooth separated
k-map of the specified pure relative dimension. The site, coefficient diagram and its
maps are identical before localization. The whole normalized system calculus is
identified, including its monoidal structure, representative models and coefficient
comparisons. Equality of Geometry identifies ordinary and derived adjunctions as well
as pullback-tensor maps; equality of Open identifies the termwise open adjunction.
The compact-support functor is identified after restriction to bounded-below inputs.
No reduction-isomorphism hypothesis appears anywhere.

Source: blueprint gamma proof (2)--(3), underlying-tower part of equivariance Step 1
(blueprint: lem-pur-tower-operations-ground-field-retagging).

Proof:
1. Over.map leaves the underlying scheme and every underlying arrow unchanged, and
   spGroundFieldRetagCompactification returns the original compactification. All fixed
   constructions in b and o therefore agree by reflexivity: sites, coefficients,
   towers, complexes, localizations, constructibility and Tor conditions, geometry,
   compact support, and open operations. The roots, integral line, quotient maps and
   signed finite lines likewise depend only on the underlying scheme.
2. For independently supplied normalized scalar comparisons, compare degree one on
   double scalar-extension pure sections using scalarExtensionTower_hom_ext. At zero
   use the prescribed unit, and induct on positive powers using the tensor pure-section
   extensionality lemma and the positive recursion. The negative normalization is a
   fixed composite involving the inverse positive comparison. Thus the entire families
   agree, and substitution identifies their semilinear transitions.
3. Write (ell) = (varpi)^e with e positive by the existing DVR calculation. The level-n
   ideal is then the uniformizer ideal at positive exponent e(n+1). Transporting the
   quotient-indexed scalar-extension construction identifies the finite line with the
   finite Tate line of pur_twist_sheaf_locally_free. The prime ell is invertible in all
   residue fields, since it is a unit in the stalks of a scheme over k. Rank-one local
   freeness supplies a covering by trivializations with the scalar unit. Apply
   existsUnique_signedLineProduct to identify the two normalized product families.
   This argument also covers empty schemes and n=0. -/
theorem sp_tower_operations_ground_field_retagging
    (P : PurityFiniteSetting.{u}) (σ : P.field.k ≃ₐ[P.field.k₀] P.field.k)
    (X Y : Over (Spec (CommRingCat.of P.field.k))) (f : X ⟶ Y) (d : ℕ)
    [IsSeparated X.hom] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [IsSeparated Y.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
    [IsSeparated f.left] [SmoothOfRelativeDimension d f.left]
    (b : SpTowerShriek.Base P.coefficients.l P.extension)
    (o : SpTowerShriek.Operations P.coefficients.l P.extension b)
    (c : Compactification f.left) :
    (∀ (T : Over (Spec (CommRingCat.of P.field.k))), T = X ∨ T = Y →
      ((spGroundFieldRetag P σ).obj T).left.ProEt = T.left.ProEt ∧
      HEq (ProEt.topology ((spGroundFieldRetag P σ).obj T).left)
        (ProEt.topology T.left) ∧
      HEq (spCoefficientRings P.coefficients.l P.extension
        ((spGroundFieldRetag P σ).obj T).left)
        (spCoefficientRings P.coefficients.l P.extension T.left) ∧
      HEq (spCoefficientPresheaf P.coefficients.l P.extension
        ((spGroundFieldRetag P σ).obj T).left)
        (spCoefficientPresheaf P.coefficients.l P.extension T.left) ∧
      spCoefficientTowers P.coefficients.l P.extension
        ((spGroundFieldRetag P σ).obj T).left =
        spCoefficientTowers P.coefficients.l P.extension T.left ∧
      CochainComplex (spCoefficientTowers P.coefficients.l P.extension
        ((spGroundFieldRetag P σ).obj T).left) ℤ =
        CochainComplex (spCoefficientTowers P.coefficients.l P.extension T.left) ℤ ∧
      HEq (HomologicalComplex.quasiIso
        (spCoefficientTowers P.coefficients.l P.extension
          ((spGroundFieldRetag P σ).obj T).left) (ComplexShape.up ℤ))
        (HomologicalComplex.quasiIso
          (spCoefficientTowers P.coefficients.l P.extension T.left) (ComplexShape.up ℤ)) ∧
      HEq (b.calculus ((spGroundFieldRetag P σ).obj T).left) (b.calculus T.left) ∧
      (∀ A : SpCoefficientTowersAbelian P.coefficients.l P.extension T.left,
        spDerivedCoefficientTowers P.coefficients.l P.extension
          ((spGroundFieldRetag P σ).obj T).left A =
          spDerivedCoefficientTowers P.coefficients.l P.extension T.left A ∧
        HEq (spConstructibleTorTowers P.coefficients.l P.extension
          ((spGroundFieldRetag P σ).obj T).left A)
          (spConstructibleTorTowers P.coefficients.l P.extension T.left A) ∧
        HEq (spConstructibleTorTowers P.coefficients.l P.extension
          ((spGroundFieldRetag P σ).obj T).left A).ι
          (spConstructibleTorTowers P.coefficients.l P.extension T.left A).ι) ∧
      HEq (proEtaleRootsOfUnityTower ((spGroundFieldRetag P σ).obj T).left
        P.coefficients.l Fact.out)
        (proEtaleRootsOfUnityTower T.left P.coefficients.l Fact.out) ∧
      HEq (purTwistIntegralOne ((spGroundFieldRetag P σ).obj T).left
        P.coefficients.l P.extension)
        (purTwistIntegralOne T.left P.coefficients.l P.extension) ∧
      (∀ n : ℕ,
        HEq (spEllTwistQuotient P.coefficients.l P.extension
          ((spGroundFieldRetag P σ).obj T).left n)
          (spEllTwistQuotient P.coefficients.l P.extension T.left n)) ∧
      (∀ (n : ℕ) (m : ℤ),
        HEq (spEllTwistLine P.coefficients.l P.extension
          ((spGroundFieldRetag P σ).obj T).left n m)
          (spEllTwistLine P.coefficients.l P.extension T.left n m)) ∧
      (∀ (n : ℕ)
        (Bσ : SpEllTwistComparisons P.coefficients.l P.extension
          ((spGroundFieldRetag P σ).obj T).left n)
        (B : SpEllTwistComparisons P.coefficients.l P.extension T.left n),
        SpEllTwistComparisonsNormalized P.coefficients.l P.extension
          ((spGroundFieldRetag P σ).obj T).left n Bσ →
        SpEllTwistComparisonsNormalized P.coefficients.l P.extension T.left n B →
        HEq Bσ B ∧ ∀ m : ℤ,
          HEq (spEllTwistTransition P.coefficients.l P.extension
            ((spGroundFieldRetag P σ).obj T).left n Bσ m)
            (spEllTwistTransition P.coefficients.l P.extension T.left n B m)) ∧
      (∀ (n : ℕ)
        (μσ : SpEllTwistProducts P.coefficients.l P.extension
          ((spGroundFieldRetag P σ).obj T).left n)
        (μ : SpEllTwistProducts P.coefficients.l P.extension T.left n),
        SheafOfModules.SignedLineProductNormalized.{u + 1, u, u + 1}
          (spEllTwistOne P.coefficients.l P.extension
            ((spGroundFieldRetag P σ).obj T).left n) μσ →
        SheafOfModules.SignedLineProductNormalized.{u + 1, u, u + 1}
          (spEllTwistOne P.coefficients.l P.extension T.left n) μ →
        HEq μσ μ)) ∧
    HEq (o.geometry ((spGroundFieldRetag P σ).map f).left) (o.geometry f.left) ∧
    HEq (SpTowerShriek.pull P.coefficients.l P.extension b
      (o.geometry ((spGroundFieldRetag P σ).map f).left))
      (SpTowerShriek.pull P.coefficients.l P.extension b (o.geometry f.left)) ∧
    HEq (DerivedCategory.Plus.ι
        (C := SpTowerShriek.S P.coefficients.l P.extension
          ((spGroundFieldRetag P σ).obj X).left) ⋙
      SpTowerShriek.F P.coefficients.l P.extension b o
        (spGroundFieldRetagCompactification P σ c))
      (DerivedCategory.Plus.ι (C := SpTowerShriek.S P.coefficients.l P.extension X.left) ⋙
        SpTowerShriek.F P.coefficients.l P.extension b o c) ∧
    HEq (o.openOp (spGroundFieldRetagCompactification P σ c).i) (o.openOp c.i) ∧
    HEq (o.geometry (spGroundFieldRetagCompactification P σ c).g) (o.geometry c.g) ∧
    HEq (o.openTensor (spGroundFieldRetagCompactification P σ c).i)
      (o.openTensor c.i) := by
  refine ⟨?_, HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl⟩
  intro T _hT
  refine ⟨rfl, HEq.rfl, HEq.rfl, HEq.rfl, rfl, rfl, HEq.rfl, HEq.rfl,
    ?_, HEq.rfl, HEq.rfl, ?_, ?_, ?_, ?_⟩
  · intro A
    exact ⟨rfl, HEq.rfl, HEq.rfl⟩
  · intro n
    exact HEq.rfl
  · intro n m
    exact HEq.rfl
  · intro n Bσ B hσ h
    have he := ellComparison_ext P.coefficients.l P.extension T.left n Bσ B hσ h
    cases he
    exact ⟨HEq.rfl, fun _ ↦ HEq.rfl⟩
  · intro n μσ μ hσ h
    classical
    let : ∀ x : T.left, Invertible (P.coefficients.l : T.left.residueField x) :=
      fun x ↦ (show IsUnit (P.coefficients.l : T.left.residueField x) by
        simpa only [map_natCast] using
          (P.coefficientPrime_isUnit_stalk T.left T.hom x).map (T.left.residue x).hom).invertible
    obtain ⟨ν, hν, huniq⟩ := SheafOfModules.existsUnique_signedLineProduct.{u + 1, u, u + 1}
      (spEllTwistOne P.coefficients.l P.extension T.left n)
      (ellTwist_cover P.coefficients.l P.extension T.left n)
    exact heq_of_eq ((huniq μσ hσ).trans (huniq μ h).symm)

end AlgebraicGeometry.ProEtale
