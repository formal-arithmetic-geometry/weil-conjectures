/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NF
-/
module

public import Sheaf.Paper.CompletedIntegralCoefficients
public import Mathlib.NumberTheory.Padics.RingHoms
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.Algebra.Category.Ring.Colimits
import Sheaf.Paper.CompletedIntegralConstantMapOfUniverses
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.CategoryTheory.Functor.EpiMono

/-! # Coefficient rings of the integral Tate twist

Source: coefficient-twist blueprint, order 1505.
(blueprint: def-pur-twist-coefficient-rings)

The constant and completed coefficient rings, their quotient projections, and the
canonical comparison form the coefficient data used before constructing the Tate line.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped ChangeOfRings
namespace AlgebraicGeometry.Scheme
variable (S : Scheme.{u}) (l : ℕ) [Fact l.Prime]

/-- The recorded small-model sheafification criterion at the actual coefficient size.
Source: Stacks Tag 00W1 (blueprint: lem-pur-twist-sheaf-locally-free). -/
noncomputable instance purTwistAbLocallyBijective :
    (ProEt.topology S).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
  WeilConjectures.integralCoefficientAbLocallyBijective.{u, u} S

/-- Forget commutativity of a coefficient sheaf, without changing its sections.
Source: Stacks Tag 03EK (blueprint: lem-pur-twist-sheaf-locally-free). -/
abbrev purTwistRing (R : Sheaf (ProEt.topology S) CommRingCat.{u + 1}) :=
  (sheafCompose (ProEt.topology S) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R

/-- Constant finite coefficients at positive level `n + 1`.
Source: Stacks Tag 03PK (blueprint: lem-pur-twist-sheaf-locally-free). -/
noncomputable abbrev purTwistFiniteRing (n : ℕ) :=
  (constantSheaf (ProEt.topology S) CommRingCat.{u + 1}).obj
    (CommRingCat.of (ULift.{u + 1} (ZMod (l ^ (n + 1)))))

/-- The constant discrete `Z_l` ring sheaf.
Source: coefficient-twist blueprint, order 1505 (blueprint: lem-pur-twist-sheaf-locally-free). -/
noncomputable abbrev purTwistZlConstant :=
  (constantSheaf (ProEt.topology S) CommRingCat.{u + 1}).obj
    (CommRingCat.of (ULift.{u + 1} ℤ_[l]))

/-- Reduction of constant finite coefficient rings.
Source: Stacks Tag 03PK (blueprint: lem-pur-twist-sheaf-locally-free). -/
noncomputable def purTwistFiniteTransition (n : ℕ) :
    purTwistFiniteRing S l (n + 1) ⟶ purTwistFiniteRing S l n :=
  (constantSheaf (ProEt.topology S) CommRingCat.{u + 1}).map
    (CommRingCat.ofHom (ULift.ringEquiv.symm.toRingHom.comp
      ((ZMod.castHom (pow_dvd_pow l (Nat.le_succ (n + 1))) (ZMod (l ^ (n + 1)))).comp
        ULift.ringEquiv.toRingHom)))

/-- The positive finite coefficient inverse system.
Source: Stacks Tag 03CO (blueprint: lem-pur-twist-sheaf-locally-free). -/
noncomputable def purTwistZlTower := Functor.ofOpSequence (purTwistFiniteTransition S l)

/-- The completed `Z_l` coefficient sheaf, as the specified inverse limit.
Source: Stacks Tag 03CO (blueprint: lem-pur-twist-sheaf-locally-free). -/
noncomputable def purTwistZlCompletion := limit (purTwistZlTower S l)

/-- The coefficient projection to exponent `n + 1`.
Source: Stacks Tag 03CO (blueprint: lem-pur-twist-sheaf-locally-free). -/
noncomputable def purTwistZlProjection (n : ℕ) :
    purTwistZlCompletion S l ⟶ purTwistFiniteRing S l n :=
  limit.π (purTwistZlTower S l) (op n)

/-- Constant p-adic reduction.
Source: Stacks Tag 03CO (blueprint: lem-pur-twist-sheaf-locally-free). -/
noncomputable def purTwistZlReduction (n : ℕ) :
    purTwistZlConstant S l ⟶ purTwistFiniteRing S l n :=
  (constantSheaf (ProEt.topology S) CommRingCat.{u + 1}).map
    (CommRingCat.ofHom (ULift.ringEquiv.symm.toRingHom.comp
      ((PadicInt.toZModPow (n + 1)).comp ULift.ringEquiv.toRingHom)))

/-- The completion map is uniquely fixed by all finite reductions.
Source: Stacks Tag 03CO (blueprint: lem-pur-twist-sheaf-locally-free).
Proof: the p-adic residue maps commute with reductions. They form a cone over the
positive quotient tower; its limit property gives the unique indicated morphism. -/
theorem purTwistZlCompletionMap_existsUnique :
    ∃! a : purTwistZlConstant S l ⟶ purTwistZlCompletion S l,
      ∀ n : ℕ, a ≫ purTwistZlProjection S l n = purTwistZlReduction S l n := by
  let c : Cone (purTwistZlTower S l) :=
    { pt := purTwistZlConstant S l
      π := NatTrans.ofOpSequence (purTwistZlReduction S l) (by
        intro n
        change 𝟙 _ ≫ _ = _
        rw [Category.id_comp]
        simp only [purTwistZlTower,
          Functor.ofOpSequence_map_homOfLE_succ]
        dsimp [purTwistZlReduction, purTwistFiniteTransition]
        rw [← Functor.map_comp]
        congr 1
        ext z
        exact DFunLike.congr_fun (PadicInt.zmod_cast_comp_toZModPow
          (n + 1) (n + 1 + 1) (Nat.le_succ _)).symm z.down) }
  refine ⟨limit.lift _ c, ?_, ?_⟩
  · intro n
    exact limit.lift_π c (op n)
  · intro a ha
    apply limit.hom_ext
    intro n
    exact (ha n.unop).trans (limit.lift_π c n).symm

/-- The actual constant-to-completed coefficient map, fixed by its residue projections.
Source: Stacks Tag 03CO (blueprint: lem-pur-twist-sheaf-locally-free). -/
noncomputable def purTwistZlCompletionMap :=
  (purTwistZlCompletionMap_existsUnique S l).exists.choose

variable (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The canonical `Z_l` inclusion into the extension's valuation ring is fixed in the field.
Source: coefficient-twist blueprint, order 1505 (blueprint: lem-pur-twist-sheaf-locally-free).
Proof: the spectral absolute value extends the p-adic norm, so the image of each
p-adic integer has norm at most one. It lies in the specified valuation subring.
Corestrict the field inclusion. Injectivity of the subring inclusion gives uniqueness. -/
theorem purTwistIntegersMap_existsUnique :
    ∃! i : ℤ_[l] →+* Padic.coefficientExtensionIntegers l E,
      ∀ z : ℤ_[l], (i z : E) = algebraMap ℚ_[l] E (z : ℚ_[l]) := by
  have hO := (Padic.extension_integers_dvr l E
    (Padic.coefficientExtensionAbsoluteValue l E)
    (spectralNorm_extends (K := ℚ_[l]) (L := E))).choose_spec.choose_spec.1
  let i : ℤ_[l] →+* Padic.coefficientExtensionIntegers l E :=
    ((algebraMap ℚ_[l] E).comp (algebraMap ℤ_[l] ℚ_[l])).codRestrict _ (by
      intro z
      apply (hO _).2
      change spectralNorm ℚ_[l] E (algebraMap ℚ_[l] E (z : ℚ_[l])) ≤ 1
      rw [spectralNorm_extends]
      exact z.property)
  refine ⟨i, fun z ↦ rfl, ?_⟩
  intro j hj
  ext z
  exact (hj z).trans rfl

/-- The canonical inclusion, chosen from its equality in the coefficient field.
Source: coefficient-twist blueprint, order 1505 (blueprint: lem-pur-twist-sheaf-locally-free). -/
noncomputable def purTwistIntegersMap := (purTwistIntegersMap_existsUnique l E).exists.choose

/-- The constant valuation-ring sheaf.
Source: coefficient-twist blueprint, order 1505 (blueprint: lem-pur-twist-sheaf-locally-free). -/
noncomputable abbrev purTwistIntegralConstant :=
  (constantSheaf (ProEt.topology S) CommRingCat.{u + 1}).obj
    (CommRingCat.of (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)))

/-- The constant scalar-extension map induced by the field inclusion.
Source: Stacks Tag 03EK (blueprint: lem-pur-twist-sheaf-locally-free). -/
noncomputable def purTwistConstantIntegersMap :
    purTwistZlConstant S l ⟶ purTwistIntegralConstant S l E :=
  (constantSheaf (ProEt.topology S) CommRingCat.{u + 1}).map
    (CommRingCat.ofHom (ULift.ringEquiv.symm.toRingHom.comp
      ((purTwistIntegersMap l E).comp ULift.ringEquiv.toRingHom)))

/-- The canonical quotient of the discrete valuation-ring sheaf.
Source: Stacks Tag 03EK (blueprint: lem-pur-twist-sheaf-locally-free). -/
noncomputable def purTwistIntegralQuotient (n : ℕ) :
    purTwistIntegralConstant S l E ⟶
      WeilConjectures.integralCoefficientCommRingSheaf l E S n :=
  (constantSheaf (ProEt.topology S) CommRingCat.{u + 1}).map
    (CommRingCat.ofHom (ULift.ringEquiv.symm.toRingHom.comp
      ((Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1))).comp
        ULift.ringEquiv.toRingHom)))

/-- The constant valuation ring maps canonically into its completion.
Source: Stacks Tag 03CO (blueprint: lem-pur-twist-sheaf-locally-free).
Proof: the quotient maps form a cone over the coefficient tower. Its limit property
produces a unique ring-sheaf morphism; forgetting commutativity changes no sections. -/
theorem purTwistIntegralCompletionMap_existsUnique :
    ∃! a : purTwistIntegralConstant S l E ⟶
      WeilConjectures.completedIntegralCommRingSheafUnrestricted l E S,
      ∀ n : ℕ, a ≫ WeilConjectures.completedIntegralCommRingProjectionUnrestricted l E S n =
        purTwistIntegralQuotient S l E n := by
  let F := sheafCompose (ProEt.topology S)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})
  let c : Cone (WeilConjectures.integralCoefficientSheafSystem l E S) :=
    { pt := F.obj (purTwistIntegralConstant S l E)
      π := NatTrans.ofOpSequence
        (fun n ↦ F.map (purTwistIntegralQuotient S l E n)) (by
          intro n
          change 𝟙 _ ≫ _ = _
          rw [Category.id_comp]
          simp only [WeilConjectures.integralCoefficientSheafSystem,
            Functor.ofOpSequence_map_homOfLE_succ]
          dsimp [F, purTwistIntegralQuotient,
            WeilConjectures.integralCoefficientSheafTransition]
          rw [← Functor.map_comp, ← Functor.map_comp]
          congr 1) }
  let a : purTwistIntegralConstant S l E ⟶
      WeilConjectures.completedIntegralCommRingSheafUnrestricted l E S :=
    F.preimage (limit.lift _ c)
  have ha : ∀ n : ℕ,
      a ≫ WeilConjectures.completedIntegralCommRingProjectionUnrestricted l E S n =
        purTwistIntegralQuotient S l E n := by
    intro n
    apply F.map_injective
    rw [Functor.map_comp]
    dsimp only [a]
    rw [Functor.map_preimage]
    exact limit.lift_π c (op n)
  refine ⟨a, ha, ?_⟩
  intro b hb
  apply F.map_injective
  apply limit.hom_ext
  intro n
  exact (F.map_comp _ _).symm.trans
    ((congrArg F.map ((hb n.unop).trans (ha n.unop).symm)).trans (F.map_comp _ _))

/-- The actual constant-to-completed valuation-ring map.
Source: Stacks Tag 03CO (blueprint: lem-pur-twist-sheaf-locally-free). -/
noncomputable def purTwistIntegralCompletionMap :=
  (purTwistIntegralCompletionMap_existsUnique S l E).exists.choose

/-- A completed scalar map is canonical when each finite projection factors through a
finite p-adic quotient with the specified constant residues. The index is allowed to depend
on the target quotient, as required for ramified extensions.
Source: coefficient-twist blueprint, order 1505 (blueprint: lem-pur-twist-sheaf-locally-free). -/
def IsPurTwistCompletedScalarMap
    (a : purTwistZlCompletion S l ⟶
      WeilConjectures.completedIntegralCommRingSheafUnrestricted l E S) : Prop :=
  ∀ n : ℕ, ∃ (k : ℕ) (q : ZMod (l ^ (k + 1)) →+* Padic.coefficientExtensionRing l E (n + 1)),
    (∀ z : ℤ_[l], q (PadicInt.toZModPow (k + 1) z) =
      Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1))
        (purTwistIntegersMap l E z)) ∧
    a ≫ WeilConjectures.completedIntegralCommRingProjectionUnrestricted l E S n =
      purTwistZlProjection S l k ≫
        (constantSheaf (ProEt.topology S) CommRingCat.{u + 1}).map
          (CommRingCat.ofHom (ULift.ringEquiv.symm.toRingHom.comp
            (q.comp ULift.ringEquiv.toRingHom)))

private theorem purTwistZlReduction_epi (n : ℕ) : Epi (purTwistZlReduction S l n) := by
  let q : CommRingCat.of (ULift.{u + 1} ℤ_[l]) ⟶
      CommRingCat.of (ULift.{u + 1} (ZMod (l ^ (n + 1)))) :=
    CommRingCat.ofHom (ULift.ringEquiv.symm.toRingHom.comp
      ((PadicInt.toZModPow (n + 1)).comp ULift.ringEquiv.toRingHom))
  have : Epi q := ConcreteCategory.epi_of_surjective q (by
    intro x
    obtain ⟨z, hz⟩ := ZMod.ringHom_surjective (PadicInt.toZModPow (n + 1)) x.down
    exact ⟨ULift.up z, congrArg ULift.up hz⟩)
  change Epi ((constantSheaf (ProEt.topology S) CommRingCat.{u + 1}).map q)
  let := (constantSheafAdj (ProEt.topology S) CommRingCat.{u + 1}
    (MorphismProperty.Over.mkIdTerminal _ _)).isLeftAdjoint
  infer_instance

private theorem purTwistZlFiniteFactor_ext
    {B : Sheaf (ProEt.topology S) CommRingCat.{u + 1}} (k m : ℕ)
    (f : purTwistFiniteRing S l k ⟶ B) (g : purTwistFiniteRing S l m ⟶ B)
    (h : purTwistZlReduction S l k ≫ f = purTwistZlReduction S l m ≫ g) :
    purTwistZlProjection S l k ≫ f = purTwistZlProjection S l m ≫ g := by
  let t := max k m
  let p (i : ℕ) (hi : i ≤ t) := (purTwistZlTower S l).map (homOfLE hi).op
  have hp (i : ℕ) (hi : i ≤ t) :
      purTwistZlProjection S l t ≫ p i hi = purTwistZlProjection S l i :=
    limit.w (purTwistZlTower S l) (homOfLE hi).op
  have hr (i : ℕ) (hi : i ≤ t) :
      purTwistZlReduction S l t ≫ p i hi = purTwistZlReduction S l i := by
    have hz (j : ℕ) := (purTwistZlCompletionMap_existsUnique S l).exists.choose_spec j
    change ∀ j, purTwistZlCompletionMap S l ≫ purTwistZlProjection S l j =
      purTwistZlReduction S l j at hz
    rw [← hz t, Category.assoc, hp, hz i]
  have : Epi (purTwistZlReduction S l t) := purTwistZlReduction_epi S l t
  have he : p k (le_max_left k m) ≫ f = p m (le_max_right k m) ≫ g := by
    apply (cancel_epi (purTwistZlReduction S l t)).mp
    simpa only [← Category.assoc, hr] using h
  rw [← hp k (le_max_left k m), ← hp m (le_max_right k m),
    Category.assoc, Category.assoc, he]

/-- The completed scalar map is uniquely determined by its finite quotient formulas.
Source: coefficient-twist blueprint, order 1505 (blueprint: lem-pur-twist-sheaf-locally-free).
Proof: write `l = unit * uniformizer^e` with positive ramification index. For each
positive target exponent choose a sufficiently large p-adic exponent. Quotient factorization
then gives `q`. The residue formulas make these maps independent of the choice and compatible
with transitions, so the limit property constructs the map. Surjectivity of p-adic reduction
and joint injectivity of completion projections prove uniqueness. -/
theorem purTwistCompletedScalarMap_existsUnique :
    ∃! a : purTwistZlCompletion S l ⟶
      WeilConjectures.completedIntegralCommRingSheafUnrestricted l E S,
      IsPurTwistCompletedScalarMap S l E a := by
  classical
  have h := (Padic.extension_integers_dvr l E
    (Padic.coefficientExtensionAbsoluteValue l E)
    (spectralNorm_extends (K := ℚ_[l]) (L := E))).choose_spec.choose_spec
  have hm : (l : Padic.coefficientExtensionIntegers l E) ∈
      Padic.coefficientExtensionMaximalIdeal l E := by
    apply (h.2.1 _).2
    change spectralNorm ℚ_[l] E (l : E) < 1
    rw [← map_natCast (algebraMap ℚ_[l] E), spectralNorm_extends]
    exact Padic.norm_p_lt_one
  have hgen : Ideal.span ({Padic.coefficientExtensionUniformizer l E} :
      Set (Padic.coefficientExtensionIntegers l E)) =
        Padic.coefficientExtensionMaximalIdeal l E :=
    h.2.2.2.2.2.2.2.2.2.2.2.2.2.1.choose_spec
  have hq (n : ℕ) : ∃ q : ZMod (l ^ (n + 1)) →+*
      Padic.coefficientExtensionRing l E (n + 1),
      ∀ z : ℤ_[l], q (PadicInt.toZModPow (n + 1) z) =
        Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1))
          (purTwistIntegersMap l E z) := by
    let g := (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1))).comp
      (purTwistIntegersMap l E)
    have hker : RingHom.ker (PadicInt.toZModPow (n + 1)) ≤ RingHom.ker g := by
      rw [PadicInt.ker_toZModPow, Ideal.span_le, Set.singleton_subset_iff]
      change Ideal.Quotient.mk _ ((purTwistIntegersMap l E) ((l : ℤ_[l]) ^ (n + 1))) = 0
      rw [map_pow, map_natCast, Ideal.Quotient.eq_zero_iff_mem]
      change (l : Padic.coefficientExtensionIntegers l E) ^ (n + 1) ∈
        Ideal.span ({Padic.coefficientExtensionUniformizer l E} :
          Set (Padic.coefficientExtensionIntegers l E)) ^ (n + 1)
      rw [hgen]
      exact Ideal.pow_mem_pow hm (n + 1)
    exact ⟨(PadicInt.toZModPow (n + 1)).liftOfSurjective
      (ZMod.ringHom_surjective _) ⟨g, hker⟩,
      fun z ↦ RingHom.liftOfSurjective_comp_apply _ _ _ z⟩
  choose q hq using hq
  let C (n : ℕ) : purTwistFiniteRing S l n ⟶
      WeilConjectures.integralCoefficientCommRingSheaf l E S n :=
    (constantSheaf (ProEt.topology S) CommRingCat.{u + 1}).map
      (CommRingCat.ofHom (ULift.ringEquiv.symm.toRingHom.comp
        ((q n).comp ULift.ringEquiv.toRingHom)))
  let T (n : ℕ) : WeilConjectures.integralCoefficientCommRingSheaf l E S (n + 1) ⟶
      WeilConjectures.integralCoefficientCommRingSheaf l E S n :=
    (constantSheaf (ProEt.topology S) CommRingCat.{u + 1}).map
      (CommRingCat.ofHom (ULift.ringEquiv.symm.toRingHom.comp
        ((Padic.coefficientExtensionTransition l E (n + 1)).comp ULift.ringEquiv.toRingHom)))
  have hconst (n : ℕ) : purTwistZlReduction S l n ≫ C n =
      purTwistConstantIntegersMap S l E ≫ purTwistIntegralQuotient S l E n := by
    dsimp [C, purTwistZlReduction, purTwistConstantIntegersMap, purTwistIntegralQuotient]
    rw [← Functor.map_comp, ← Functor.map_comp]
    congr 1
    ext z
    exact hq n z.down
  have hquo (n : ℕ) : purTwistIntegralQuotient S l E (n + 1) ≫ T n =
      purTwistIntegralQuotient S l E n := by
    dsimp [T, purTwistIntegralQuotient]
    rw [← Functor.map_comp]
    congr 1
  let b (n : ℕ) := purTwistZlProjection S l n ≫ C n
  have hb (n : ℕ) : b (n + 1) ≫ T n = b n := by
    dsimp only [b]
    rw [Category.assoc]
    apply purTwistZlFiniteFactor_ext
    rw [← Category.assoc, hconst, Category.assoc, hquo, hconst]
  let F := sheafCompose (ProEt.topology S)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})
  let c : Cone (WeilConjectures.integralCoefficientSheafSystem l E S) :=
    { pt := F.obj (purTwistZlCompletion S l)
      π := NatTrans.ofOpSequence (fun n ↦ F.map (b n)) (by
        intro n
        change 𝟙 _ ≫ _ = _
        rw [Category.id_comp]
        simp only [WeilConjectures.integralCoefficientSheafSystem,
          Functor.ofOpSequence_map_homOfLE_succ]
        change F.map (b n) = F.map (b (n + 1)) ≫ F.map (T n)
        rw [← Functor.map_comp, hb]) }
  let a : purTwistZlCompletion S l ⟶
      WeilConjectures.completedIntegralCommRingSheafUnrestricted l E S :=
    F.preimage (limit.lift _ c)
  have ha (n : ℕ) :
      a ≫ WeilConjectures.completedIntegralCommRingProjectionUnrestricted l E S n = b n := by
    apply F.map_injective
    rw [Functor.map_comp]
    dsimp only [a]
    rw [Functor.map_preimage]
    exact limit.lift_π c (op n)
  refine ⟨a, fun n ↦ ⟨n, q n, hq n, ha n⟩, ?_⟩
  intro a' ha'
  apply F.map_injective
  apply limit.hom_ext
  intro n
  have he : a' ≫ WeilConjectures.completedIntegralCommRingProjectionUnrestricted l E S n.unop =
      a ≫ WeilConjectures.completedIntegralCommRingProjectionUnrestricted l E S n.unop := by
    obtain ⟨k, q', hq', hc'⟩ := ha' n.unop
    rw [hc', ha]
    apply purTwistZlFiniteFactor_ext
    dsimp [C, purTwistZlReduction]
    rw [← Functor.map_comp, ← Functor.map_comp]
    congr 1
    ext z
    exact (hq' z.down).trans (hq n.unop z.down).symm
  exact (F.map_comp _ _).symm.trans ((congrArg F.map he).trans (F.map_comp _ _))

/-- The canonical completed scalar map, with its finite quotient characterization.
Source: coefficient-twist blueprint, order 1505 (blueprint: lem-pur-twist-sheaf-locally-free). -/
noncomputable def purTwistCompletedScalarMap :=
  (purTwistCompletedScalarMap_existsUnique S l E).exists.choose

/-- The two inclusions of the discrete p-adic ring agree.
Source: coefficient-twist blueprint, order 1505 (blueprint: lem-pur-twist-sheaf-locally-free).
Proof: compose with every finite projection and apply the specified constant-residue
formula; joint injectivity of limit projections then gives the displayed equality. -/
theorem purTwistCoefficientSquare :
    purTwistZlCompletionMap S l ≫ purTwistCompletedScalarMap S l E =
      purTwistConstantIntegersMap S l E ≫ purTwistIntegralCompletionMap S l E := by
  have hproj (n : ℕ) :
      (purTwistZlCompletionMap S l ≫ purTwistCompletedScalarMap S l E) ≫
          WeilConjectures.completedIntegralCommRingProjectionUnrestricted l E S n =
        (purTwistConstantIntegersMap S l E ≫ purTwistIntegralCompletionMap S l E) ≫
          WeilConjectures.completedIntegralCommRingProjectionUnrestricted l E S n := by
    obtain ⟨k, q, hq, hcomp⟩ :=
      (purTwistCompletedScalarMap_existsUnique S l E).exists.choose_spec n
    change purTwistCompletedScalarMap S l E ≫ _ = _ at hcomp
    have hzl := (purTwistZlCompletionMap_existsUnique S l).exists.choose_spec k
    change purTwistZlCompletionMap S l ≫ _ = _ at hzl
    have hint := (purTwistIntegralCompletionMap_existsUnique S l E).exists.choose_spec n
    change purTwistIntegralCompletionMap S l E ≫ _ = _ at hint
    rw [Category.assoc, hcomp, ← Category.assoc, hzl, Category.assoc, hint]
    dsimp [purTwistZlReduction, purTwistConstantIntegersMap, purTwistIntegralQuotient]
    rw [← Functor.map_comp, ← Functor.map_comp]
    congr 1
    ext z
    exact hq z.down
  let F := sheafCompose (ProEt.topology S)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})
  apply F.map_injective
  apply limit.hom_ext
  intro n
  exact (F.map_comp _ _).symm.trans ((congrArg F.map (hproj n.unop)).trans
    (F.map_comp _ _))

/-- The coefficient comparison is the canonical map from the ring-sheaf tensor (pushout).
Source: Stacks Tag 03EK (blueprint: lem-pur-twist-sheaf-locally-free). -/
noncomputable def purTwistCoefficientComparison :=
  pushout.desc (purTwistCompletedScalarMap S l E) (purTwistIntegralCompletionMap S l E)
    (purTwistCoefficientSquare S l E)


end AlgebraicGeometry.Scheme
