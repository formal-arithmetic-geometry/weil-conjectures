/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NF
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleRootsOfUnitySheaf
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import Sheaf.Paper.CompletedIntegralCoefficients
public import Sheaf.Paper.DerivedCompleteIntegralDetailed
public import Sheaf.AlgebraicGeometry.ProEtaleCohomologicalSupport
public import Mathlib.NumberTheory.Padics.RingHoms
public import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.Algebra.Category.Ring.Colimits
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree

import Sheaf.AlgebraicGeometry.FiniteEtaleTwistLine
import Sheaf.AlgebraicGeometry.Morphisms.RootSplitAwayCoverEtale
import Sheaf.AlgebraicGeometry.ProEtaleSiteComparison
import Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory
import Sheaf.CategoryTheory.RingedSiteModules
import WeilConjectures.AlgebraicGeometry.Sites.Kummer
import Sheaf.AlgebraicGeometry.ProEtaleAffineWeaklyContractibleCover
import Sheaf.AlgebraicGeometry.ProEtaleConstantSheafStalk
import Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import WeilConjectures.AlgebraicGeometry.SiteSheafificationSectionsLocal
import Mathlib.CategoryTheory.Limits.HasLimits
import Sheaf.Paper.ConstantCompletionEquivalence
import Sheaf.NumberTheory.Padics.ExtensionIntegersDvr
import Sheaf.CategoryTheory.LocalizedModuleAdjunctionExact
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import Sheaf.CategoryTheory.ExtensionByZeroPresheaf
import Sheaf.Algebra.Homology.KFlat
import Sheaf.Paper.IntegralDerivedReduction
import Sheaf.Paper.IntrinsicFiniteTorsionConstructibility
import Sheaf.AlgebraicGeometry.ProEtaleSurjectiveTowerDerivedLimit
import Sheaf.Paper.DerivedComplete
import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import Sheaf.CategoryTheory.LocalizedModuleExactForSystems
import Sheaf.Paper.ComparisonPullbackExact
import Sheaf.Paper.CompletedIntegralConstantMapOfUniverses
import Sheaf.Paper.DerivedCompleteOnSlices
import Sheaf.Paper.DerivedScalarExtensionRestrictionAdjunction
import Sheaf.Paper.SfIntegralConstructible
import WeilConjectures.AlgebraicGeometry.SiteSheafificationSectionsLocal

/-! # The integral Tate line on the pro-etale site

Source: Stacks Project, Tag 03PK; the coefficient-twist blueprint, order 1505
(blueprint: lem-pur-twist-sheaf-locally-free).

The auxiliary constructions retain the root tower, constant scalar extension and completed
scalar action. All choices below have a uniqueness specification. The tensor of commutative
ring sheaves is their pushout, so the coefficient comparison is a morphism of ring sheaves.
The natural-number level `n` means positive exponent `n + 1` throughout.

## Main definitions

* `purTwistZlOne` and `purTwistZlModule`: the root limit and its completed scalar action.
* `purTwistIntegralOne` and `purTwistIntegralModule`: the prescribed integral tensor line.
* `purTwistFiniteOne`: its prescribed ordinary finite-coefficient tensor reduction.
* `purTwistCoefficientComparison`: the canonical comparison of coefficient ring sheaves.

## Main statements

* `pur_twist_sheaf_locally_free`: all four local-freeness and derived-completeness clauses.
-/

@[expose] public section

set_option autoImplicit false

universe u d

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

/-- The original root tower's inverse limit, with no replacement of its underlying groups.
Source: Stacks Tag 03PK (blueprint: lem-pur-twist-sheaf-locally-free). -/
noncomputable def purTwistZlOne :=
  limit (proEtaleRootsOfUnityTower S l (Fact.out : l.Prime))

/-- Forgetting commutativity preserves sheafification on the small pro-etale site.
Source: Stacks Tag 00W1 (blueprint: lem-pur-twist-sheaf-locally-free).
Proof: sheafification uses covering-compatible families and their local equality relation.
Forgetting commutativity preserves the finite limits and filtered colimits in this
construction. Thus the same sheafification is obtained before and after forgetting. -/
theorem purTwistForgetPreservesSheafification :
    (ProEt.topology S).PreservesSheafification
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}) := by
  have : EssentiallySmall.{u + 1} S.ProEt := essentiallySmallSelf.{0} _
  constructor
  intro P Q f hf
  change (ProEt.topology S).W
    (Functor.whiskerRight f (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}))
  have hi : Presheaf.IsLocallyInjective (ProEt.topology S) f := hf.isLocallyInjective
  have hs : Presheaf.IsLocallySurjective (ProEt.topology S) f := hf.isLocallySurjective
  apply ((ProEt.topology S).W_iff_isLocallyBijective _).mpr
  constructor
  · exact ⟨fun x y h ↦ Presheaf.equalizerSieve_mem (ProEt.topology S) f x y h⟩
  · exact ⟨fun x ↦ Presheaf.imageSieve_mem (ProEt.topology S) f x⟩

/-- The constant-ring comparison coming from commutation with forgetting commutativity.
Source: Stacks Tags 03CY and 03PK (blueprint: lem-pur-twist-sheaf-locally-free). -/
noncomputable def purTwistFiniteRingIso (n : ℕ) :
    purTwistRing S (purTwistFiniteRing S l n) ≅
      proEtaleRootsOfUnityCoefficientRing S (l ^ (n + 1)) :=
  letI := purTwistForgetPreservesSheafification S
  (constantCommuteCompose (ProEt.topology S)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).app _

/-- The recorded finite roots module, transported along the canonical coefficient comparison.
Source: Stacks Tags 03CY and 03PK (blueprint: lem-pur-twist-sheaf-locally-free). -/
noncomputable def purTwistRootsModule (n : ℕ) :=
  (SheafOfModules.restrictScalars (purTwistFiniteRingIso S l n).hom).obj
    (proEtaleRootsOfUnityModule S (l ^ (n + 1)) (pow_pos (Fact.out : l.Prime).pos _))

/-- The completed scalar action is determined coordinatewise on the root limit.
Source: coefficient-twist blueprint, order 1505 (blueprint: lem-pur-twist-sheaf-locally-free).
Proof: limits of abelian sheaves are sectionwise compatible tuples. Multiplication
of each root by its finite coefficient is compatible with reduction and the power
transition. All module identities and restriction identities hold coordinatewise.
Joint injectivity of the limit projections gives uniqueness of this module action. -/
theorem purTwistZlAction_existsUnique :
    ∃! M : ∀ U : S.ProEtᵒᵖ,
      Module ((purTwistZlCompletion S l).obj.obj U) ((purTwistZlOne S l).obj.obj U),
      (∀ ⦃U V : S.ProEtᵒᵖ⦄ (f : U ⟶ V)
        (a : (purTwistZlCompletion S l).obj.obj U) (x : (purTwistZlOne S l).obj.obj U),
        (purTwistZlOne S l).obj.map f (@SMul.smul _ _ (M U).toSMul a x) =
          @SMul.smul _ _ (M V).toSMul ((purTwistZlCompletion S l).obj.map f a)
            ((purTwistZlOne S l).obj.map f x)) ∧
      ∀ (n : ℕ) (U : S.ProEtᵒᵖ)
        (a : (purTwistZlCompletion S l).obj.obj U) (x : (purTwistZlOne S l).obj.obj U),
        (limit.π (proEtaleRootsOfUnityTower S l (Fact.out : l.Prime)) (op n)).hom.app U
          (@SMul.smul _ _ (M U).toSMul a x) =
        ((purTwistZlProjection S l n).hom.app U a) •
          (@id ((purTwistRootsModule S l n).val.obj U)
            ((limit.π (proEtaleRootsOfUnityTower S l (Fact.out : l.Prime)) (op n)).hom.app
              U x)) := by
  sorry

/-- The unique coordinatewise completed coefficient action.
Source: coefficient-twist blueprint, order 1505 (blueprint: lem-pur-twist-sheaf-locally-free). -/
@[instance_reducible]
noncomputable def purTwistZlAction := (purTwistZlAction_existsUnique S l).exists.choose

/-- The action commutes with restriction.
Source: Stacks Tag 03PK (blueprint: lem-pur-twist-sheaf-locally-free).
Proof: take the restriction clause of the defining unique coordinatewise action. -/
theorem purTwistZlAction_restriction ⦃U V : S.ProEtᵒᵖ⦄ (f : U ⟶ V)
    (a : (purTwistZlCompletion S l).obj.obj U) (x : (purTwistZlOne S l).obj.obj U) :
    (purTwistZlOne S l).obj.map f
      (@SMul.smul _ _ (purTwistZlAction S l U).toSMul a x) =
    @SMul.smul _ _ (purTwistZlAction S l V).toSMul
      ((purTwistZlCompletion S l).obj.map f a) ((purTwistZlOne S l).obj.map f x) := by
  exact (purTwistZlAction_existsUnique S l).exists.choose_spec.1 f a x

/-- `Z_l(1)` as a module over the completed coefficient sheaf, with unchanged root limit.
Source: Stacks Tag 03PK (blueprint: lem-pur-twist-sheaf-locally-free). -/
noncomputable def purTwistZlModule :
    SheafOfModules.{u + 1} (purTwistRing S (purTwistZlCompletion S l)) :=
  letI : ∀ U : S.ProEtᵒᵖ,
      Module ((purTwistRing S (purTwistZlCompletion S l)).obj.obj U)
        ((purTwistZlOne S l).obj.obj U) := purTwistZlAction S l
  ⟨PresheafOfModules.ofPresheaf
    (R := (purTwistRing S (purTwistZlCompletion S l)).obj) (purTwistZlOne S l).obj
    (purTwistZlAction_restriction S l), (purTwistZlOne S l).property⟩

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

/-- The integral Tate line is the prescribed scalar extension over the discrete constants.
Source: coefficient-twist blueprint, order 1505 (blueprint: lem-pur-twist-sheaf-locally-free). -/
noncomputable def purTwistIntegralOne :
    SheafOfModules.{u + 1} (purTwistRing S (purTwistIntegralConstant S l E)) :=
  SheafOfModules.changeOfRingsOfUniverses.{u, u + 1, u + 1, u + 1}
    (purTwistConstantIntegersMap S l E)
    ((SheafOfModules.restrictScalars.{u + 1}
      ((sheafCompose (ProEt.topology S) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
        (purTwistZlCompletionMap S l))).obj (purTwistZlModule S l))

/-- A pure tensor in the prescribed integral line, after sheafification.
Source: Stacks Tag 03EK (blueprint: lem-pur-twist-sheaf-locally-free). -/
noncomputable def purTwistIntegralTensor (U : S.ProEtᵒᵖ)
    (b : (purTwistIntegralConstant S l E).obj.obj U)
    (x : (purTwistZlModule S l).val.obj U) :
    (purTwistIntegralOne S l E).val.obj U :=
  (((PresheafOfModules.sheafificationAdjunction
    (𝟙 (purTwistRing S (purTwistIntegralConstant S l E)).obj)).unit.app
      (SheafOfModules.changeOfRingsPresheafOfUniverses.{u, u + 1, u + 1, u + 1}
        (purTwistConstantIntegersMap S l E)
        ((SheafOfModules.restrictScalars.{u + 1}
          ((sheafCompose (ProEt.topology S)
            (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
              (purTwistZlCompletionMap S l))).obj (purTwistZlModule S l)))).app U)
      (b ⊗ₜ[(purTwistZlConstant S l).obj.obj U,
        ((purTwistConstantIntegersMap S l E).hom.app U).hom] x)

/-- The completed action on the integral tensor is uniquely fixed on pure tensors.
Source: coefficient-twist blueprint, order 1505 (blueprint: lem-pur-twist-sheaf-locally-free).
Proof: the coefficient comparison identifies the completed ring with the ring-sheaf tensor.
Its action is `(a tensor b)(x tensor c) = (a*x) tensor (b*c)`. This respects balanced
relations and sheafifies. The section formulas below and local generation by pure tensors
prove uniqueness; restriction compatibility follows from the same formula. -/
theorem purTwistIntegralAction_existsUnique :
    ∃! M : ∀ U : S.ProEtᵒᵖ,
      Module ((WeilConjectures.completedIntegralCoefficientSheafUnrestricted l E S).obj.obj U)
        ((purTwistIntegralOne S l E).val.obj U),
      (∀ ⦃U V : S.ProEtᵒᵖ⦄ (f : U ⟶ V)
        (a : (WeilConjectures.completedIntegralCoefficientSheafUnrestricted l E S).obj.obj U)
        (x : (purTwistIntegralOne S l E).val.obj U),
        (purTwistIntegralOne S l E).val.map f (@SMul.smul _ _ (M U).toSMul a x) =
          @SMul.smul _ _ (M V).toSMul
            ((WeilConjectures.completedIntegralCoefficientSheafUnrestricted l E S).obj.map f a)
            ((purTwistIntegralOne S l E).val.map f x)) ∧
      (∀ (U : S.ProEtᵒᵖ) (b : (purTwistIntegralConstant S l E).obj.obj U)
        (x : (purTwistIntegralOne S l E).val.obj U),
        @SMul.smul _ _ (M U).toSMul
          ((purTwistIntegralCompletionMap S l E).hom.app U b) x = b • x) ∧
      ∀ (U : S.ProEtᵒᵖ) (a : (purTwistZlCompletion S l).obj.obj U)
        (b : (purTwistIntegralConstant S l E).obj.obj U)
        (x : (purTwistZlModule S l).val.obj U),
        @SMul.smul _ _ (M U).toSMul ((purTwistCompletedScalarMap S l E).hom.app U a)
          (purTwistIntegralTensor S l E U b x) =
        purTwistIntegralTensor S l E U b (a • x) := by
  sorry

/-- The unique action on the concrete integral tensor sheaf.
Source: coefficient-twist blueprint, order 1505 (blueprint: lem-pur-twist-sheaf-locally-free). -/
@[instance_reducible]
noncomputable def purTwistIntegralAction :=
  (purTwistIntegralAction_existsUnique S l E).exists.choose

/-- The integral action commutes with restriction.
Source: Stacks Tag 03EK (blueprint: lem-pur-twist-sheaf-locally-free).
Proof: take the restriction clause of the uniquely characterized action. -/
theorem purTwistIntegralAction_restriction ⦃U V : S.ProEtᵒᵖ⦄ (f : U ⟶ V)
    (a : (WeilConjectures.completedIntegralCoefficientSheafUnrestricted l E S).obj.obj U)
    (x : (purTwistIntegralOne S l E).val.obj U) :
    (purTwistIntegralOne S l E).val.map f
      (@SMul.smul _ _ (purTwistIntegralAction S l E U).toSMul a x) =
    @SMul.smul _ _ (purTwistIntegralAction S l E V).toSMul
      ((WeilConjectures.completedIntegralCoefficientSheafUnrestricted l E S).obj.map f a)
      ((purTwistIntegralOne S l E).val.map f x) := by
  exact (purTwistIntegralAction_existsUnique S l E).exists.choose_spec.1 f a x

/-- The prescribed integral tensor equipped with its canonical completed-ring action.
Source: coefficient-twist blueprint, order 1505 (blueprint: lem-pur-twist-sheaf-locally-free). -/
noncomputable def purTwistIntegralModule :
    SheafOfModules.{u + 1}
      (WeilConjectures.completedIntegralCoefficientSheafUnrestricted l E S) :=
  letI : ∀ U : S.ProEtᵒᵖ,
      Module ((WeilConjectures.completedIntegralCoefficientSheafUnrestricted l E S).obj.obj U)
        ((purTwistIntegralOne S l E).val.presheaf.obj U) := purTwistIntegralAction S l E
  ⟨PresheafOfModules.ofPresheaf
    (R := (WeilConjectures.completedIntegralCoefficientSheafUnrestricted l E S).obj)
    (purTwistIntegralOne S l E).val.presheaf
    (purTwistIntegralAction_restriction S l E), (purTwistIntegralOne S l E).isSheaf⟩

/-- The finite Tate line, exactly the ordinary constant-coefficient tensor in the node.
Source: coefficient-twist blueprint, order 1505 (blueprint: lem-pur-twist-sheaf-locally-free). -/
noncomputable def purTwistFiniteOne (n : ℕ) :
    SheafOfModules.{u + 1} (WeilConjectures.integralCoefficientSheaf l E S n) :=
  SheafOfModules.changeOfRingsOfUniverses.{u, u + 1, u + 1, u + 1}
    (purTwistIntegralQuotient S l E n)
    (purTwistIntegralOne S l E)

/-- All four properties of the concrete Tate lines, including the empty-scheme case.
Source: Stacks Project, Tag 03PK and Lemma 03RV; coefficient-twist blueprint, order 1505
(blueprint: lem-pur-twist-sheaf-locally-free).
Proof:
1. On affine opens the finite root scheme is etale, by
   lem-sbc-root-split-away-cover-etale. Use lem-asd-finite-etale-twist-line and the
   representable calculation for def-weil-pbc-site-comparison-morphism to transfer its
   trivializations to the pro-etale root sheaf. The comparison of constant finite
   coefficients in lem-sf-comparison-pullback-exact respects the scalar action.
2. Apply lem-amb-kummer-any-base on each test scheme to lift roots through the power
   transitions locally. The sheaf local-surjectivity criterion makes them epimorphisms.
3. Refine the level-one etale cover by
   lem-weil-pbc-proetale-affine-wcontractible-covering-family. On each weakly contractible
   member lift primitive roots recursively. Every lift stays primitive: its coefficient
   modulo l is a unit, hence its coefficient modulo every l-power is a unit. Constant
   sections and their equality can be checked locally by
   lem-weil-pbc-site-sheafification-sections-local and the constant-sheaf stalk theorem.
4. Take the compatible root trivializations to the inverse limit. Slice restriction
   commutes with sectionwise limits, by lem-weil-proetale-weakly-etale-localization.
   The coordinate action gives a completed coefficient line. The quotient clause of
   lem-weil-pbc-constant-completion-equivalence and the tensor-quotient formula identify
   its finite reductions with the roots sheaves.
5. The valuation-ring DVR theorem writes l as a unit times a positive uniformizer power.
   Lift a finite residue basis and use successive l-adic digit expansions and completeness
   to obtain finite generation over Z_l. Torsion freeness and
   lem-sc-dvr-fg-torsionfree-free give a finite basis.
6. Reduce that basis modulo l-powers and take limits. Uniformizer powers and l-powers are
   cofinal, so the canonical ring-sheaf tensor comparison is an isomorphism, including its
   multiplicative and unit structure. Its pure-tensor formula gives the completed action
   on the prescribed integral tensor sheaf, which is locally a line.
7. Both ordinary reductions are quotient by the same uniformizer power, hence coincide.
   Choose a finite l-power annihilating each coefficient quotient; its finite root
   trivialization is an etale trivialization of the finite Tate line. The geometric-point
   lifting and constant-stalk lemmas make its stalks finite.
8. The integral line placed in degree zero is K-flat: on its trivializing cover its tensor
   with any acyclic complex is that complex, and slice restriction is exact by
   lem-pur-site-restriction-module-adjunction-exact. Compute derived reduction on this
   representative using def-weil-integral-derived-reduction, obtaining the ordinary
   finite line in degree zero with the same quotient transition and augmentation maps.
9. The single stratum S witnesses constructibility of each finite reduction. Its support
   is contained in {0}; on a nonempty S a geometric stalk is the nonzero coefficient ring,
   so the support equals {0}. On the empty scheme every sheaf is zero and support is empty.
10. The finite reduction tower is surjective and its ordinary inverse limit is the
    integral line, checked on the same trivializing cover. Apply
    lem-weil-proetale-surjective-tower-derived-limit to its quotient maps to obtain the
    Roos triangle with the actual augmentation. This is def-weil-derived-complete.
11. All reductions are constructible with uniform amplitude [0,0], so the integral line
    belongs to def-weil-derived-complete-integral-detailed. -/
theorem pur_twist_sheaf_locally_free
    (S : Scheme.{u}) (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    [∀ x : S, Invertible (l : S.residueField x)] :
    (∀ n : ℕ,
      (∃ (I : Type (u + 1)) (U : I → S.ProEt)
        (f : ∀ i : I, U i ⟶ ProEt.mk (𝟙 S)),
        Presieve.ofArrows U f ∈ (ProEt.precoverage S).coverings _ ∧
        (∀ i : I, Etale (U i).hom) ∧
        ∀ i : I, Nonempty ((purTwistRootsModule S l n).over (U i) ≅
          (SheafOfModules.unit (purTwistRing S (purTwistFiniteRing S l n))).over (U i))) ∧
      (purTwistRootsModule S l n).IsFiniteLocallyFreeOfRank 1 ∧
      (∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S),
        Finite ((proEtaleGeometricStalk (C := AddCommGrpCat.{u + 1}) s
          (proEtaleRootsOfUnitySheaf S (l ^ (n + 1)))) : Type (u + 1))) ∧
      Epi (proEtaleRootsOfUnityTransition S (l ^ (n + 1)) (l ^ (n + 2))
        (pow_pos (Fact.out : l.Prime).pos _) (pow_pos (Fact.out : l.Prime).pos _)
        (pow_dvd_pow l (Nat.le_succ (n + 1))))) ∧
    ((∃ (I : Type (u + 1)) (U : I → S.ProEt)
        (f : ∀ i : I, U i ⟶ ProEt.mk (𝟙 S)),
        Presieve.ofArrows U f ∈ (ProEt.precoverage S).coverings _ ∧
        ∀ i : I, Nonempty ((purTwistZlModule S l).over (U i) ≅
          (SheafOfModules.unit (purTwistRing S (purTwistZlCompletion S l))).over (U i))) ∧
      (purTwistZlModule S l).IsFiniteLocallyFreeOfRank 1 ∧
      ∀ n : ℕ, Nonempty
        (SheafOfModules.changeOfRingsOfUniverses.{u, u + 1, u + 1, u + 1}
          (purTwistZlProjection S l n)
          (purTwistZlModule S l) ≅ purTwistRootsModule S l n)) ∧
    ((∃ k : ℕ, Nonempty (@Module.Basis (Fin k) ℤ_[l]
        (Padic.coefficientExtensionIntegers l E) _ _
        (Module.compHom (Padic.coefficientExtensionIntegers l E) (purTwistIntegersMap l E)))) ∧
      IsIso (purTwistCoefficientComparison S l E) ∧
      (purTwistIntegralModule S l E).IsFiniteLocallyFreeOfRank 1 ∧
      ∀ n : ℕ,
        Nonempty (SheafOfModules.changeOfRingsOfUniverses.{u, u + 1, u + 1, u + 1}
          (WeilConjectures.completedIntegralCommRingProjectionUnrestricted l E S n)
            (purTwistIntegralModule S l E) ≅ purTwistFiniteOne S l E n) ∧
        (purTwistFiniteOne S l E n).IsFiniteLocallyFreeOfRank 1 ∧
        IsLocallyConstantProEtaleModuleSheaf S (Padic.coefficientExtensionRing l E (n + 1))
          (purTwistFiniteOne S l E n) ∧
        ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S),
          Finite (proEtaleGeometricModuleStalk s
            (WeilConjectures.integralCoefficientCommRingSheaf l E S n)
            (purTwistFiniteOne S l E n))) ∧
    (∀ (D : WeilConjectures.FiniteFieldDatum.{d}) (hl : l ≠ D.p),
      (∀ n : ℕ,
        Nonempty ((WeilConjectures.integralDerivedReduction l E S D hl n).obj
          ((DerivedCategory.singleFunctor _ 0).obj (purTwistIntegralModule S l E)) ≅
            (DerivedCategory.singleFunctor _ 0).obj (purTwistFiniteOne S l E n)) ∧
        intrinsicFiniteTorsionConstructible l E (n + 1)
          (Nat.succ_le_succ (Nat.zero_le n)) S
          ((DerivedCategory.singleFunctor _ 0).obj (purTwistFiniteOne S l E n)) ∧
        proEtaleCohomologicalSupport
          ((DerivedCategory.singleFunctor _ 0).obj (purTwistFiniteOne S l E n)) ⊆ {0} ∧
        (Nonempty S → proEtaleCohomologicalSupport
          ((DerivedCategory.singleFunctor _ 0).obj (purTwistFiniteOne S l E n)) = {0})) ∧
      WeilConjectures.IsDerivedComplete l E S D hl
        ((DerivedCategory.singleFunctor _ 0).obj (purTwistIntegralModule S l E)) ∧
      WeilConjectures.boundedConstructibleDerivedCompleteIntegral D l hl E S
        ((DerivedCategory.singleFunctor _ 0).obj (purTwistIntegralModule S l E))) := by
  sorry

end AlgebraicGeometry.Scheme
