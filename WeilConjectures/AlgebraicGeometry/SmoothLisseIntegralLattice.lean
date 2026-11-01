/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
public import WeilConjectures.CategoryTheory.Ringed.RingedSectionLocalizationOfUniversesSupplement
public import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType

import WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
import WeilConjectures.CategoryTheory.Ringed.RingedSectionLocalizationOfUniversesSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.CategoryTheory.RingedSiteModules
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import WeilConjectures.AlgebraicGeometry.Galois.GaloisLisseRepresentations
import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Algebra.Module.Equiv
import Mathlib.Topology.CompactOpen
import Mathlib.LinearAlgebra.Basis.Defs
import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
import Mathlib.RingTheory.Nakayama
import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.Algebra.Module.Lattice
import Mathlib.GroupTheory.QuotientGroup.Finite
import WeilConjectures.NumberTheory.Padics.IntegersCosetBasis
import Mathlib.Topology.Algebra.Module.Compact
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.NumberTheory.Padics.ProperSpace
import WeilConjectures.AlgebraicGeometry.Integral.Lisse.IntegralLisseReductionEquivalence
import WeilConjectures.Mathlib.Topology.NoetherianSpace
import WeilConjectures.AlgebraicGeometry.CompletedLisse.LisseCompletedSystemData
import WeilConjectures.AlgebraicGeometry.Integral.Lisse.IntegralLisseReductionData
import WeilConjectures.AlgebraicGeometry.Adic.AdicLisseModuleSupplement
import Mathlib.CategoryTheory.Sites.Sheafification
import WeilConjectures.AlgebraicGeometry.CompletedLisse.LisseCompletedPointwiseComparison
import Mathlib.Tactic.Choose
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.FieldTheory.PurelyInseparable.Basic
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import WeilConjectures.AlgebraicGeometry.Regular
import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
import Mathlib.RingTheory.Flat.Basic

/-!
# Global integral lattices on smooth geometric fibres

Source: Bhatt--Scholze, Lemmas 7.4.7 and 7.4.10 and Proposition 6.8.4(1),(4);
Stacks Project, Tags 056T, 01VB and 0BQ3
(blueprint: lem-a1-smooth-lisse-integral-lattice).

The integral ring is the recorded inverse limit of finite constant coefficient sheaves.
The rational ring is its sheaf localization at the recorded uniformizer. A lattice is
an actual subobject of the restriction of the given rational sheaf. The normalization
on `1 ⊗ m` says that its rationalization isomorphism is induced by that inclusion.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open CategoryTheory.Functor
open scoped ChangeOfRings

namespace AlgebraicGeometry.ProEtale

variable (l : ℕ) [Fact l.Prime] (E : Type v) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (T : Scheme.{u})

/-- The uniformizer as a global section of the completed coefficient ring, obtained
from its constant section through the canonical quotient-cone map.
Source: Bhatt--Scholze, Section 6.8
(blueprint: lem-a1-smooth-lisse-integral-lattice). -/
def smoothLatticeUniformizerSection :
    ((WeilConjectures.completedIntegralCommRingSheafUnrestricted l E T).obj ⋙
      forget CommRingCat).sections :=
  (Functor.sectionsFunctor T.ProEtᵒᵖ).map
    (whiskerRight
      (whiskerRight
        (toSheafify (Scheme.ProEt.topology T)
          ((Functor.const T.ProEtᵒᵖ).obj
            (CommRingCat.of (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)))))
        (forget₂ CommRingCat.{max v (u + 1)} RingCat.{max v (u + 1)}) ≫
        (WeilConjectures.integralConstantToCompletionOfUniverses l E T).hom)
      (forget RingCat))
    ⟨fun _ ↦ ULift.up (Padic.coefficientExtensionUniformizer l E), fun _ ↦ rfl⟩

/-- The rational coefficient sheaf `B_T[1/varpi]`, by actual sheafified localization.
Source: Bhatt--Scholze, Definition 6.8.1 and Lemma 6.8.2(2)
(blueprint: lem-a1-smooth-lisse-integral-lattice). -/
def smoothLatticeRationalRing :
    Sheaf (Scheme.ProEt.topology T) CommRingCat.{max v (u + 1)} :=
  ringedLocalizationRingOfUniverses.{max v (u + 1), u + 1, u}
    (WeilConjectures.completedIntegralCommRingSheafUnrestricted l E T)
    (smoothLatticeUniformizerSection l E T)

/-- The canonical coefficient localization map, with no choice of rational realization.
Source: Bhatt--Scholze, Lemma 6.8.2(2)
(blueprint: lem-a1-smooth-lisse-integral-lattice). -/
def smoothLatticeCoefficientMap :
    WeilConjectures.completedIntegralCommRingSheafUnrestricted l E T ⟶
      smoothLatticeRationalRing l E T :=
  ringedLocalizationRingUnitOfUniverses.{max v (u + 1), u + 1, u}
    (WeilConjectures.completedIntegralCommRingSheafUnrestricted l E T)
    (smoothLatticeUniformizerSection l E T)

section LocalizationInjection

universe c d r

variable {C : Type c} [Category.{d} C] {J : GrothendieckTopology C}
  [HasSheafify J CommRingCat.{r}] [J.WEqualsLocallyBijective CommRingCat.{r}]
  [HasSheafify J AddCommGrpCat.{r}] [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  (R : Sheaf J CommRingCat.{r}) (s : (R.obj ⋙ forget CommRingCat).sections)

private theorem localizationCoefficient_injective
    (hs : ∀ U, Function.Injective (fun b : R.obj.obj U ↦ (show R.obj.obj U from s.val U) * b))
    (U : Cᵒᵖ) :
    Function.Injective ((ringedLocalizationRingUnitOfUniverses R s).hom.app U).hom := by
  intro x y hxy
  let P := ringedLocalizationRingPresheafOfUniverses R s
  have hz := Presheaf.equalizerSieve_mem J (toSheafify J P)
    ((algebraMap _ (ringedSectionLocalizationCarrierOfUniverses R s U)) x)
    ((algebraMap _ (ringedSectionLocalizationCarrierOfUniverses R s U)) y) hxy
  let F := R.obj ⋙ forget CommRingCat.{r}
  have hF : Presheaf.IsSheaf J F :=
    Presheaf.isSheaf_comp_of_isSheaf J R.obj (forget CommRingCat.{r}) R.property
  have heq : Presheaf.equalizerSieve (F := F) x y ∈ J U.unop := by
    apply J.superset_covering _ hz
    intro V f hf
    change F.map f.op x = F.map f.op y
    have hinj : Function.Injective
        (algebraMap (R.obj.obj (op V))
          (ringedSectionLocalizationCarrierOfUniverses R s (op V))) := by
      apply (IsLocalization.injective_iff_isRegular
        (M := Submonoid.powers (show R.obj.obj (op V) from s.val (op V)))).mpr
      rintro ⟨a, ⟨n, rfl⟩⟩
      apply IsRegular.pow
      refine ⟨hs (op V), ?_⟩
      intro a b h
      apply hs (op V)
      exact (mul_comm _ _).trans (h.trans (mul_comm _ _))
    apply hinj
    exact (congrArg (fun k ↦ k x)
      (ringedLocalizationRing_unit_naturalityOfUniverses R s f.op)).trans
        (hf.trans (congrArg (fun k ↦ k y)
          (ringedLocalizationRing_unit_naturalityOfUniverses R s f.op)).symm)
  exact (((isSheaf_iff_isSheaf_of_type _ _).mp hF).isSeparated _ heq).ext
    (fun _ _ h ↦ h)

end LocalizationInjection

section ScalarExtensionEmbedding

universe c d r

variable {C : Type c} [Category.{d} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
  [HasWeakSheafify J AddCommGrpCat.{r}]
  {R S : Sheaf J CommRingCat.{r}} (a : R ⟶ S)
  (M : SheafOfModules.{r} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
  (L : SheafOfModules.{r} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S))
  (e : SheafOfModules.changeOfRingsOfUniverses a M ≅ L)

variable [∀ U, HasWeakSheafify (J.over U) AddCommGrpCat.{r}]
  [∀ U, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{r}]

omit [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
  [HasWeakSheafify J AddCommGrpCat.{r}] in
end ScalarExtensionEmbedding

section CompletedRegular

universe c d r

private theorem quotient_transition_kills_annihilator
    {A : Type u} [CommRing A] [IsDomain A] (π : A) (hπ : π ≠ 0) (n : ℕ)
    (x : A ⧸ (Ideal.span {π}) ^ (n + 2))
    (hx : Ideal.Quotient.mk _ π * x = 0) :
    Ideal.Quotient.factorPow (Ideal.span {π}) (Nat.le_succ (n + 1)) x = 0 := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem, Ideal.span_singleton_pow,
    Ideal.mem_span_singleton, pow_succ, mul_comm (π ^ (n + 1)) π] at hx
  have ha : π ^ (n + 1) ∣ a := (mul_dvd_mul_iff_left hπ).mp hx
  change Ideal.Quotient.mk _ a = 0
  rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.span_singleton_pow,
    Ideal.mem_span_singleton]
  exact ha

private theorem constantSheaf_kills_annihilator
    {C : Type c} [Category.{d} C] (J : GrothendieckTopology C)
    [HasSheafify J CommRingCat.{r}] [J.WEqualsLocallyBijective CommRingCat.{r}]
    (A B : CommRingCat.{r}) (f : A ⟶ B) (p : A)
    (hf : ∀ a : A, p * a = 0 → f a = 0)
    (U : Cᵒᵖ) (x : ((constantSheaf J CommRingCat.{r}).obj A).obj.obj U)
    (hx : (show ((constantSheaf J CommRingCat.{r}).obj A).obj.obj U from
      (toSheafify J ((Functor.const Cᵒᵖ).obj A)).app U p) * x = 0) :
    (((constantSheaf J CommRingCat.{r}).map f).hom.app U) x = 0 := by
  let P := (Functor.const Cᵒᵖ).obj A
  let Q := (Functor.const Cᵒᵖ).obj B
  let F := (constantSheaf J CommRingCat.{r}).obj A
  let G := (constantSheaf J CommRingCat.{r}).obj B
  let a : P ⟶ F.obj := toSheafify J P
  let b : Q ⟶ G.obj := toSheafify J Q
  let t := (constantSheaf J CommRingCat.{r}).map f
  change a.app U p * x = 0 at hx
  let GF := G.obj ⋙ forget CommRingCat.{r}
  have hGF : Presheaf.IsSheaf J GF :=
    Presheaf.isSheaf_comp_of_isSheaf J G.obj (forget CommRingCat.{r}) G.property
  have hcover : Presheaf.equalizerSieve (F := GF) (t.hom.app U x) 0 ∈ J U.unop := by
    apply J.transitive (Presheaf.imageSieve_mem J a x)
    intro V g hg
    let y : A := Presheaf.localPreimage a x g hg
    have hy : a.app (op V) y = F.obj.map g.op x :=
      Presheaf.app_localPreimage a x g hg
    have hyzero : a.app (op V) (p * y) = a.app (op V) 0 := by
      rw [map_mul, map_zero, hy]
      have hp : F.obj.map g.op (a.app U p) = a.app (op V) p :=
        (NatTrans.naturality_apply a g.op p).symm
      rw [← hp, ← map_mul, hx, map_zero]
    apply J.superset_covering _ (Presheaf.equalizerSieve_mem J a (p * y) 0 hyzero)
    intro W h hh
    have hp : p * y = 0 := hh
    have hfy : f y = 0 := hf y hp
    have htb : t.hom.app (op W) (a.app (op W) y) = b.app (op W) (f y) :=
      (congrArg (fun k ↦ k.app (op W) y)
        (toSheafify_naturality J ((Functor.const Cᵒᵖ).map f))).symm
    change G.obj.map (h ≫ g).op (t.hom.app U x) = G.obj.map (h ≫ g).op 0
    rw [map_zero, ← NatTrans.naturality_apply t.hom]
    have hyh : F.obj.map (h ≫ g).op x = a.app (op W) y := by
      rw [op_comp, F.obj.map_comp, ConcreteCategory.comp_apply, ← hy]
      exact (NatTrans.naturality_apply a h.op y).symm
    rw [hyh, htb, hfy, map_zero]
  exact (((isSheaf_iff_isSheaf_of_type _ _).mp hGF).isSeparated _ hcover).ext
    (fun _ _ h ↦ h)

private theorem smoothLatticeUniformizer_ne_zero :
    Padic.coefficientExtensionUniformizer l E ≠ 0 := by
  have h := (Padic.extension_integers_dvr l E (Padic.coefficientExtensionAbsoluteValue l E)
    (spectralNorm_extends (K := ℚ_[l]) (L := E))).choose_spec.choose_spec
  have hm : Padic.coefficientExtensionMaximalIdeal l E ≠ ⊥ :=
    h.2.2.2.2.2.2.2.2.2.1
  have hg : Ideal.span ({Padic.coefficientExtensionUniformizer l E} :
      Set (Padic.coefficientExtensionIntegers l E)) =
        Padic.coefficientExtensionMaximalIdeal l E :=
    h.2.2.2.2.2.2.2.2.2.2.2.2.2.1.choose_spec
  intro he
  apply hm
  rw [← hg, he]
  simp

private theorem smoothLatticeUniformizer_regular
    (U : T.ProEtᵒᵖ) :
    Function.Injective (fun b :
      (WeilConjectures.completedIntegralCommRingSheafUnrestricted l E T).obj.obj U ↦
        (show (WeilConjectures.completedIntegralCommRingSheafUnrestricted l E T).obj.obj U
          from (smoothLatticeUniformizerSection l E T).val U) * b) := by
  let : EssentiallySmall.{max v (u + 1)} T.ProEt := essentiallySmallSelf _
  let : (Scheme.ProEt.topology T).WEqualsLocallyBijective
      CommRingCat.{max v (u + 1)} :=
    GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall _
  suffices hz : ∀ b :
      (WeilConjectures.completedIntegralCommRingSheafUnrestricted l E T).obj.obj U,
      (show (WeilConjectures.completedIntegralCommRingSheafUnrestricted l E T).obj.obj U
          from (smoothLatticeUniformizerSection l E T).val U) * b = 0 → b = 0 by
    intro a b hab
    apply sub_eq_zero.mp
    apply hz
    dsimp only at hab
    rw [mul_sub, hab, sub_self]
  intro b hb
  let D := WeilConjectures.integralCoefficientSheafSystem l E T
  let ev := sheafToPresheaf (Scheme.ProEt.topology T) RingCat.{max v (u + 1)} ⋙
    (evaluation T.ProEtᵒᵖ RingCat.{max v (u + 1)}).obj U
  apply Concrete.isLimit_ext (D ⋙ ev)
    (isLimitOfPreserves ev (limit.isLimit D)) b 0
  intro j
  obtain ⟨n⟩ := j
  let πn := ((limit.π D (op n)).hom.app U).hom
  let πs := ((limit.π D (op (n + 1))).hom.app U).hom
  have hp : πs ((smoothLatticeUniformizerSection l E T).val U) =
      (toSheafify (Scheme.ProEt.topology T)
        ((Functor.const T.ProEtᵒᵖ).obj (CommRingCat.of
          (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 2)))))).app U
            (ULift.up (Ideal.Quotient.mk _ (Padic.coefficientExtensionUniformizer l E))) := by
    change (((WeilConjectures.integralConstantToCompletionOfUniverses l E T ≫
      limit.π D (op (n + 1))).hom.app U)
        ((toSheafify (Scheme.ProEt.topology T)
          ((Functor.const T.ProEtᵒᵖ).obj (CommRingCat.of
            (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E))))).app U
              (ULift.up (Padic.coefficientExtensionUniformizer l E)))) = _
    rw [WeilConjectures.integralConstantToCompletionOfUniverses, limit.lift_π]
    let q : CommRingCat.of (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) ⟶
        CommRingCat.of (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 2))) :=
      CommRingCat.ofHom (ULift.ringEquiv.symm.toRingHom.comp
        ((Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 2))).comp
          ULift.ringEquiv.toRingHom))
    have he := toSheafify_naturality (Scheme.ProEt.topology T)
      ((Functor.const T.ProEtᵒᵖ).map q)
    exact congrArg (fun k ↦ (ConcreteCategory.hom k)
      (ULift.up (Padic.coefficientExtensionUniformizer l E)))
        (NatTrans.congr_app he U).symm
  have hz :
      ((WeilConjectures.integralCoefficientSheafTransition l E T n).hom.app U)
        (πs b) = 0 := by
    apply constantSheaf_kills_annihilator (Scheme.ProEt.topology T)
      (CommRingCat.of (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 2))))
      (CommRingCat.of (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1))))
      (CommRingCat.ofHom (ULift.ringEquiv.symm.toRingHom.comp
        ((Padic.coefficientExtensionTransition l E (n + 1)).comp
          ULift.ringEquiv.toRingHom)))
      (ULift.up (Ideal.Quotient.mk _ (Padic.coefficientExtensionUniformizer l E)))
    · intro a ha
      apply ULift.ext
      apply quotient_transition_kills_annihilator
        (Padic.coefficientExtensionUniformizer l E) (smoothLatticeUniformizer_ne_zero l E) n
      exact congrArg ULift.down ha
    · rw [← hp]
      exact (πs.map_mul _ _).symm.trans ((congrArg πs hb).trans πs.map_zero)
  have hw := congrArg (fun f ↦ f.hom.app U b)
    (limit.w D (homOfLE (Nat.le_succ n)).op)
  change _ = _
  change πn b = πn 0
  rw [map_zero]
  apply hw.symm.trans
  have hmap : D.map (homOfLE (Nat.le_succ n)).op =
      WeilConjectures.integralCoefficientSheafTransition l E T n := by
    simp only [D, WeilConjectures.integralCoefficientSheafSystem,
      Functor.ofOpSequence_map_homOfLE_succ]
  rw [hmap]
  exact hz

end CompletedRegular

set_option maxHeartbeats 800000 in
-- Elaborating the independent coefficient universes and localization tensor needs this budget.
end AlgebraicGeometry.ProEtale
