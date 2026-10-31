/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SixFunctorDatum
public import WeilConjectures.AlgebraicGeometry.FixedEtaleOriginWitness
public import WeilConjectures.AlgebraicGeometry.FiniteTorAmplitudeSites
public import WeilConjectures.AlgebraicGeometry.SfIntegralConstructible
public import WeilConjectures.AlgebraicGeometry.SfRationalizationKaroubi
public import WeilConjectures.AlgebraicGeometry.GeneralAlgebraicallyClosedCoefficients
public import WeilConjectures.AlgebraicGeometry.ExchangeProjectionSuppliedDomains
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import WeilConjectures.AlgebraicGeometry.FiniteRingConstructibleDerivedOrigin
import WeilConjectures.AlgebraicGeometry.FixProjectionCompactificationComparison
import WeilConjectures.AlgebraicGeometry.IntegralResidueTor
import WeilConjectures.AlgebraicGeometry.DirectImagesConstructible
import WeilConjectures.AlgebraicGeometry.ProEtaleConstantModuleConstructibility
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-! # Finite-Tor and witnessed inputs of the relative product

Source: current blueprint, sec-six-functors/sk-thm-sf-kunneth-relative,
typing of the displayed composite and its finite-Tor second-variable paragraph
(blueprint: lem-sf-relative-product-input-domains).

The lists below enumerate the actual objects, including both tensor orders and
all compact-support images. Field witnesses belong to integral presentations;
there is no reduction of a rational object to finite coefficients.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
universe u i a b c d
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures
namespace RelativeProductInputs

/-- The chosen scheme fibre product with its existing finite-type base structure.
Source: relative-product typing (blueprint: lem-sf-relative-product-input-domains). -/
def space {D : FiniteFieldDatum.{u}} {X Y B : SixFunctorSpace D}
    (f : X ⟶ B) (g : Y ⟶ B)
    [LocallyOfFiniteType g.hom.left] [QuasiCompact g.hom.left] : SixFunctorSpace D := by
  refine ⟨Over.mk (pullback.fst f.hom.left g.hom.left ≫ X.obj.hom), ?_, ?_⟩
  · change LocallyOfFiniteType (pullback.fst f.hom.left g.hom.left ≫ X.obj.hom)
    exact @locallyOfFiniteType_comp _ _ _ _ _ inferInstance X.property.1
  · change QuasiCompact (pullback.fst f.hom.left g.hom.left ≫ X.obj.hom)
    exact @quasiCompact_comp _ _ _ _ _ inferInstance X.property.2

/-- The first projection of the chosen fibre product, over the original base field.
Source: relative-product typing (blueprint: lem-sf-relative-product-input-domains). -/
def left {D : FiniteFieldDatum.{u}} {X Y B : SixFunctorSpace D}
    (f : X ⟶ B) (g : Y ⟶ B)
    [LocallyOfFiniteType g.hom.left] [QuasiCompact g.hom.left] : space f g ⟶ X :=
  ObjectProperty.homMk (Over.homMk (pullback.fst f.hom.left g.hom.left) rfl)

/-- The second projection with its canonical commutativity proof.
Source: relative-product typing (blueprint: lem-sf-relative-product-input-domains). -/
def right {D : FiniteFieldDatum.{u}} {X Y B : SixFunctorSpace D}
    (f : X ⟶ B) (g : Y ⟶ B)
    [LocallyOfFiniteType g.hom.left] [QuasiCompact g.hom.left] : space f g ⟶ Y :=
  ObjectProperty.homMk (Over.homMk (pullback.snd f.hom.left g.hom.left) (by
    change pullback.snd f.hom.left g.hom.left ≫ Y.obj.hom =
      pullback.fst f.hom.left g.hom.left ≫ X.obj.hom
    rw [← g.hom.w, ← Category.assoc, ← pullback.condition, Category.assoc, f.hom.w]))

/-- Exactly the relative-product inputs, their indicated images, and the two final tensors.
The first two entries retain the original inputs for the witnessed-domain assertion.
Source: all displayed objects in relative-product typing
(blueprint: lem-sf-relative-product-input-domains). -/
def objects {I : Type i} {A : I → Type a} {B X Y T : I}
    (pu : A X → A T) (pv : A Y → A T) (pg : A B → A Y)
    (sf : A X → A B) (sg : A Y → A B) (sv : A T → A Y) (sh : A T → A B)
    (tb : A B → A B → A B) (ty : A Y → A Y → A Y) (tt : A T → A T → A T)
    (K : A X) (L : A Y) : List (Σ Z : I, A Z) :=
  let P := pu K
  let V := pv L
  let Q := sf K
  let R := sv P
  let G := pg Q
  let H := tt P V
  [⟨X, K⟩, ⟨Y, L⟩, ⟨T, P⟩, ⟨T, V⟩, ⟨T, H⟩, ⟨B, Q⟩,
    ⟨Y, R⟩, ⟨Y, G⟩, ⟨Y, ty R L⟩, ⟨Y, ty G L⟩, ⟨Y, ty L G⟩,
    ⟨B, sh P⟩, ⟨B, sh V⟩, ⟨B, sh H⟩,
    ⟨B, sg R⟩, ⟨B, sg G⟩, ⟨B, sg (ty R L)⟩, ⟨B, sg (ty G L)⟩,
    ⟨B, sg (ty L G)⟩, ⟨B, sg L⟩, ⟨B, tb (sg L) Q⟩, ⟨B, tb Q (sg L)⟩]

/-- Instantiate the displayed list with a recorded construction stage and its tensor.
Source: relative-product typing (blueprint: lem-sf-relative-product-input-domains). -/
def stageObjects {D : FiniteFieldDatum.{u}} {A : SixFunctorSpace D → Type a}
    [∀ Z, Category.{b} (A Z)] (O : SixFunctorPushStage D A)
    (tensor : ∀ Z, A Z ⥤ A Z ⥤ A Z) {X Y B : SixFunctorSpace D}
    (f : X ⟶ B) (g : Y ⟶ B)
    [LocallyOfFiniteType g.hom.left] [QuasiCompact g.hom.left]
    (cf : Compactification f.hom.left) (cg : Compactification g.hom.left)
    (cv : Compactification (right f g).hom.left)
    (ch : Compactification ((left f g) ≫ f).hom.left) (K : A X) (L : A Y) :=
  objects (A := A) (B := B) (X := X) (Y := Y) (T := space f g)
    (O.pull (left f g)).obj (O.pull (right f g)).obj (O.pull g).obj
    (O.support f cf).obj (O.support g cg).obj (O.support (right f g) cv).obj
    (O.support ((left f g) ≫ f) ch).obj
    (fun M N ↦ ((tensor B).obj M).obj N)
    (fun M N ↦ ((tensor Y).obj M).obj N)
    (fun M N ↦ ((tensor (space f g)).obj M).obj N) K L

/-- Existence of a bounded constructible etale antecedent, retaining its comparison pair.
The inverse coefficient equivalence is the recorded section-normalized realization.
Source: Stacks Tags 09AK--09AL, relative-product typing
(blueprint: lem-sf-relative-product-input-domains). -/
def finiteWitness (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
    (E : Type u) [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] (n : ℕ) (hn : 1 ≤ n)
    (X : SixFunctorSpace D)
    (K : proEtaleDerivedCategory X.obj.left (Padic.coefficientExtensionRing C.l E n)) : Prop :=
  letI := Padic.finite_coefficientExtensionRing C.l E n hn
  ∃ F : DerivedCategory.Plus (Sheaf (ProEt.topology X.obj.left)
      (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionRing C.l E n)))),
    ∃ W : FixedEtaleOriginWitness X.obj.left
        (ULift.{u + 1, u} (Padic.coefficientExtensionRing C.l E n)) F,
      Nonempty (F.obj ≅ (sixFunctorFiniteRealization D C E n hn X).inverse.obj K) ∧
      Etale.DerivedCategory.isBoundedConstructible
        (ULift.{u + 1, u} (Padic.coefficientExtensionRing C.l E n)) X.obj.left W.complex.obj

/-- Finite witnesses of every reduction of the actual completed integral object.
No compatibility between the chosen antecedents at different levels is imposed.
Source: relative-product typing (blueprint: lem-sf-relative-product-input-domains). -/
def integralWitness (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
    (E : Type u) [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] (X : SixFunctorSpace D)
    (K : sfIntegralConstructibleCategory C.l E X.obj.left) : Prop :=
  ∀ m : ℕ, finiteWitness D C E (m + 1) (Nat.succ_le_succ (Nat.zero_le m)) X
    ((scalarReductionDerivedExtension C.l E X.obj.left m).obj K.obj)

/-- Compare two displayed lists through the actual coefficient-passage functors.
Each existential equality only identifies the scheme labels, not the coefficients.
Source: relative-product field-passage clause
(blueprint: lem-sf-relative-product-input-domains). -/
def presented {I : Type i} {A : I → Type a} {A' : I → Type c}
    [catA : ∀ Z, Category.{b} (A Z)] [catB : ∀ Z, Category.{d} (A' Z)]
    (F : ∀ Z, A Z ⥤ A' Z) (M : List (Σ Z, A Z)) (N : List (Σ Z, A' Z)) : Prop :=
  List.Forall₂ (fun M N ↦ ∃ e : M.1 = N.1,
    Nonempty ((F M.1).obj M.2 ≅ e.symm ▸ N.2)) M N

end RelativeProductInputs
end WeilConjectures

namespace WeilConjectures
namespace RelativeProductInputs

/-- The displayed finite-level objects, using ambient pullback, tensor and compact support.
In particular no preservation statement is assumed merely to form this list.
Source: relative-product typing (blueprint: lem-sf-relative-product-input-domains). -/
def finiteObjects (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
    (E : Type u) [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] (n : ℕ) (hn : 1 ≤ n)
    {X Y B : SixFunctorSpace D} (f : X ⟶ B) (g : Y ⟶ B)
    [LocallyOfFiniteType g.hom.left] [QuasiCompact g.hom.left]
    (cf : Compactification f.hom.left) (cg : Compactification g.hom.left)
    (cv : Compactification (right f g).hom.left)
    (ch : Compactification ((left f g) ≫ f).hom.left)
    (K : proEtaleDerivedCategory X.obj.left (Padic.coefficientExtensionRing C.l E n))
    (L : proEtaleDerivedCategory Y.obj.left (Padic.coefficientExtensionRing C.l E n)) :=
  objects
    (A := fun Z : SixFunctorSpace D ↦
      proEtaleDerivedCategory Z.obj.left (Padic.coefficientExtensionRing C.l E n))
    (B := B) (X := X) (Y := Y) (T := space f g)
    (sixFunctorFinitePullback D C E n hn (left f g)).obj
    (sixFunctorFinitePullback D C E n hn (right f g)).obj
    (sixFunctorFinitePullback D C E n hn g).obj
    (sixFunctorFiniteSupport D C E n hn f cf).obj
    (sixFunctorFiniteSupport D C E n hn g cg).obj
    (sixFunctorFiniteSupport D C E n hn (right f g) cv).obj
    (sixFunctorFiniteSupport D C E n hn ((left f g) ≫ f) ch).obj
    (fun M N ↦ (sixFunctorFiniteTensor D C E n hn B).obj (M, N))
    (fun M N ↦ (sixFunctorFiniteTensor D C E n hn Y).obj (M, N))
    (fun M N ↦ (sixFunctorFiniteTensor D C E n hn (space f g)).obj (M, N)) K L

/-- Integral presentation followed by rationalization and the actual common-stage embedding.
Source: relative-product coefficient passage
(blueprint: lem-sf-relative-product-input-domains). -/
def commonPassage (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
    (E₀ : Padic.FiniteCoefficientFields C.l C.Qbar) (Z : SixFunctorSpace D) :
    sfIntegralConstructibleCategory C.l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} C.l C.Qbar E₀) Z.obj.left ⥤
      generalAlgebraicallyClosedConstructibleCategory C.l C.Qbar Z.obj.left :=
  sfRationalConstructibleLocalization C.l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} C.l C.Qbar E₀) Z.obj.left ⋙
    GeneralAlgebraicallyClosedCoefficients.inclusion
      (l := C.l) (Ω := C.Qbar) (Y := Z.obj.left) E₀

end RelativeProductInputs

open RelativeProductInputs

attribute [-instance] IntegralHom.tensorLocalization IntegralHom.derivedCategory in
attribute [local irreducible] Padic.coefficientExtensionIdeal in
private theorem finite_origin
    (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
    (E : Type u) [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] (n : ℕ) (hn : 1 ≤ n)
    (X : SixFunctorSpace D)
    (K : proEtaleDerivedCategory X.obj.left (Padic.coefficientExtensionRing C.l E n))
    (hK : intrinsicFiniteTorsionConstructible.{u} C.l E n hn X.obj.left K) :
    finiteWitness D C E n hn X K := by
  classical
  let B := Padic.coefficientExtensionRing C.l E n
  let : Finite B := Padic.finite_coefficientExtensionRing C.l E n hn
  let : HasDerivedCategory.{u + 1}
      (Sheaf X.obj.left.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1, u} B))) :=
    HasDerivedCategory.ofIsGrothendieckAbelian _
  let : HasDerivedCategory.{u + 1}
      (Sheaf (ProEt.topology X.obj.left) (ModuleCat.{u + 1} (ULift.{u + 1, u} B))) :=
    HasDerivedCategory.ofIsGrothendieckAbelian _
  let ν := ProEtale.comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) X.obj.left
  let R := sfIntrinsicDerivedEquivalence X.obj.left B
  have hb : ∃ a b : ℤ, a ≤ b ∧ ∀ q : ℤ, (q < a ∨ b < q) →
      IsZero ((DerivedCategory.homologyFunctor
        (proEtaleRingModules.{u} X.obj.left (proEtaleConstantRing X.obj.left B)) q).obj K) := by
    obtain ⟨a, ha⟩ := hK.1.bddBelow
    obtain ⟨b, hb⟩ := hK.1.bddAbove
    refine ⟨min a b, b, min_le_right _ _, ?_⟩
    intro q hq
    by_contra hz
    rcases hq with hq | hq
    · exact (not_lt_of_ge (ha hz)) (lt_of_lt_of_le hq (min_le_left _ _))
    · exact (not_lt_of_ge (hb hz)) hq
  obtain ⟨J, ⟨eJ⟩⟩ := (finiteRing_constructibleDerived_origin X.obj.left B).2.2.1 K
    |>.mpr ⟨hK.2, hb⟩
  let : (sfIntrinsicModuleEquivalence X.obj.left B).functor.Additive :=
    inferInstanceAs (ProEtale.finiteCoefficientIntrinsicRealization X.obj.left B).Additive
  let : Category.{u + 1}
      (Etale.DerivedCategoryModule (ULift.{u + 1, u} B) X.obj.left) :=
    instCategoryDerivedCategory _
  let : Category.{u + 1}
      (DerivedCategory (Sheaf (ProEt.topology X.obj.left)
        (ModuleCat.{u + 1} (ULift.{u + 1, u} B)))) := instCategoryDerivedCategory _
  let ecomp : (ProEtale.finiteCoefficientIntrinsicDerivedComparison X.obj.left B).obj J.obj ≅
      (ProEtale.finiteCoefficientIntrinsicRealization X.obj.left B).mapDerivedCategory.obj
        (ν.mapDerivedCategory.obj J.obj) :=
    Iso.app
      (C := DerivedCategory (Sheaf X.obj.left.smallEtaleTopology
        (ModuleCat.{u + 1} (ULift.{u + 1, u} B))))
      (D := proEtaleDerivedCategory X.obj.left B)
      (Functor.mapDerivedCategoryCompIso
        (C := Sheaf X.obj.left.smallEtaleTopology
          (ModuleCat.{u + 1} (ULift.{u + 1, u} B)))
        (D := Sheaf (ProEt.topology X.obj.left)
          (ModuleCat.{u + 1} (ULift.{u + 1, u} B)))
        (E := proEtaleRingModules X.obj.left (proEtaleConstantRing X.obj.left B))
        ν (ProEtale.finiteCoefficientIntrinsicRealization X.obj.left B)) J.obj
  let ec : R.functor.obj (ν.mapDerivedCategory.obj J.obj) ≅ K := ecomp.symm ≪≫ eJ
  let e : ν.mapDerivedCategory.obj J.obj ≅ R.inverse.obj K :=
    R.unitIso.app _ ≪≫ R.inverse.mapIso ec
  obtain ⟨a, b, _, hz⟩ := J.property.2
  let Jplus : DerivedCategory.Plus
      (Sheaf X.obj.left.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1, u} B))) :=
    ⟨J.obj, a, (DerivedCategory.isGE_iff J.obj a).mpr (fun i hi ↦ hz i (.inl hi))⟩
  let F := ν.mapDerivedCategoryPlus.obj Jplus
  exact ⟨F, ⟨Jplus, (ν.mapDerivedCategoryPlusCompatibility.app Jplus).symm⟩,
    ⟨ν.mapDerivedCategoryPlusCompatibility.app Jplus ≪≫ e⟩, J.property⟩

attribute [-instance] IntegralHom.tensorLocalization IntegralHom.derivedCategory in
private theorem integral_domains
    (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
    (E : Type u) [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] (X : SixFunctorSpace D)
    (K : sfIntegralConstructibleCategory C.l E X.obj.left) :
    finiteTorConstructibleIntegral C.l E X.obj.left K.obj ∧ integralWitness D C E X K := by
  let : ∀ x : X.obj.left, Invertible (C.l : X.obj.left.residueField x) := fun x ↦ by
    let φ : D.k →+* X.obj.left.residueField x :=
      (X.obj.left.evaluation ⊤ x (by trivial)).hom.comp
        (X.obj.hom.appTop.hom.comp (Scheme.ΓSpecIso (.of D.k)).inv.hom)
    exact (show IsUnit (C.l : X.obj.left.residueField x) from by
      simpa only [map_natCast] using
        (finiteFieldDatumPrimeUnit D C.l C.different).map φ).invertible
  refine ⟨?_, ?_⟩
  · rw [← (integral_residue_tor D C.l C.different E X.obj.left).2]
    exact K.property
  · intro m
    obtain ⟨a, b, hab, h⟩ := K.property.2
    exact finite_origin D C E (m + 1) (Nat.succ_pos m) X _ (h m).1

attribute [-instance] IntegralHom.tensorLocalization IntegralHom.derivedCategory in
private theorem finite_tor_iso
    (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
    (E : Type u) [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] (n : ℕ) (hn : 1 ≤ n) (X : SixFunctorSpace D)
    {K L : proEtaleDerivedCategory X.obj.left (Padic.coefficientExtensionRing C.l E n)}
    (e : K ≅ L) (hK : finiteTorConstructible C.l E n hn X.obj.left K) :
    finiteTorConstructible C.l E n hn X.obj.left L := by
  let : Finite (Padic.coefficientExtensionRing C.l E n) :=
    Padic.finite_coefficientExtensionRing C.l E n hn
  refine ⟨?_, ?_⟩
  · refine ⟨hK.1.1.subset (fun i hi hz ↦ hi
        (hz.of_iso ((DerivedCategory.homologyFunctor
          (proEtaleRingModules.{u} X.obj.left
            (proEtaleConstantRing X.obj.left
              (Padic.coefficientExtensionRing C.l E n))) i).mapIso e).symm)), ?_⟩
    intro i
    have hc := hK.1.2 i
    rw [proEtaleModuleRestriction_constructible_iff] at hc ⊢
    exact ProEtale.isConstructible_of_iso
      ((proEtaleModuleRestriction X.obj.left _).mapIso
        ((DerivedCategory.homologyFunctor
          (proEtaleRingModules X.obj.left
            (proEtaleConstantRing X.obj.left
              (Padic.coefficientExtensionRing C.l E n))) i).mapIso e))
      hc
  · obtain ⟨a, b, ht⟩ := hK.2
    refine ⟨a, b, ht.1, ?_⟩
    intro M P hM f hf hP N i hi
    exact ht.2 M P (hM.map (fun j ↦ j ≪≫ e.symm)) f hf hP N i hi

attribute [-instance] IntegralHom.tensorLocalization IntegralHom.derivedCategory in
private theorem finite_pull
    (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
    (E : Type u) [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] (n : ℕ) (hn : 1 ≤ n)
    (S : SixFunctorDatum D C E n hn) {X Y : SixFunctorSpace D}
    (f : X ⟶ Y) [IsSeparated f.hom.left]
    (K : proEtaleDerivedCategory Y.obj.left (Padic.coefficientExtensionRing C.l E n))
    (hK : finiteTorConstructible C.l E n hn Y.obj.left K) :
    finiteTorConstructible C.l E n hn X.obj.left
      ((sixFunctorFinitePullback D C E n hn f).obj K) := by
  exact finite_tor_iso D C E n hn X ((S.finitePullback f).app ⟨K, hK.1⟩)
    (S.finiteCoherence.pullDomain f ⟨K, hK.1⟩ hK)

attribute [-instance] IntegralHom.tensorLocalization IntegralHom.derivedCategory in
private theorem finite_support
    (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
    (E : Type u) [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] (n : ℕ) (hn : 1 ≤ n)
    (S : SixFunctorDatum D C E n hn) {X Y : SixFunctorSpace D}
    (f : X ⟶ Y) (c : Compactification f.hom.left)
    (K : proEtaleDerivedCategory X.obj.left (Padic.coefficientExtensionRing C.l E n))
    (hK : finiteTorConstructible C.l E n hn X.obj.left K) :
    finiteTorConstructible C.l E n hn Y.obj.left
      ((sixFunctorFiniteSupport D C E n hn f c).obj K) := by
  exact finite_tor_iso D C E n hn Y ((S.finiteSupport f c).app ⟨K, hK.1⟩)
    (S.finiteCoherence.supportDomain f c ⟨K, hK.1⟩ hK)

attribute [-instance] IntegralHom.tensorLocalization IntegralHom.derivedCategory in
private theorem finite_tensor
    (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
    (E : Type u) [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] (n : ℕ) (hn : 1 ≤ n)
    (S : SixFunctorDatum D C E n hn) (X : SixFunctorSpace D)
    (K L : proEtaleDerivedCategory X.obj.left (Padic.coefficientExtensionRing C.l E n))
    (hK : finiteTorConstructible C.l E n hn X.obj.left K)
    (hL : finiteTorConstructible C.l E n hn X.obj.left L) :
    finiteTorConstructible C.l E n hn X.obj.left
      ((sixFunctorFiniteTensor D C E n hn X).obj (K, L)) := by
  have he := S.finiteTensorNormalization X ⟨K, hK⟩ ⟨L, hL⟩
  change (((S.finiteTensor X).obj ⟨K, hK⟩).obj ⟨L, hL⟩).obj =
    (sixFunctorFiniteTensor D C E n hn X).obj (K, L) at he
  exact he ▸ (((S.finiteTensor X).obj ⟨K, hK⟩).obj ⟨L, hL⟩).property

attribute [-instance] IntegralHom.tensorLocalization IntegralHom.derivedCategory in
private theorem objects_property {I : Type i} {A : I → Type a}
    {B X Y T : I} (P : ∀ Z, A Z → Prop)
    (pu : A X → A T) (pv : A Y → A T) (pg : A B → A Y)
    (sf : A X → A B) (sg : A Y → A B) (sv : A T → A Y) (sh : A T → A B)
    (tb : A B → A B → A B) (ty : A Y → A Y → A Y) (tt : A T → A T → A T)
    (hpu : ∀ K, P X K → P T (pu K)) (hpv : ∀ L, P Y L → P T (pv L))
    (hpg : ∀ Q, P B Q → P Y (pg Q)) (hsf : ∀ K, P X K → P B (sf K))
    (hsg : ∀ L, P Y L → P B (sg L)) (hsv : ∀ M, P T M → P Y (sv M))
    (hsh : ∀ M, P T M → P B (sh M))
    (htb : ∀ K L, P B K → P B L → P B (tb K L))
    (hty : ∀ K L, P Y K → P Y L → P Y (ty K L))
    (htt : ∀ K L, P T K → P T L → P T (tt K L))
    (K : A X) (L : A Y) (hK : P X K) (hL : P Y L) :
    ∀ M ∈ objects pu pv pg sf sg sv sh tb ty tt K L, P M.1 M.2 := by
  have hP := hpu K hK
  have hV := hpv L hL
  have hQ := hsf K hK
  have hR := hsv _ hP
  have hG := hpg _ hQ
  have hH := htt _ _ hP hV
  have hRL := hty _ _ hR hL
  have hGL := hty _ _ hG hL
  have hLG := hty _ _ hL hG
  have hSL := hsg _ hL
  intro M hM
  simp only [objects, List.mem_cons, List.not_mem_nil, or_false] at hM
  rcases hM with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact hK
  · exact hL
  · exact hP
  · exact hV
  · exact hH
  · exact hQ
  · exact hR
  · exact hG
  · exact hRL
  · exact hGL
  · exact hLG
  · exact hsh _ hP
  · exact hsh _ hV
  · exact hsh _ hH
  · exact hsg _ hR
  · exact hsg _ hG
  · exact hsg _ hRL
  · exact hsg _ hGL
  · exact hsg _ hLG
  · exact hSL
  · exact htb _ _ hSL hQ
  · exact htb _ _ hQ hSL

attribute [-instance] IntegralHom.tensorLocalization IntegralHom.derivedCategory in
private theorem stage_presented
    {D : FiniteFieldDatum.{u}} {A : SixFunctorSpace D → Type a}
    {A' : SixFunctorSpace D → Type c}
    [∀ Z, Category.{b} (A Z)] [∀ Z, Category.{d} (A' Z)]
    (O : SixFunctorPushStage D A) (O' : SixFunctorPushStage D A')
    (T : ∀ Z, A Z ⥤ A Z ⥤ A Z) (T' : ∀ Z, A' Z ⥤ A' Z ⥤ A' Z)
    (F : ∀ Z, A Z ⥤ A' Z) (cmp : SixFunctorCoefficientComparison O O' F)
    (tensor : ∀ Z, Functor.uncurry.obj (T Z) ⋙ F Z ≅
      (F Z).prod (F Z) ⋙ Functor.uncurry.obj (T' Z))
    {X Y B : SixFunctorSpace D} (f : X ⟶ B) (g : Y ⟶ B)
    [LocallyOfFiniteType g.hom.left] [QuasiCompact g.hom.left]
    (cf : Compactification f.hom.left) (cg : Compactification g.hom.left)
    (cv : Compactification (right f g).hom.left)
    (ch : Compactification ((left f g) ≫ f).hom.left)
    (K : A X) (L : A Y) (K' : A' X) (L' : A' Y)
    (eK : (F X).obj K ≅ K') (eL : (F Y).obj L ≅ L') :
    presented F (stageObjects O T f g cf cg cv ch K L)
      (stageObjects O' T' f g cf cg cv ch K' L') := by
  let unary {Z W : SixFunctorSpace D} (H : A Z ⥤ A W) (H' : A' Z ⥤ A' W)
      (cmp : H ⋙ F W ≅ F Z ⋙ H') {M : A Z} {N : A' Z}
      (e : (F Z).obj M ≅ N) : (F W).obj (H.obj M) ≅ H'.obj N :=
    cmp.app M ≪≫ H'.mapIso e
  let binary (Z : SixFunctorSpace D) {M N : A Z} {M' N' : A' Z}
      (e : (F Z).obj M ≅ M') (e' : (F Z).obj N ≅ N') :
      (F Z).obj (((T Z).obj M).obj N) ≅ ((T' Z).obj M').obj N' :=
    (tensor Z).app (M, N) ≪≫
      (Functor.uncurry.obj (T' Z)).mapIso (Iso.prod e e')
  have eP := unary _ _ (cmp.directAdjunction (left f g)).left eK
  have eV := unary _ _ (cmp.directAdjunction (right f g)).left eL
  have eQ := unary _ _ (cmp.supportAdjunction f cf).left eK
  have eR := unary _ _ (cmp.supportAdjunction (right f g) cv).left eP
  have eG := unary _ _ (cmp.directAdjunction g).left eQ
  have eH := binary _ eP eV
  have eRL := binary _ eR eL
  have eGL := binary _ eG eL
  have eLG := binary _ eL eG
  have eSL := unary _ _ (cmp.supportAdjunction g cg).left eL
  unfold presented stageObjects objects
  dsimp only
  refine List.Forall₂.cons ⟨rfl, ⟨eK⟩⟩ ?_
  refine List.Forall₂.cons ⟨rfl, ⟨eL⟩⟩ ?_
  refine List.Forall₂.cons ⟨rfl, ⟨eP⟩⟩ ?_
  refine List.Forall₂.cons ⟨rfl, ⟨eV⟩⟩ ?_
  refine List.Forall₂.cons ⟨rfl, ⟨eH⟩⟩ ?_
  refine List.Forall₂.cons ⟨rfl, ⟨eQ⟩⟩ ?_
  refine List.Forall₂.cons ⟨rfl, ⟨eR⟩⟩ ?_
  refine List.Forall₂.cons ⟨rfl, ⟨eG⟩⟩ ?_
  refine List.Forall₂.cons ⟨rfl, ⟨eRL⟩⟩ ?_
  refine List.Forall₂.cons ⟨rfl, ⟨eGL⟩⟩ ?_
  refine List.Forall₂.cons ⟨rfl, ⟨eLG⟩⟩ ?_
  refine List.Forall₂.cons ⟨rfl, ⟨unary _ _ (cmp.supportAdjunction ((left f g) ≫ f) ch).left eP⟩⟩ ?_
  refine List.Forall₂.cons ⟨rfl, ⟨unary _ _ (cmp.supportAdjunction ((left f g) ≫ f) ch).left eV⟩⟩ ?_
  refine List.Forall₂.cons ⟨rfl, ⟨unary _ _ (cmp.supportAdjunction ((left f g) ≫ f) ch).left eH⟩⟩ ?_
  refine List.Forall₂.cons ⟨rfl, ⟨unary _ _ (cmp.supportAdjunction g cg).left eR⟩⟩ ?_
  refine List.Forall₂.cons ⟨rfl, ⟨unary _ _ (cmp.supportAdjunction g cg).left eG⟩⟩ ?_
  refine List.Forall₂.cons ⟨rfl, ⟨unary _ _ (cmp.supportAdjunction g cg).left eRL⟩⟩ ?_
  refine List.Forall₂.cons ⟨rfl, ⟨unary _ _ (cmp.supportAdjunction g cg).left eGL⟩⟩ ?_
  refine List.Forall₂.cons ⟨rfl, ⟨unary _ _ (cmp.supportAdjunction g cg).left eLG⟩⟩ ?_
  refine List.Forall₂.cons ⟨rfl, ⟨eSL⟩⟩ ?_
  refine List.Forall₂.cons ⟨rfl, ⟨binary _ eSL eQ⟩⟩ ?_
  refine List.Forall₂.cons ⟨rfl, ⟨binary _ eQ eSL⟩⟩ ?_
  exact List.Forall₂.nil

attribute [-instance] IntegralHom.tensorLocalization IntegralHom.derivedCategory in
private theorem presented_trans {I : Type i}
    {A : I → Type a} {A' : I → Type c} {A'' : I → Type b}
    [catA : ∀ Z, Category.{d} (A Z)] [catB : ∀ Z, Category.{d} (A' Z)]
    [catC : ∀ Z, Category.{d} (A'' Z)]
    (F : ∀ Z, A Z ⥤ A' Z) (G : ∀ Z, A' Z ⥤ A'' Z)
    {M : List (Σ Z, A Z)} {N : List (Σ Z, A' Z)} {P : List (Σ Z, A'' Z)}
    (h : presented F M N) (h' : presented G N P) :
    presented (fun Z ↦ F Z ⋙ G Z) M P := by
  induction M generalizing N P with
  | nil => cases h; cases h'; exact List.Forall₂.nil
  | cons m ms ih =>
    cases N with
    | nil => cases h
    | cons n ns =>
      cases P with
      | nil => cases h'
      | cons p ps =>
        cases h with
        | cons hmn ht =>
          cases h' with
          | cons hnp ht' =>
            refine List.Forall₂.cons ?_ (ih ht ht')
            rcases m with ⟨Z, m⟩
            rcases n with ⟨W, n⟩
            rcases p with ⟨V, p⟩
            change ∃ h : Z = W, Nonempty ((F Z).obj m ≅ h.symm ▸ n) at hmn
            rcases hmn with ⟨hZW, he⟩
            subst W
            rcases he with ⟨e⟩
            change ∃ h : Z = V, Nonempty ((G Z).obj n ≅ h.symm ▸ p) at hnp
            rcases hnp with ⟨hZV, he'⟩
            subst V
            rcases he' with ⟨e'⟩
            exact ⟨rfl, ⟨(G Z).mapIso e ≪≫ e'⟩⟩

attribute [-instance] IntegralHom.tensorLocalization IntegralHom.derivedCategory in
/-- Every factor in the relative-product composite has its prescribed finite-Tor and
witnessed domain, at all four coefficient stages. The field clauses retain a joint
integral presentation of the whole displayed list; they never reduce a field object.
Source: current blueprint, sec-six-functors/sk-thm-sf-kunneth-relative, typing before
the displayed relative map and the finite-Tor second-variable paragraph
(blueprint: lem-sf-relative-product-input-domains).

Proof (postponed):
1. The two projections are base changes of g and f. Finite-type base-change stability
(lem-sfb-finite-type-composition-base-change), separated base change
(lem-weil-pbc-separated-base-change), and composition permanence
(lem-weil-pbc-proper-fp-permanence) give every geometric clause.
2. At finite coefficients apply thm-sf-ctf-stability to pullback along u and v,
then tensor, support along f and v, pullback along g, and the three ordered tensors
on Y. Apply support along h and g to every displayed object, then tensor Rg!L
with Q in both orders. This uses no relative-product isomorphism.
3. For the other stages use the pullback, tensor and support restrictions of
lem-sf-package-coefficient-domain-realization. At the integral stage
lem-coef-integral-residue-tor gives one Tor interval for all reductions; at field
stages finite Tor means precisely the whole bounded constructible category.
4. The two projection components of def-exchange-projection have second arguments
L and Q, respectively, both in the already verified finite-Tor domains.
5. Apply lem-sf-proetale-constructible-origin(ii) separately to every finite input,
including the original K and L. Retain the bounded constructible etale antecedent
and its comparison isomorphism as the pair of def-weil-pbc-etale-origin-witness.
6. The witnesses for H and K are exactly the bounded-below witnessed inputs of
thm-sf-comp-composition and thm-cbc-finite-level-proetale. Use the given
compactification of f in the latter; no extra hypothesis on the base is needed.
7. At integral coefficients def-weil-derived-complete-integral-detailed gives
bounded constructibility of each positive finite reduction. Apply Step 5 to each
reduction separately; compatible antecedents across levels are not required.
8. Raw rationalization has integral representatives with the same objects. Form
the entire list integrally and use the specified coefficient comparisons to
identify its rationalization with the rational list. At algebraically closed
coefficients choose one finite coefficient field containing both fields of
definition, take integral representatives there, and use common-stage comparisons.
Step 7 supplies their finite witnesses. Since f,g,K,L were arbitrary, the same
assertions hold for every other pair with the stated geometric and Tor hypotheses. -/
theorem relative_product_input_domains
    (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
    (E : Type u) [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] (n : ℕ) (hn : 1 ≤ n)
    (S : SixFunctorDatum D C E n hn)
    {X Y B : SixFunctorSpace D} [IsSeparated B.obj.hom]
    (f : X ⟶ B) (g : Y ⟶ B)
    [IsSeparated f.hom.left] [LocallyOfFiniteType f.hom.left] [QuasiCompact f.hom.left]
    [IsSeparated g.hom.left] [LocallyOfFiniteType g.hom.left] [QuasiCompact g.hom.left]
    (cf : Compactification f.hom.left) (cg : Compactification g.hom.left)
    (cv : Compactification (right f g).hom.left)
    (ch : Compactification ((left f g) ≫ f).hom.left) :
    (IsSeparated X.obj.hom ∧ LocallyOfFiniteType X.obj.hom ∧ QuasiCompact X.obj.hom) ∧
    (IsSeparated Y.obj.hom ∧ LocallyOfFiniteType Y.obj.hom ∧ QuasiCompact Y.obj.hom) ∧
    (IsSeparated (space f g).obj.hom ∧ LocallyOfFiniteType (space f g).obj.hom ∧
      QuasiCompact (space f g).obj.hom) ∧
    (IsSeparated (left f g).hom.left ∧ LocallyOfFiniteType (left f g).hom.left ∧
      QuasiCompact (left f g).hom.left) ∧
    (IsSeparated (right f g).hom.left ∧ LocallyOfFiniteType (right f g).hom.left ∧
      QuasiCompact (right f g).hom.left) ∧
    (IsSeparated (((left f g) ≫ f).hom.left) ∧
      LocallyOfFiniteType (((left f g) ≫ f).hom.left) ∧
      QuasiCompact (((left f g) ≫ f).hom.left)) ∧
    (∀ (K : proEtaleDerivedCategory X.obj.left (Padic.coefficientExtensionRing C.l E n))
      (L : proEtaleDerivedCategory Y.obj.left (Padic.coefficientExtensionRing C.l E n)),
      finiteTorConstructible C.l E n hn X.obj.left K →
      finiteTorConstructible C.l E n hn Y.obj.left L →
      ∀ M ∈ finiteObjects D C E n hn f g cf cg cv ch K L,
        finiteTorConstructible C.l E n hn M.1.obj.left M.2 ∧
          finiteWitness D C E n hn M.1 M.2) ∧
    (∀ (K : sfIntegralConstructibleCategory C.l E X.obj.left)
      (L : sfIntegralConstructibleCategory C.l E Y.obj.left),
      finiteTorConstructibleIntegral C.l E X.obj.left K.obj →
      finiteTorConstructibleIntegral C.l E Y.obj.left L.obj →
      ∀ M ∈ stageObjects S.higher.integral S.higher.integralTensor f g cf cg cv ch K L,
        finiteTorConstructibleIntegral C.l E M.1.obj.left M.2.obj ∧
          integralWitness D C E M.1 M.2) ∧
    (∀ (K : sfRationalConstructibleCategory C.l E X.obj.left)
      (L : sfRationalConstructibleCategory C.l E Y.obj.left),
      ∃ (K₀ : sfIntegralConstructibleCategory C.l E X.obj.left)
        (L₀ : sfIntegralConstructibleCategory C.l E Y.obj.left),
        (∀ M ∈ stageObjects S.higher.integral S.higher.integralTensor
            f g cf cg cv ch K₀ L₀,
          finiteTorConstructibleIntegral C.l E M.1.obj.left M.2.obj ∧
            integralWitness D C E M.1 M.2) ∧
        presented
          (fun Z : SixFunctorSpace D ↦ sfRationalConstructibleLocalization C.l E Z.obj.left)
          (stageObjects S.higher.integral S.higher.integralTensor f g cf cg cv ch K₀ L₀)
          (stageObjects S.higher.rational S.higher.rationalTensor f g cf cg cv ch K L)) ∧
    (∀ (K : generalAlgebraicallyClosedConstructibleCategory C.l C.Qbar X.obj.left)
      (L : generalAlgebraicallyClosedConstructibleCategory C.l C.Qbar Y.obj.left),
      ∃ (E₀ : Padic.FiniteCoefficientFields C.l C.Qbar)
        (K₀ : sfIntegralConstructibleCategory C.l
          (AlgebraicallyClosedCoefficients.Coefficient.{u} C.l C.Qbar E₀) X.obj.left)
        (L₀ : sfIntegralConstructibleCategory C.l
          (AlgebraicallyClosedCoefficients.Coefficient.{u} C.l C.Qbar E₀) Y.obj.left),
        (∀ M ∈ stageObjects (S.closure.coefficientStages E₀).integral
            (S.closure.coefficientStages E₀).integralTensor f g cf cg cv ch K₀ L₀,
          finiteTorConstructibleIntegral C.l
              (AlgebraicallyClosedCoefficients.Coefficient.{u} C.l C.Qbar E₀)
              M.1.obj.left M.2.obj ∧
            integralWitness D C (AlgebraicallyClosedCoefficients.Coefficient.{u}
              C.l C.Qbar E₀) M.1 M.2) ∧
        presented
          (A := fun Z : SixFunctorSpace D ↦ sfIntegralConstructibleCategory C.l
            (AlgebraicallyClosedCoefficients.Coefficient.{u} C.l C.Qbar E₀) Z.obj.left)
          (A' := fun Z : SixFunctorSpace D ↦
            generalAlgebraicallyClosedConstructibleCategory C.l C.Qbar Z.obj.left)
          (catA := fun Z ↦ inferInstanceAs (Category (sfIntegralConstructibleCategory C.l
            (AlgebraicallyClosedCoefficients.Coefficient.{u} C.l C.Qbar E₀) Z.obj.left)))
          (catB := fun Z ↦ inferInstanceAs (Category
            (generalAlgebraicallyClosedConstructibleCategory C.l C.Qbar Z.obj.left)))
          (commonPassage D C E₀)
          (stageObjects (S.closure.coefficientStages E₀).integral
            (S.closure.coefficientStages E₀).integralTensor f g cf cg cv ch K₀ L₀)
          (stageObjects S.closure.commonStage S.closure.commonStageTensor
            f g cf cg cv ch K L)) := by
  have hX : IsSeparated X.obj.hom := by
    rw [← f.hom.w]
    infer_instance
  have hY : IsSeparated Y.obj.hom := by
    rw [← g.hom.w]
    infer_instance
  have hu : IsSeparated (left f g).hom.left := by
    change IsSeparated (pullback.fst f.hom.left g.hom.left)
    infer_instance
  have hv : IsSeparated (right f g).hom.left := by
    change IsSeparated (pullback.snd f.hom.left g.hom.left)
    infer_instance
  have huft : LocallyOfFiniteType (left f g).hom.left := by
    change LocallyOfFiniteType (pullback.fst f.hom.left g.hom.left)
    infer_instance
  have hvft : LocallyOfFiniteType (right f g).hom.left := by
    change LocallyOfFiniteType (pullback.snd f.hom.left g.hom.left)
    infer_instance
  have huqc : QuasiCompact (left f g).hom.left := by
    change QuasiCompact (pullback.fst f.hom.left g.hom.left)
    infer_instance
  have hvqc : QuasiCompact (right f g).hom.left := by
    change QuasiCompact (pullback.snd f.hom.left g.hom.left)
    infer_instance
  have hT : IsSeparated (space f g).obj.hom := by
    change IsSeparated (pullback.fst f.hom.left g.hom.left ≫ X.obj.hom)
    infer_instance
  have hh : IsSeparated ((left f g) ≫ f).hom.left := by
    change IsSeparated ((left f g).hom.left ≫ f.hom.left)
    infer_instance
  have hhft : LocallyOfFiniteType ((left f g) ≫ f).hom.left := by
    change LocallyOfFiniteType ((left f g).hom.left ≫ f.hom.left)
    infer_instance
  have hhqc : QuasiCompact ((left f g) ≫ f).hom.left := by
    change QuasiCompact ((left f g).hom.left ≫ f.hom.left)
    infer_instance
  refine ⟨⟨hX, X.property⟩, ⟨hY, Y.property⟩, ⟨hT, (space f g).property⟩,
    ⟨hu, huft, huqc⟩, ⟨hv, hvft, hvqc⟩, ⟨hh, hhft, hhqc⟩, ?_, ?_, ?_, ?_⟩
  · intro K L hK hL M hM
    have h := objects_property
      (A := fun Z : SixFunctorSpace D ↦ proEtaleDerivedCategory Z.obj.left
        (Padic.coefficientExtensionRing C.l E n))
      (B := B) (X := X) (Y := Y) (T := space f g)
      (fun Z K ↦ finiteTorConstructible C.l E n hn Z.obj.left K)
      (sixFunctorFinitePullback D C E n hn (left f g)).obj
      (sixFunctorFinitePullback D C E n hn (right f g)).obj
      (sixFunctorFinitePullback D C E n hn g).obj
      (sixFunctorFiniteSupport D C E n hn f cf).obj
      (sixFunctorFiniteSupport D C E n hn g cg).obj
      (sixFunctorFiniteSupport D C E n hn (right f g) cv).obj
      (sixFunctorFiniteSupport D C E n hn ((left f g) ≫ f) ch).obj
      (fun M N ↦ (sixFunctorFiniteTensor D C E n hn B).obj (M, N))
      (fun M N ↦ (sixFunctorFiniteTensor D C E n hn Y).obj (M, N))
      (fun M N ↦ (sixFunctorFiniteTensor D C E n hn (space f g)).obj (M, N))
      (finite_pull D C E n hn S (left f g))
      (finite_pull D C E n hn S (right f g))
      (finite_pull D C E n hn S g)
      (finite_support D C E n hn S f cf)
      (finite_support D C E n hn S g cg)
      (finite_support D C E n hn S (right f g) cv)
      (finite_support D C E n hn S ((left f g) ≫ f) ch)
      (finite_tensor D C E n hn S B)
      (finite_tensor D C E n hn S Y)
      (finite_tensor D C E n hn S (space f g)) K L hK hL M hM
    exact ⟨h, finite_origin D C E n hn M.1 M.2 h.1⟩
  · intro K L _ _ M _
    exact integral_domains D C E M.1 M.2
  · intro K L
    refine ⟨K.obj, L.obj, ?_, ?_⟩
    · intro M _
      exact integral_domains D C E M.1 M.2
    · exact stage_presented S.higher.integral S.higher.rational
        S.higher.integralTensor S.higher.rationalTensor
        (fun Z ↦ sfRationalConstructibleLocalization C.l E Z.obj.left)
        S.higher.rationalization
        (S.higher.rationalExchangeComparison
          (FixProjectionCompactification.identitySquare f cf)).tensor
        f g cf cg cv ch K.obj L.obj K L (Iso.refl _) (Iso.refl _)
  · intro K L
    let sysX := GeneralAlgebraicallyClosedCoefficients.stageSystem C.l C.Qbar X.obj.left
    let sysY := GeneralAlgebraicallyClosedCoefficients.stageSystem C.l C.Qbar Y.obj.left
    let E₀ := Padic.finiteCoefficientCompositum C.l C.Qbar K.stage L.stage
    have hK : K.stage ≤ E₀ :=
      (Padic.finiteCoefficientFields_properties C.l C.Qbar).1 K.stage L.stage |>.1
    have hL : L.stage ≤ E₀ :=
      (Padic.finiteCoefficientFields_properties C.l C.Qbar).1 K.stage L.stage |>.2
    let Kr := K.toStage hK
    let Lr := L.toStage hL
    let H := S.closure.coefficientStages E₀
    refine ⟨E₀, Kr.obj, Lr.obj, ?_, ?_⟩
    · intro M _
      exact integral_domains D C _ M.1 M.2
    · have h₁ := stage_presented H.integral H.rational H.integralTensor H.rationalTensor
        (fun Z : SixFunctorSpace D ↦ sfRationalConstructibleLocalization C.l
          (AlgebraicallyClosedCoefficients.Coefficient.{u} C.l C.Qbar E₀) Z.obj.left)
        H.rationalization
        (H.rationalExchangeComparison
          (FixProjectionCompactification.identitySquare f cf)).tensor
        f g cf cg cv ch Kr.obj Lr.obj Kr Lr (Iso.refl _) (Iso.refl _)
      have h₂ := stage_presented H.rational S.closure.commonStage
        H.rationalTensor S.closure.commonStageTensor
        (fun Z : SixFunctorSpace D ↦ GeneralAlgebraicallyClosedCoefficients.inclusion
          (l := C.l) (Ω := C.Qbar) (Y := Z.obj.left) E₀)
        (S.closure.commonStageComparison E₀)
        (S.closure.commonStageExchangeComparison E₀
          (FixProjectionCompactification.identitySquare f cf)).tensor
        f g cf cg cv ch Kr Lr K L (sysX.isoToStage K hK).symm
          (sysY.isoToStage L hL).symm
      exact presented_trans
        (A := fun Z : SixFunctorSpace D ↦ sfIntegralConstructibleCategory C.l
          (AlgebraicallyClosedCoefficients.Coefficient.{u} C.l C.Qbar E₀) Z.obj.left)
        (A' := fun Z : SixFunctorSpace D ↦ sfRationalConstructibleCategory C.l
          (AlgebraicallyClosedCoefficients.Coefficient.{u} C.l C.Qbar E₀) Z.obj.left)
        (A'' := fun Z : SixFunctorSpace D ↦
          generalAlgebraicallyClosedConstructibleCategory C.l C.Qbar Z.obj.left)
        (catA := fun Z ↦ inferInstance) (catB := fun Z ↦ inferInstance)
        (catC := fun Z ↦ inferInstance)
        (fun Z : SixFunctorSpace D ↦ sfRationalConstructibleLocalization C.l
          (AlgebraicallyClosedCoefficients.Coefficient.{u} C.l C.Qbar E₀) Z.obj.left)
        (fun Z : SixFunctorSpace D ↦ GeneralAlgebraicallyClosedCoefficients.inclusion
          (l := C.l) (Ω := C.Qbar) (Y := Z.obj.left) E₀) h₁ h₂

end WeilConjectures
