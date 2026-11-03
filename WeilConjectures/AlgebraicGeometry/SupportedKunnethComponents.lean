/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.SixFunctors.Etale.Derived.EtaleTorAmplitude
public import WeilConjectures.AlgebraicGeometry.Supported.SupportedExteriorProduct
import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Ordinary
import WeilConjectures.AlgebraicGeometry.Etale.Constant.EtaleConstantProjectionMap
import WeilConjectures.AlgebraicGeometry.FullSupportKunnethComparison
import WeilConjectures.AlgebraicGeometry.KunnethGlobalSections
import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
import WeilConjectures.AlgebraicGeometry.DerivedCategories
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvr
import WeilConjectures.AlgebraicGeometry.Etale.EtaleStalkTorTest
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.FieldTheory.Finite.Basic

/-!
# Supported Künneth: boundedness and the full-support components

Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-smooth-purity/
sec-the-trace-map-of-affine-space/sk-prop-an/lem-pur-kunneth-supported.proof.md,
paragraphs 1--2
(blueprint: lem-pur-kunneth-supported-components).
-/

@[expose] public section
set_option autoImplicit false
universe u uA
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
namespace AlgebraicGeometry.Etale

private theorem externalProduct_boundedBelow
    (A : Type (u + 1)) [CommRing A] {B X Y : Scheme.{u}}
    (f : X ⟶ B) (g : Y ⟶ B)
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (L : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (hK : ∃ a b : ℤ, K.IsGE a ∧ K.IsLE b)
    (hTor : ∃ a b : ℤ, DerivedCategory.hasTorAmplitudeIn A Y a b L) :
    ∃ q : ℤ, (externalProduct (ModuleCat.{u + 1} A) f g K L).IsGE q := by
  obtain ⟨c, d, hc, hd⟩ := hK
  obtain ⟨a, b, ht⟩ := hTor
  have ht' : DerivedCategory.hasTorAmplitudeIn A Y a (max a b) L := by
    intro M q hq
    apply ht M q
    rcases hq with hq | hq
    · exact Or.inl hq
    · exact Or.inr (lt_of_le_of_lt (le_max_right a b) hq)
  have hp := (geometricStalk_torAmplitude_test A Y L a (max a b)
    (le_max_left a b)).2 (pullback f g) (pullback.snd f g) ht'
  let P := (upperStar (ModuleCat.{u + 1} A) (pullback.fst f g)).mapDerivedCategory.obj K
  let Q := (upperStar (ModuleCat.{u + 1} A) (pullback.snd f g)).mapDerivedCategory.obj L
  have hcP : P.IsGE c := by
    have : K.IsGE c := hc
    exact Functor.isGE_mapDerivedCategory_obj _ K c
  have hdP : P.IsLE d := by
    have : K.IsLE d := hd
    exact Functor.isLE_mapDerivedCategory_obj _ K d
  have htQ : _root_.DerivedCategory.torAmplitudeIn
      (Sheaf (pullback f g).smallEtaleTopology (ModuleCat.{u + 1} A)) a (max a b) Q :=
    DerivedCategory.hasTorAmplitudeIn_iff_torAmplitudeIn.mp hp
  have hPQ := _root_.DerivedCategory.homologyConcentratedIn_tensor_of_torAmplitudeIn_right
    (show _root_.DerivedCategory.homologyConcentratedIn c d P from ⟨hcP, hdP⟩) htQ
  let e : externalProduct (ModuleCat.{u + 1} A) f g K L ≅ P ⊗ Q :=
    tensorIso
      ((leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A)
        (pullback.fst f g)).app K)
      ((leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A)
        (pullback.snd f g)).app L)
  have : (P ⊗ Q).IsGE (c + a) := hPQ.1
  exact ⟨c + a, _root_.DerivedCategory.TStructure.t.isGE_of_iso e.symm _⟩

private theorem datum_char (D : WeilConjectures.FiniteFieldDatum.{u}) :
    ringChar D.k = D.p := by
  let : Fintype D.k₀ := Fintype.ofFinite D.k₀
  have : Fact D.p.Prime := ⟨D.prime⟩
  have : CharP D.k₀ D.p := charP_of_card_eq_prime_pow
    ((Nat.card_eq_fintype_card (α := D.k₀)).symm.trans (D.card_base.trans D.cardinality_eq))
  have : CharP D.k D.p := charP_of_injective_algebraMap' D.k₀ D.p
  exact ringChar.eq D.k D.p

attribute [local instance 2000] CommRing.toRing monoidalConstantSheaf

private theorem ordinary_of_relative
    (A : Type uA) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [HasSmallSiteSheafify A]
    [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
    [Abelian.HasFunctorialFlatResolution A] [UpperStarPreservesFlat A]
    {S X Y Z : Scheme.{u}} (p : Z ⟶ X) (q : Z ⟶ Y)
    (f : X ⟶ S) (g : Y ⟶ S) (w : q ≫ g = p ≫ f)
    [(constantSheaf S.smallEtaleTopology A).PreservesFlat]
    [(constantSheaf S.smallEtaleTopology A).IsEquivalence]
    [(constantSheaf Z.smallEtaleTopology A).PreservesFlat]
    [hZ : (constantSheaf Z.smallEtaleTopology A).Monoidal]
    (hcanon : hZ = monoidalConstantSheaf Z.smallEtaleTopology A)
    (K : DerivedCategory (Sheaf X.smallEtaleTopology A))
    (M : DerivedCategory (Sheaf Y.smallEtaleTopology A))
    [IsIso (kunnethMap A p q f g (p ≫ f) rfl w K M)] :
    IsIso (ordinaryGlobalKunnethMap A p q K M) := by
  cases hcanon
  rw [ordinaryGlobalKunnethMap_eq_relative A p q f g w K M]
  unfold ordinaryRelativeGlobalKunnethMap ordinaryKunnethTensorMate
  rw [Adjunction.homEquiv_unit]
  infer_instance

private theorem ordinary_for_map
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (ell : ℕ) [Fact ell.Prime] (hell : ell ≠ D.p)
    (E : Type (u + 1)) [Field E] [Algebra (Padic ell) E]
    [FiniteDimensional (Padic ell) E] (n : ℕ) (hn : 1 ≤ n)
    {X Y : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of D.k))
    (g : Y ⟶ Spec (CommRingCat.of D.k))
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} (Padic.coefficientExtensionRing ell E n))))
    (L : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology
      (ModuleCat.{u + 1} (Padic.coefficientExtensionRing ell E n)))) :
    IsIso (ordinaryGlobalKunnethMap (ModuleCat.{u + 1}
      (Padic.coefficientExtensionRing ell E n)) (pullback.fst f g) (pullback.snd f g) K L) := by
  have hell' : ell ≠ ringChar D.k := by rwa [datum_char D]
  let X' := Over.mk f
  let Y' := Over.mk g
  have : IsSeparated X'.hom := ‹IsSeparated f›
  have : LocallyOfFiniteType X'.hom := ‹LocallyOfFiniteType f›
  have : QuasiCompact X'.hom := ‹QuasiCompact f›
  have : IsSeparated Y'.hom := ‹IsSeparated g›
  have : LocallyOfFiniteType Y'.hom := ‹LocallyOfFiniteType g›
  have : QuasiCompact Y'.hom := ‹QuasiCompact g›
  have : IsAlgClosed D.k := IsAlgClosure.isAlgClosed D.k₀
  let A := Padic.coefficientExtensionRing ell E n
  let C := ModuleCat.{u + 1} A
  have h := isIso_kunnethGlobalSectionsMap_finiteCoefficientRing D ell hell' E n hn X' Y' K L
  have hmap : IsIso ((rightDerivedGlobalSections C (Spec (CommRingCat.of D.k))).map
      (kunnethMap C (pullback.fst X'.hom Y'.hom) (pullback.snd X'.hom Y'.hom)
        X'.hom Y'.hom (pullback.fst X'.hom Y'.hom ≫ X'.hom)
        rfl pullback.condition.symm K L)) := by
    simpa only [kunnethGlobalSectionsMap, Category.assoc,
      isIso_comp_left_iff, isIso_comp_right_iff] using h
  let e := constantSheafEquivalenceOfIsSepClosed A (k := D.k)
  have : (constantSheaf (Spec (CommRingCat.of D.k)).smallEtaleTopology C).IsEquivalence :=
    e.isEquivalence_functor
  have : (rightDerivedGlobalSections C (Spec (CommRingCat.of D.k))).IsEquivalence :=
    isEquivalence_rightDerivedGlobalSections_of_isEquivalence C _
  have hk : IsIso (kunnethMap C (pullback.fst X'.hom Y'.hom) (pullback.snd X'.hom Y'.hom)
      X'.hom Y'.hom (pullback.fst X'.hom Y'.hom ≫ X'.hom)
      rfl pullback.condition.symm K L) :=
    isIso_of_reflects_iso _ (rightDerivedGlobalSections C (Spec (CommRingCat.of D.k)))
  exact ordinary_of_relative C
    (pullback.fst X'.hom Y'.hom) (pullback.snd X'.hom Y'.hom)
    X'.hom Y'.hom pullback.condition.symm
    rfl K L

private theorem full_for_map
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (ell : ℕ) [Fact ell.Prime] (hell : ell ≠ D.p)
    (E : Type (u + 1)) [Field E] [Algebra (Padic ell) E]
    [FiniteDimensional (Padic ell) E] (n : ℕ) (hn : 1 ≤ n)
    {X Y : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of D.k))
    (g : Y ⟶ Spec (CommRingCat.of D.k))
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} (Padic.coefficientExtensionRing ell E n))))
    (L : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology
      (ModuleCat.{u + 1} (Padic.coefficientExtensionRing ell E n)))) :
    IsIso (supportedExteriorProduct (Padic.coefficientExtensionRing ell E n)
      f g (𝟙 X) (𝟙 Y) K L) := by
  have := ordinary_for_map D ell hell E n hn f g K L
  exact isIso_supportedExteriorProduct_fullSupport
    (Padic.coefficientExtensionRing ell E n) f g K L

private theorem open_quasiCompact
    {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
    [LocallyOfFiniteType f] [QuasiCompact f] (U : X.Opens) : QuasiCompact U.ι := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : IsNoetherian X := ⟨⟩
  infer_instance

/-- The boundedness and four full-support inputs for support localization: the external
product `K ⊠ L` is bounded below, and the supported exterior products with full supports
on `X × Y`, `X × V`, `U × Y`, `U × V` (`U = X \ Z`, `V = Y \ W`) are isomorphisms.

Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-smooth-purity/
sec-the-trace-map-of-affine-space/sk-prop-an/lem-pur-kunneth-supported.proof.md,
paragraphs 1--2; Stacks 0F1P
(blueprint: lem-pur-kunneth-supported-components).

Proof:
1. Exact inverse image along the projections preserves the cohomology interval of `K`,
   and by lem-sf-etale-stalk-tor-test the Tor-amplitude interval of `L`; by
   lem-sf-source-tensor-cohomology-interval the derived tensor product `K ⊠ L` is
   bounded below, which gives `q`.
2. With full supports (closed immersions `𝟙`), def-pur-supported-exterior-product
   identifies the supported exterior product with the ordinary exterior product, which is
   an isomorphism by `isIso_kunnethGlobalSectionsMap_finiteCoefficientRing`
   (lem-pur-ordinary-kunneth-finite-ring) for `A = A_{E,n}`; the open subschemes `U`, `V`
   are separated of finite type over `k` (quasi-compact since `X`, `Y` are Noetherian),
   so the same applies to `X × V`, `U × Y`, `U × V`.
-/
theorem supportedKunneth_components
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (ell : ℕ) [Fact ell.Prime] (hell : ell ≠ D.p)
    (E : Type (u + 1)) [Field E] [Algebra (Padic ell) E]
    [FiniteDimensional (Padic ell) E] (n : ℕ) (hn : 1 ≤ n)
    {X Y : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of D.k))
    (g : Y ⟶ Spec (CommRingCat.of D.k))
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    {Z W : Scheme.{u}} (i : Z ⟶ X) (j : W ⟶ Y)
    [IsClosedImmersion i] [IsClosedImmersion j]
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} (Padic.coefficientExtensionRing ell E n))))
    (L : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology
      (ModuleCat.{u + 1} (Padic.coefficientExtensionRing ell E n))))
    (hK : ∃ a b : ℤ, K.obj.IsGE a ∧ K.obj.IsLE b)
    (hL : ∃ a b : ℤ, L.obj.IsGE a ∧ L.obj.IsLE b)
    (hTor : ∃ a b : ℤ, DerivedCategory.hasTorAmplitudeIn
      (Padic.coefficientExtensionRing ell E n) Y a b L.obj) :
    ∃ q : ℤ,
      (externalProduct (ModuleCat.{u + 1} (Padic.coefficientExtensionRing ell E n))
        f g K.obj L.obj).IsGE q ∧
      IsIso (supportedExteriorProduct (Padic.coefficientExtensionRing ell E n)
        f g (𝟙 X) (𝟙 Y) K.obj L.obj) ∧
      IsIso (supportedExteriorProduct (Padic.coefficientExtensionRing ell E n)
        f (j.openComplement.ι ≫ g) (𝟙 X) (𝟙 j.openComplement.toScheme) K.obj
        ((upperStar (ModuleCat.{u + 1} (Padic.coefficientExtensionRing ell E n))
          j.openComplement.ι).mapDerivedCategory.obj L.obj)) ∧
      IsIso (supportedExteriorProduct (Padic.coefficientExtensionRing ell E n)
        (i.openComplement.ι ≫ f) g (𝟙 i.openComplement.toScheme) (𝟙 Y)
        ((upperStar (ModuleCat.{u + 1} (Padic.coefficientExtensionRing ell E n))
          i.openComplement.ι).mapDerivedCategory.obj K.obj) L.obj) ∧
      IsIso (supportedExteriorProduct (Padic.coefficientExtensionRing ell E n)
        (i.openComplement.ι ≫ f) (j.openComplement.ι ≫ g)
        (𝟙 i.openComplement.toScheme) (𝟙 j.openComplement.toScheme)
        ((upperStar (ModuleCat.{u + 1} (Padic.coefficientExtensionRing ell E n))
          i.openComplement.ι).mapDerivedCategory.obj K.obj)
        ((upperStar (ModuleCat.{u + 1} (Padic.coefficientExtensionRing ell E n))
          j.openComplement.ι).mapDerivedCategory.obj L.obj)) := by
  have _ := hL
  obtain ⟨q, hq⟩ := externalProduct_boundedBelow
    (Padic.coefficientExtensionRing ell E n) f g K.obj L.obj hK hTor
  have : QuasiCompact i.openComplement.ι := open_quasiCompact f i.openComplement
  have : QuasiCompact j.openComplement.ι := open_quasiCompact g j.openComplement
  exact ⟨q, hq,
    full_for_map D ell hell E n hn f g K.obj L.obj,
    full_for_map D ell hell E n hn f (j.openComplement.ι ≫ g) K.obj
      ((upperStar (ModuleCat.{u + 1} (Padic.coefficientExtensionRing ell E n))
        j.openComplement.ι).mapDerivedCategory.obj L.obj),
    full_for_map D ell hell E n hn (i.openComplement.ι ≫ f) g
      ((upperStar (ModuleCat.{u + 1} (Padic.coefficientExtensionRing ell E n))
        i.openComplement.ι).mapDerivedCategory.obj K.obj) L.obj,
    full_for_map D ell hell E n hn (i.openComplement.ι ≫ f) (j.openComplement.ι ≫ g)
      ((upperStar (ModuleCat.{u + 1} (Padic.coefficientExtensionRing ell E n))
        i.openComplement.ι).mapDerivedCategory.obj K.obj)
      ((upperStar (ModuleCat.{u + 1} (Padic.coefficientExtensionRing ell E n))
        j.openComplement.ι).mapDerivedCategory.obj L.obj)⟩

end AlgebraicGeometry.Etale
