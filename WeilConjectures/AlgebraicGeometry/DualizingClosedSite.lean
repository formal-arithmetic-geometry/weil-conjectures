/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.SixFunctors.Etale.Derived.Tensor
public import WeilConjectures.AlgebraicGeometry.EtaleTorAmplitude
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.AlgebraicGeometry.ProEtaleSiteComparisonSupplement
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import WeilConjectures.AlgebraicGeometry.EtaleClosedAmbientAdjoint
public import WeilConjectures.AlgebraicGeometry.CanonicalCompactSupportSiteComparison
public import WeilConjectures.AlgebraicGeometry.FixedComparisonDirectImageMate
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint
public import WeilConjectures.AlgebraicGeometry.SpecifiedExceptionalClassHom
public import WeilConjectures.AlgebraicGeometry.FiniteFieldFiberSupplement
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.AlgebraicGeometry.EtaleCompactSupportCoefficientChange
public import WeilConjectures.AlgebraicGeometry.ProEtaleTorAmplitudePresentations
public import WeilConjectures.AlgebraicGeometry.WitnessCompatibility
public import WeilConjectures.AlgebraicGeometry.ClosedIdentityOpenComparison
public import WeilConjectures.AlgebraicGeometry.FixedFiniteExceptionalAt
public import WeilConjectures.AlgebraicGeometry.ComparisonDerivedPullbackFixed
public import WeilConjectures.SixFunctors.Etale.Derived.Dualizing
public import WeilConjectures.Compactification.Affine
import WeilConjectures.AlgebraicGeometry.ClosedDualizingEtaleFiniteness
import WeilConjectures.AlgebraicGeometry.ClosedIdentityOpenHomNormalization
import WeilConjectures.AlgebraicGeometry.CompactSupportComparisonNormalization
import WeilConjectures.CategoryTheory.DerivedCategory.TorAmplitudeMapDerivedCategory
import WeilConjectures.SixFunctors.ProEtale.Comparison.Flat
import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.FlatModel

/-! # Bounded site transport of closed exceptional dualizing objects

Source: main-20261015 blueprint, lem-coef-finite-dualizing.proof.md, paragraph 3
(blueprint: lem-coef-dualizing-closed-site).

The identity-open compactification is retained literally. Its direct images and right
adjoint are identified with the closed direct images and their right adjoint by
`closedIdentityOpenEtaleComparison`, `closedIdentityOpenProEtaleComparison`, and
adjunction uniqueness.
The counit is the inverse image of the identity under the specified relative Hom chain.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor ZeroObject
namespace AlgebraicGeometry.ProEtale

/-- The bounded closed-site assertion at one coefficient ring and one ordinary object.
This expands the specified unit, its exceptional image, retained origin, inverse
compact-support comparison, and transported counit; it chooses no map or isomorphism.
Source: lem-coef-finite-dualizing.proof.md, paragraph 3, closed counit identification
(blueprint: lem-coef-dualizing-closed-site). -/
def dualizingClosedSiteTransport (R : Type (u + 1)) [CommRing R] [Finite R]
    {Y P : Scheme.{u}} [CompactSpace P] (i : Y ⟶ P) [IsClosedImmersion i]
    (H : Etale.DerivedCategoryModule R P) : Prop :=
  let C := ModuleCat.{u + 1, u + 1} R
  let c := Compactification.ofIsProper i
  let F := Etale.rightDerivedLowerShriekOfCompactification C c
  letI := Etale.isLeftAdjoint_rightDerivedLowerShriekOfCompactification R c
  let I := F.rightAdjoint
  let S := fun W : Scheme.{u} ↦ (comparisonUpperStar C W).mapDerivedCategory.{u + 1, u + 1}
  let U := (comparisonLowerStar C P).rightDerivedFunctor
  let J := U ⋙ I ⋙ S Y
  let η := (derivedComparisonAdjunction C P).unit
  let α := (S Y).map (I.map (η.app H))
  ∃ hH : _root_.DerivedCategory.TStructure.t.plus H,
    ∃ hIH : _root_.DerivedCategory.TStructure.t.plus (I.obj H),
      IsIso (η.app H) ∧ IsIso α ∧
      ∃ hJ : _root_.DerivedCategory.TStructure.t.plus (J.obj ((S P).obj H)),
        ∃ W : Scheme.FixedEtaleOriginWitness Y R ⟨J.obj ((S P).obj H), hJ⟩,
          W.complex = ⟨I.obj H, hIH⟩ ∧ HEq W.iso.hom α ∧
          (compactSupportSiteComparison R c).inv.app ⟨I.obj H, hIH⟩ ≫
              (rightDerivedLowerShriekOfCompactification C c).map α ≫
              (specifiedExceptionalHomEquiv R c ⟨J.obj ((S P).obj H), hJ⟩ W
                ((siteComparisonDerivedPullbackPlus P R).obj ⟨H, hH⟩)).symm
                  (𝟙 (J.obj ((S P).obj H))) =
            (S P).map ((Adjunction.ofIsLeftAdjoint F).counit.app H)

/-- The canonical closed direct-image mate equals the inverse identity-open
compact-support comparison, after the two identity-open identifications.
Source: lem-coef-finite-dualizing.proof.md, paragraph 3, definition of delta
(blueprint: lem-coef-dualizing-closed-site). -/
def dualizingClosedSiteDirectImage (R : Type (u + 1)) [CommRing R] [Finite R]
    {Y P : Scheme.{u}} (i : Y ⟶ P) [IsClosedImmersion i] : Prop :=
  ∀ L : _root_.DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1, u + 1} R)),
    (closedIdentityOpenProEtaleComparison R i).inv.app
          ((comparisonUpperStar.{u + 2, u}
            (ModuleCat.{u + 1, u + 1} R) Y).mapDerivedCategory.{u + 1, u + 1}.obj L.obj) ≫
        (compactSupportSiteComparison R (Compactification.ofIsProper i)).hom.app L ≫
        (comparisonUpperStar.{u + 2, u}
          (ModuleCat.{u + 1, u + 1} R) P).mapDerivedCategory.{u + 1, u + 1}.map
          ((closedIdentityOpenEtaleComparison R i).hom.app L.obj) =
      (fixedDirectImageComparisonIso R i).inv.app L

/-- All assertions of the closed dualizing site lemma, with its notation expanded.
The coefficient rings and their quotient map are the recorded valuation-ring quotients.
The predicates test Tor amplitude against every degree-zero module sheaf. The natural
isomorphisms are between actual B-module-valued derived functors, on all inputs.
Source: lem-coef-finite-dualizing.proof.md, paragraph 3
(blueprint: lem-coef-dualizing-closed-site). -/
def dualizingClosedSiteProperty
    (D : WeilConjectures.FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (m n : ℕ) (hm : 1 ≤ m) (hmn : m ≤ n) (r : ℕ)
    (Y : Scheme.{u}) [IsAffine Y]
    (i : Y ⟶ AffineSpace (ULift.{u} (Fin r)) (Spec (.of D.k))) [IsClosedImmersion i] : Prop :=
  let A := ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n)
  let B := ULift.{u + 1, u} (Padic.coefficientExtensionRing l E m)
  letI : Finite (Padic.coefficientExtensionRing l E n) :=
    Padic.finite_coefficientExtensionRing l E n (hm.trans hmn)
  letI : Finite (Padic.coefficientExtensionRing l E m) :=
    Padic.finite_coefficientExtensionRing l E m hm
  let φ : A →+* B := RingHom.ulift.{u + 1, u + 1} (Ideal.Quotient.factor
    (S := Padic.coefficientExtensionIdeal l E n)
    (T := Padic.coefficientExtensionIdeal l E m) (Ideal.pow_le_pow_right hmn))
  let P := AffineSpace (ULift.{u} (Fin r)) (Spec (.of D.k))
  let aP := P ↘ Spec (.of D.k)
  let c := Compactification.ofIsProper i
  letI := Etale.isLeftAdjoint_rightDerivedLowerShriekOfCompactification A c
  letI := Etale.isLeftAdjoint_rightDerivedLowerShriekOfCompactification B c
  let IA := (Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1, u + 1} A)
    c).rightAdjoint
  let IB := (Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1, u + 1} B)
    c).rightAdjoint
  let M := Etale.dualizingComplex A aP
  let MB := (pbcFixedScalarExtension P.smallEtaleTopology φ).obj M
  let N := IA.obj M
  let S := fun (R : Type (u + 1)) [CommRing R] (W : Scheme.{u}) ↦
    (comparisonUpperStar.{u + 2, u}
      (ModuleCat.{u + 1, u + 1} R) W).mapDerivedCategory.{u + 1, u + 1}
  let JA := (comparisonLowerStar (ModuleCat.{u + 1, u + 1} A) P).rightDerivedFunctor ⋙ IA ⋙ S A Y
  (∀ W : Scheme.{u}, W ∈ ({Y, P} : Set Scheme.{u}) →
    IsIso (pbcComparisonReductionMap.{u} W φ)) ∧
  (Etale.DerivedCategory.isBoundedConstructible A P ⊓
    (fun K ↦ ∃ a b : ℤ, a ≤ b ∧
      Etale.DerivedCategory.hasTorAmplitudeIn A P a b K)) M ∧
  (Etale.DerivedCategory.isBoundedConstructible A Y ⊓
    (fun K ↦ ∃ a b : ℤ, a ≤ b ∧
      Etale.DerivedCategory.hasTorAmplitudeIn A Y a b K)) N ∧
  (Etale.DerivedCategory.isBoundedConstructible B P ⊓
    (fun K ↦ ∃ a b : ℤ, a ≤ b ∧
      Etale.DerivedCategory.hasTorAmplitudeIn B P a b K)) MB ∧
  (Etale.DerivedCategory.isBoundedConstructible B Y ⊓
    (fun K ↦ ∃ a b : ℤ, a ≤ b ∧
      Etale.DerivedCategory.hasTorAmplitudeIn B Y a b K)) (IB.obj MB) ∧
  ((Etale.DerivedCategory.isBoundedConstructible A P).map (S A P) ⊓
    (fun K ↦ ∃ a b : ℤ, Scheme.HasFixedCoefficientProEtaleTorAmplitude P A K a b))
      ((S A P).obj M) ∧
  ((Etale.DerivedCategory.isBoundedConstructible A Y).map (S A Y) ⊓
    (fun K ↦ ∃ a b : ℤ, Scheme.HasFixedCoefficientProEtaleTorAmplitude Y A K a b))
      ((S A Y).obj N) ∧
  ((Etale.DerivedCategory.isBoundedConstructible B P).map (S B P) ⊓
    (fun K ↦ ∃ a b : ℤ, Scheme.HasFixedCoefficientProEtaleTorAmplitude P B K a b))
      ((S B P).obj MB) ∧
  ((Etale.DerivedCategory.isBoundedConstructible B Y).map (S B Y) ⊓
    (fun K ↦ ∃ a b : ℤ, Scheme.HasFixedCoefficientProEtaleTorAmplitude Y B K a b))
      ((S B Y).obj (IB.obj MB)) ∧
  ((Etale.DerivedCategory.isBoundedConstructible A Y).map (S A Y) ⊓
    (fun K ↦ ∃ a b : ℤ, Scheme.HasFixedCoefficientProEtaleTorAmplitude Y A K a b))
      (JA.obj ((S A P).obj M)) ∧
  dualizingClosedSiteDirectImage A i ∧ dualizingClosedSiteDirectImage B i ∧
  dualizingClosedSiteTransport A i M ∧ dualizingClosedSiteTransport B i MB

private theorem boundedConstructible_plus
    (R : Type (u + 1)) [CommRing R] [Finite R] (X : Scheme.{u})
    (K : Etale.DerivedCategoryModule R X)
    (hK : Etale.DerivedCategory.isBoundedConstructible R X K) :
    _root_.DerivedCategory.TStructure.t.plus K := by
  obtain ⟨_, a, b, _, hv⟩ := hK
  exact ⟨a, (_root_.DerivedCategory.isGE_iff K a).2 (fun q hq ↦ hv q (Or.inl hq))⟩

private theorem closed_direct_image
    (D : WeilConjectures.FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
    (hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (n : ℕ) (hn : 1 ≤ n) {Y P : Scheme.{u}}
    (aY : Y ⟶ Spec (.of D.k)) (aP : P ⟶ Spec (.of D.k))
    [LocallyOfFiniteType aY] [QuasiCompact aY] [IsSeparated aY]
    [LocallyOfFiniteType aP] [QuasiCompact aP] [IsSeparated aP]
    (i : Y ⟶ P) [IsClosedImmersion i] (hi : i ≫ aP = aY) :
    let R := ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n)
    let : Finite (Padic.coefficientExtensionRing l E n) :=
      Padic.finite_coefficientExtensionRing l E n hn
    dualizingClosedSiteDirectImage R i := by
  let R := ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n)
  let : Finite (Padic.coefficientExtensionRing l E n) :=
    Padic.finite_coefficientExtensionRing l E n hn
  let C := ModuleCat.{u + 1} R
  let F := (Etale.lowerStar C i).rightDerivedFunctor
  let I := F.rightAdjoint
  have : I.Additive := (Adjunction.ofIsLeftAdjoint F).right_adjoint_additive
  let H : _root_.DerivedCategory.Plus (Sheaf P.smallEtaleTopology C) := ⟨0, by
    exact ⟨0, inferInstance⟩⟩
  have hIH : _root_.DerivedCategory.TStructure.t.plus (I.obj H.obj) := by
    have hz := I.map_isZero (isZero_zero _)
    exact _root_.DerivedCategory.TStructure.t.plus.prop_of_iso hz.isoZero.symm
      (show _root_.DerivedCategory.TStructure.t.plus (0 : Etale.DerivedCategoryModule R Y)
        from ⟨0, inferInstance⟩)
  have h := closedIdentityOpenHomNormalization D l hl E n hn aY aP i hi
  change closedIdentityOpenHomNormalizationProperty D l E n hn aY aP i at h
  have h' := h H hIH
  change dualizingClosedSiteDirectImage R i
  intro L
  exact (h'.2.2.2 L).1

private theorem comparison_finiteTor
    (R : Type (u + 1)) [CommRing R] [Finite R] (X : Scheme.{u})
    (K : Etale.DerivedCategoryModule R X)
    (hK : (Etale.DerivedCategory.isBoundedConstructible R X ⊓
      (fun K ↦ ∃ a b : ℤ, a ≤ b ∧
        Etale.DerivedCategory.hasTorAmplitudeIn R X a b K)) K) :
    ((Etale.DerivedCategory.isBoundedConstructible R X).map
        (comparisonUpperStar (ModuleCat.{u + 1} R) X).mapDerivedCategory ⊓
      (fun K ↦ ∃ a b : ℤ, Scheme.HasFixedCoefficientProEtaleTorAmplitude X R K a b))
        ((comparisonUpperStar (ModuleCat.{u + 1} R) X).mapDerivedCategory.obj K) := by
  refine ⟨ObjectProperty.prop_map_obj _ _ hK.1, ?_⟩
  obtain ⟨a, b, hab, ht⟩ := hK.2
  exact ⟨a, b, hab, _root_.DerivedCategory.torAmplitudeIn_mapDerivedCategory_obj
    (comparisonUpperStar (ModuleCat.{u + 1} R) X)
    (Etale.DerivedCategory.hasTorAmplitudeIn_iff_torAmplitudeIn.mp ht)⟩

set_option backward.isDefEq.respectTransparency false in
private theorem closed_transport
    (R : Type (u + 1)) [CommRing R] [Finite R]
    {Y P : Scheme.{u}} [CompactSpace P] (i : Y ⟶ P) [IsClosedImmersion i]
    (H : Etale.DerivedCategoryModule R P)
    (hH : _root_.DerivedCategory.TStructure.t.plus H)
    (hIH :
      let := Etale.isLeftAdjoint_rightDerivedLowerShriekOfCompactification R
        (Compactification.ofIsProper i)
      _root_.DerivedCategory.TStructure.t.plus
      ((Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} R)
        (Compactification.ofIsProper i)).rightAdjoint.obj H)) :
    dualizingClosedSiteTransport R i H := by
  let C := ModuleCat.{u + 1} R
  let c := Compactification.ofIsProper i
  let F := Etale.rightDerivedLowerShriekOfCompactification C c
  let := Etale.isLeftAdjoint_rightDerivedLowerShriekOfCompactification R c
  let I := F.rightAdjoint
  let S := fun W : Scheme.{u} ↦ (comparisonUpperStar C W).mapDerivedCategory
  let U := (comparisonLowerStar C P).rightDerivedFunctor
  let J := U ⋙ I ⋙ S Y
  let η := (derivedComparisonAdjunction C P).unit
  let α := (S Y).map (I.map (η.app H))
  have hη : IsIso (η.app H) := isIso_derivedComparisonAdjunction_unit_app C P H hH
  have hα : IsIso α := by dsimp only [α]; infer_instance
  let e : (S Y).obj (I.obj H) ≅ J.obj ((S P).obj H) := asIso α
  have hs : _root_.DerivedCategory.TStructure.t.plus ((S Y).obj (I.obj H)) :=
    (DerivedCategory.plusEtaleOrigin_mapDerivedCategory_obj hIH).plus
  have hJ : _root_.DerivedCategory.TStructure.t.plus (J.obj ((S P).obj H)) :=
    _root_.DerivedCategory.TStructure.t.plus.prop_of_iso e hs
  let W : Scheme.FixedEtaleOriginWitness Y R ⟨J.obj ((S P).obj H), hJ⟩ :=
    ⟨⟨I.obj H, hIH⟩, e⟩
  refine ⟨hH, hIH, hη, hα, hJ, W, rfl, HEq.rfl, ?_⟩
  let adj := Adjunction.ofIsLeftAdjoint F
  let HP := (siteComparisonDerivedPullbackPlus P R).obj ⟨H, hH⟩
  let E := (specifiedExceptionalHomEquiv R c ⟨J.obj ((S P).obj H), hJ⟩ W HP).symm
    (𝟙 (J.obj ((S P).obj H)))
  have hE : E =
      (rightDerivedLowerShriekOfCompactification C c).map e.inv ≫
        (fixedCompactSupportComparisonIso R c).hom.app ⟨I.obj H, hIH⟩ ≫
        (S P).map (adj.counit.app H) := by
    apply (specifiedExceptionalHomEquiv R c _ W HP).injective
    dsimp only [E]
    rw [Equiv.apply_symm_apply]
    dsimp only [specifiedExceptionalHomEquiv, Equiv.trans_apply,
      Equiv.ofBijective_apply, Iso.homFromEquiv, Equiv.coe_fn_mk]
    change 𝟙 _ = e.inv ≫ (S Y).map
      ((adj.homEquiv _ _) ((derivedComparisonAdjunction C P).homEquiv _ _
        ((fixedCompactSupportComparisonIso R c).inv.app ⟨I.obj H, hIH⟩ ≫
          (rightDerivedLowerShriekOfCompactification C c).map e.hom ≫
          (rightDerivedLowerShriekOfCompactification C c).map e.inv ≫
          (fixedCompactSupportComparisonIso R c).hom.app ⟨I.obj H, hIH⟩ ≫
          (S P).map (adj.counit.app H))))
    erw [← (rightDerivedLowerShriekOfCompactification C c).map_comp_assoc,
      e.hom_inv_id, CategoryTheory.Functor.map_id, Category.id_comp, Iso.inv_hom_id_app_assoc]
    erw [(derivedComparisonAdjunction C P).homEquiv_unit]
    erw [← η.naturality (adj.counit.app H)]
    erw [adj.homEquiv_naturality_right, ← adj.homEquiv_symm_id,
      Equiv.apply_symm_apply, Category.id_comp]
    exact e.inv_hom_id.symm
  change (compactSupportSiteComparison R c).inv.app ⟨I.obj H, hIH⟩ ≫
    (rightDerivedLowerShriekOfCompactification C c).map α ≫ E = _
  rw [hE]
  erw [← (rightDerivedLowerShriekOfCompactification C c).map_comp_assoc]
  have he : α ≫ e.inv = 𝟙 _ := e.hom_inv_id
  erw [he, CategoryTheory.Functor.map_id, Category.id_comp,
    compactSupportComparisonNormalization R c, Iso.inv_hom_id_app_assoc]

/-- Bounded site transport of the closed exceptional dualizing objects.
Source: main-20261015 blueprint, lem-coef-finite-dualizing.proof.md, paragraph 3
(blueprint: lem-coef-dualizing-closed-site).

Proof:
1. closedDualizingEtaleFiniteness supplies the four ordinary bounded constructible
   finite-Tor objects. Bounded constructibility supplies each required lower bound.
2. The generic exact comparison functor preserves the Tor interval, and its image
   property gives pro-etale constructibility. The existing coefficient-mate theorem
   proves invertibility of the actual B-linear coefficient comparison.
3. The actual bounded-below comparison unit is invertible. Applying I and S gives
   alpha and the explicit retained origin (IH, asIso alpha) for JSH. Transfer the
   finite-Tor constructible property across this isomorphism.
4. The input-independent direct-image clause of closedIdentityOpenHomNormalization
   gives the required identity-open direct-image equality at both coefficient levels.
5. Compute the inverse identity in specifiedExceptionalHomEquiv by injectivity,
   unit naturality and ordinary adjunction naturality with beta(counit)=identity.
   Cancel alpha and use compactSupportComparisonNormalization to obtain the stated
   counit equation for that explicit retained witness.
6. These constructions apply also to empty Y and equal coefficient levels. They
   require neither an unbounded pro-etale adjunction nor finite Tor dimension of
   the quotient B as an A-module. -/
theorem dualizingClosedSite
    (D : WeilConjectures.FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
    (_hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (m n : ℕ) (hm : 1 ≤ m) (hmn : m ≤ n) (r : ℕ)
    (Y : Scheme.{u}) [IsAffine Y]
    (i : Y ⟶ AffineSpace (ULift.{u} (Fin r)) (Spec (.of D.k))) [IsClosedImmersion i] :
    dualizingClosedSiteProperty D l E m n hm hmn r Y i := by
  let A := ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n)
  let B := ULift.{u + 1, u} (Padic.coefficientExtensionRing l E m)
  let : Finite (Padic.coefficientExtensionRing l E n) :=
    Padic.finite_coefficientExtensionRing l E n (hm.trans hmn)
  let : Finite (Padic.coefficientExtensionRing l E m) :=
    Padic.finite_coefficientExtensionRing l E m hm
  let φ : A →+* B := RingHom.ulift.{u + 1, u + 1} (Ideal.Quotient.factor
    (S := Padic.coefficientExtensionIdeal l E n)
    (T := Padic.coefficientExtensionIdeal l E m) (Ideal.pow_le_pow_right hmn))
  let P := AffineSpace (ULift.{u} (Fin r)) (Spec (.of D.k))
  let aP := P ↘ Spec (.of D.k)
  let c := Compactification.ofIsProper i
  let := Etale.isLeftAdjoint_rightDerivedLowerShriekOfCompactification A c
  let := Etale.isLeftAdjoint_rightDerivedLowerShriekOfCompactification B c
  let IA := (Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A)
    c).rightAdjoint
  let IB := (Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} B)
    c).rightAdjoint
  let M := Etale.dualizingComplex A aP
  let MB := (pbcFixedScalarExtension P.smallEtaleTopology φ).obj M
  let N := IA.obj M
  let S := fun (R : Type (u + 1)) [CommRing R] (W : Scheme.{u}) ↦
    (comparisonUpperStar (ModuleCat.{u + 1} R) W).mapDerivedCategory
  let JA := (comparisonLowerStar (ModuleCat.{u + 1} A) P).rightDerivedFunctor ⋙ IA ⋙ S A Y
  obtain ⟨hM, hN, hMB, hNB⟩ :=
    closedDualizingEtaleFiniteness D l _hl E m n hm hmn r Y i
  have tA := closed_transport A i M (boundedConstructible_plus A P M hM.1)
    (boundedConstructible_plus A Y N hN.1)
  have tB := closed_transport B i MB (boundedConstructible_plus B P MB hMB.1)
    (boundedConstructible_plus B Y (IB.obj MB) hNB.1)
  have hSM := comparison_finiteTor A P M hM
  have hSN := comparison_finiteTor A Y N hN
  have hSMB := comparison_finiteTor B P MB hMB
  have hSNB := comparison_finiteTor B Y (IB.obj MB) hNB
  have hJ : ((Etale.DerivedCategory.isBoundedConstructible A Y).map (S A Y) ⊓
      (fun K ↦ ∃ a b : ℤ, Scheme.HasFixedCoefficientProEtaleTorAmplitude Y A K a b))
        (JA.obj ((S A P).obj M)) := by
    obtain ⟨hH, hIH, hη, hα, hJ, W, hW, he⟩ := tA
    let η := (derivedComparisonAdjunction (ModuleCat.{u + 1} A) P).unit
    let α := (S A Y).map (IA.map (η.app M))
    let : IsIso α := hα
    let e : (S A Y).obj N ≅ JA.obj ((S A P).obj M) := asIso α
    refine ⟨(ObjectProperty.map _ _).prop_of_iso e hSN.1, ?_⟩
    obtain ⟨a, b, hab, ht⟩ := hSN.2
    exact ⟨a, b, hab,
      (_root_.DerivedCategory.torAmplitudeIn _ a b).prop_of_iso e ht⟩
  have dA := closed_direct_image D l _hl E n (hm.trans hmn) (i ≫ aP) aP i rfl
  have dB := closed_direct_image D l _hl E m hm (i ≫ aP) aP i rfl
  exact ⟨(fun W _ ↦ pbcComparisonReductionMap_isIso W φ),
    hM, hN, hMB, hNB, hSM, hSN, hSMB, hSNB, hJ, dA, dB, tA, tB⟩

end AlgebraicGeometry.ProEtale
