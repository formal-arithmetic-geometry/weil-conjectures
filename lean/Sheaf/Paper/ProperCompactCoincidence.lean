/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NP
-/
module
public import Sheaf.Paper.OrdinaryCompactCohomology
public import Sheaf.Paper.CompactSupportCoefficientAction
public import Sheaf.Paper.SfDerivedDirectImage
public import Sheaf.AlgebraicGeometry.ProEtaleConstantDerivedDirectImage
public import Sheaf.Paper.SfIntegralReductionTower
public import Sheaf.Paper.DerivedScalarExtensionRestrictionAdjunction
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import WeilConjectures.Compactification.RefinementCategory
import Sheaf.Paper.ProperFiniteNormalization
import Sheaf.Paper.FiniteRingConstructibleDerivedOrigin
import Sheaf.Paper.ProperCompactIntegralComparisons
import Sheaf.Paper.ProperCompactRationalFunctorComparison
import Sheaf.Paper.ProperCompactCoefficientActionComparison
/-!
# Proper coincidence of compact-support and ordinary cohomology

Source: literature/blueprint/main-20261015/blueprint/sec-zeta-weil/sk-input-weights/
prop-weil-proper-compact-coincidence.md (blueprint: prop-weil-proper-compact-coincidence).

## Main statements

* `WeilConjectures.properCompactPointOver`: the identity structure morphism on the point.
* `WeilConjectures.properCompactCoincidence`: proper comparison for all four coefficients.
-/
@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures
open AlgebraicallyClosedCoefficients (Coefficient)

/-- The point has its identity structure morphism over the fixed geometric field.
Source: blueprint structure morphism a_Y and its point s = Spec k
(blueprint: prop-weil-proper-compact-coincidence). -/
instance properCompactPointOver (D : FiniteFieldDatum.{u}) :
    (Spec (CommRingCat.of D.k)).Over (Spec (CommRingCat.of D.k)) :=
  ⟨𝟙 _⟩

private theorem extendFiniteComparison
    {A B C : Type*} [Category A] [Category B] [Category C]
    (F : A ⥤ B) [F.Full] (G H : B ⥤ C) (Q : ObjectProperty B)
    (hw : ∀ K : Q.FullSubcategory, ∃ M : A, Nonempty (F.obj M ≅ K.obj))
    (α : F ⋙ G ≅ F ⋙ H) :
    ∃! t : Q.ι ⋙ G ≅ Q.ι ⋙ H,
      ∀ (K : Q.FullSubcategory) (M : A) (e : F.obj M ≅ K.obj),
        t.app K = G.mapIso e.symm ≪≫ α.app M ≪≫ H.mapIso e := by
  classical
  choose M e using hw
  let e' (K : Q.FullSubcategory) : F.obj (M K) ≅ K.obj := (e K).some
  have hn {U V : A} (f : F.obj U ⟶ F.obj V) :
      G.map f ≫ α.hom.app V = α.hom.app U ≫ H.map f := by
    simpa only [Functor.comp_map, Functor.map_preimage] using
      α.hom.naturality (F.preimage f)
  let t : Q.ι ⋙ G ≅ Q.ι ⋙ H := NatIso.ofComponents
    (fun K ↦ G.mapIso (e' K).symm ≪≫ α.app (M K) ≪≫ H.mapIso (e' K)) (by
      intro K L f
      have h := congrArg
        (fun z ↦ G.map (e' K).inv ≫ z ≫ H.map (e' L).hom)
        (hn ((e' K).hom ≫ f.hom ≫ (e' L).inv))
      simpa only [Functor.map_comp, Category.assoc, Iso.map_inv_hom_id_assoc,
        Iso.map_inv_hom_id, Functor.map_id,
        Category.id_comp, Category.comp_id, Functor.comp_map, ObjectProperty.ι_map, Iso.app_hom,
        Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom] using h)
  have ht (K : Q.FullSubcategory) (N : A) (d : F.obj N ≅ K.obj) :
      t.app K = G.mapIso d.symm ≪≫ α.app N ≪≫ H.mapIso d := by
    apply Iso.ext
    have h := congrArg (fun z ↦ G.map d.inv ≫ z ≫ H.map (e' K).hom)
      (hn (d.hom ≫ (e' K).inv))
    simpa only [t, Iso.app_hom, NatIso.ofComponents_hom_app, Iso.trans_hom, Functor.mapIso_hom,
      Iso.symm_hom, Functor.map_comp, Category.assoc, Iso.map_inv_hom_id_assoc,
      Iso.map_inv_hom_id, Functor.map_id,
      Category.id_comp, Category.comp_id] using h
  refine ⟨t, ht, ?_⟩
  intro t' ht'
  apply Iso.ext
  apply NatTrans.ext
  funext K
  exact congrArg Iso.hom ((ht' K (M K) (e' K)).trans (ht K (M K) (e' K)).symm)

private theorem finiteOrigin
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (n : ℕ) (hn : 1 ≤ n)
    [Finite (Padic.coefficientExtensionRing l E n)]
    {T : Scheme.{u}} (K : Scheme.proEtaleDerivedCategory T (Padic.coefficientExtensionRing l E n))
    (hK : Scheme.intrinsicFiniteTorsionConstructible l E n hn T K) :
    ∃ L : DerivedCategory.Plus
        (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1}
          (Padic.coefficientExtensionRing l E n)))),
      Nonempty ((Scheme.sfIntrinsicDerivedEquivalence T (Padic.coefficientExtensionRing l E
        n)).functor.obj
        (((AlgebraicGeometry.ProEtale.comparisonUpperStar
          (ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing l E n)))
            T).mapDerivedCategory).obj L.obj) ≅ K) := by
  classical
  let : Finite (Padic.coefficientExtensionRing l E n) :=
    Padic.finite_coefficientExtensionRing l E n hn
  have : (AlgebraicGeometry.ProEtale.finiteCoefficientIntrinsicRealization
      T (Padic.coefficientExtensionRing l E n)).Additive :=
    AlgebraicGeometry.ProEtale.finiteCoefficientIntrinsicRealization_additive T
      (Padic.coefficientExtensionRing l E n)
  have : PreservesFiniteLimits
      (AlgebraicGeometry.ProEtale.finiteCoefficientIntrinsicRealization T
        (Padic.coefficientExtensionRing l E n)) :=
    AlgebraicGeometry.ProEtale.finiteCoefficientIntrinsicRealization_preservesFiniteLimits
      T (Padic.coefficientExtensionRing l E n)
  have : PreservesFiniteColimits
      (AlgebraicGeometry.ProEtale.finiteCoefficientIntrinsicRealization T
        (Padic.coefficientExtensionRing l E n)) :=
    AlgebraicGeometry.ProEtale.finiteCoefficientIntrinsicRealization_preservesFiniteColimits
      T (Padic.coefficientExtensionRing l E n)
  obtain ⟨a, ha⟩ := hK.1.bddBelow
  obtain ⟨b, hb⟩ := hK.1.bddAbove
  have hv (q : ℤ) (hq : q < min a b ∨ max a b < q) :
      IsZero ((DerivedCategory.homologyFunctor _ q).obj K) := by
    by_contra hz
    rcases hq with hq | hq
    · exact (not_lt_of_ge ((min_le_left a b).trans (ha hz))) hq
    · exact (not_lt_of_ge ((hb hz).trans (le_max_right a b))) hq
  obtain ⟨L, ⟨e⟩⟩ := (Scheme.finiteRing_constructibleDerived_origin T
    (Padic.coefficientExtensionRing l E n)).2.2.1 K
    |>.mpr ⟨hK.2, min a b, max a b, min_le_max, hv⟩
  obtain ⟨c, d, hcd, hd⟩ := L.property.2
  have hplus : DerivedCategory.TStructure.t.plus L.obj :=
    ⟨c, (DerivedCategory.isGE_iff L.obj c).mpr (fun q hq ↦ hd q (Or.inl hq))⟩
  refine ⟨⟨L.obj, hplus⟩, ⟨?_⟩⟩
  exact ((Functor.mapDerivedCategoryCompIso
    (AlgebraicGeometry.ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing l E n))) T)
    (AlgebraicGeometry.ProEtale.finiteCoefficientIntrinsicRealization T
      (Padic.coefficientExtensionRing l E n))).app
      L.obj).symm ≪≫ e

private theorem finiteCompactificationComparison
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (n : ℕ) (hn : 1 ≤ n)
    [Finite (Padic.coefficientExtensionRing l E n)]
    {X Y : Scheme.{u}} {f : X ⟶ Y} [QuasiCompact f]
    (c d : Compactification f) :
    Nonempty ((intrinsicFiniteTorsionConstructible l E n hn X).ι ⋙
        sfIntrinsicCompactSupport c (Padic.coefficientExtensionRing l E n) ≅
      (intrinsicFiniteTorsionConstructible l E n hn X).ι ⋙
        sfIntrinsicCompactSupport d (Padic.coefficientExtensionRing l E n)) := by
  classical
  let : Finite (Padic.coefficientExtensionRing l E n) :=
    Padic.finite_coefficientExtensionRing l E n hn
  let ν := (AlgebraicGeometry.ProEtale.comparisonUpperStar
    (ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing l E n))) X).mapDerivedCategory
  let Q := Scheme.sfIntrinsicDerivedEquivalence X (Padic.coefficientExtensionRing l E n)
  let F := DerivedCategory.Plus.ι ⋙ ν ⋙ Q.functor
  have : F.Full := ⟨fun {L M} f ↦ by
    obtain ⟨k, hk⟩ :=
      (AlgebraicGeometry.ProEtale.bijective_comparisonUpperStar_mapDerivedCategory_map
        L.obj M.obj M.property).2 (Q.functor.preimage f)
    exact ⟨ObjectProperty.homMk k, by
      change Q.functor.map (ν.map k) = f
      exact (congrArg Q.functor.map hk).trans (Q.functor.map_preimage f)⟩⟩
  let α : F ⋙ Scheme.sfIntrinsicCompactSupport c (Padic.coefficientExtensionRing l E n) ≅
      F ⋙ Scheme.sfIntrinsicCompactSupport d (Padic.coefficientExtensionRing l E n) :=
    Functor.isoWhiskerLeft (DerivedCategory.Plus.ι ⋙ ν)
      (AlgebraicGeometry.ProEtale.sfIntrinsicCompactSupportComparison
        (Padic.coefficientExtensionRing l E n) c) ≪≫
    Functor.isoWhiskerRight
      (AlgebraicGeometry.ProEtale.fixedCompactSupportOriginIso (ULift.{u + 1}
        (Padic.coefficientExtensionRing l E n)) c d)
      (Scheme.sfIntrinsicDerivedEquivalence Y (Padic.coefficientExtensionRing l E n)).functor ≪≫
    (Functor.isoWhiskerLeft (DerivedCategory.Plus.ι ⋙ ν)
      (AlgebraicGeometry.ProEtale.sfIntrinsicCompactSupportComparison
        (Padic.coefficientExtensionRing l E n) d)).symm
  obtain ⟨t, _, _⟩ := extendFiniteComparison F (Scheme.sfIntrinsicCompactSupport c
    (Padic.coefficientExtensionRing l E n))
    (Scheme.sfIntrinsicCompactSupport d (Padic.coefficientExtensionRing l E n)) _
    (fun K ↦ finiteOrigin l E n hn K.obj K.property) α
  exact ⟨t⟩

/-- For a proper structure morphism over the geometric field of the finite-field
datum, compact-support and ordinary direct images agree for finite, integral,
rational, and algebraically closed coefficients. Their sections and cohomology
objects are consequently isomorphic for every bounded constructible input.
For rational and algebraically closed coefficients the ordinary functor is
represented by the compact-support formula at the identity compactification;
the algebraically closed clause holds for every normalized coefficient action at
`c` and at the identity compactification, not only for some choice of them;
the image clauses also compare with the recorded ordinary tower values.

Source: literature/blueprint/main-20261015/blueprint/sec-zeta-weil/sk-input-weights/
prop-weil-proper-compact-coincidence.proof.md (blueprint: prop-weil-proper-compact-coincidence).
Proof: (1) Use the finite-field and coefficient data of
`def-weil-ordinary-compact-cohomology`; properness of the structure morphism is
`def-weil-proper-morphism`.  The identity compactification is supplied by
`def-weil-compactifications-refinements`.  For its identity open immersion,
`def-weil-extension-by-zero` identifies extension by zero with the identity,
so `def-compact-support-direct-image-detailed` gives the finite-level direct-image
isomorphism.  The etale-origin and compactification-coherence clauses are those
of `lem-sf-proetale-constructible-origin` and
`prop-compactification-coherence-detailed`.
(2) For integral coefficients, `def-weil-integral-rational-qbar-compact-support`
and `def-weil-derived-direct-image` give the two towers.  Their terms and
transition maps agree by `lem-sf-compact-support-restriction-of-scalars`, since
the identity extension is literally the identity.
(3) Localization through `def-weil-rationalization-karoubi` preserves the
comparison, and `def-weil-algebraically-closed-coefficients` transports it to
common finite stages, yielding the rational and algebraically closed clauses.
(4) Applying the geometric-point fibre and degreewise cohomology in
`def-weil-ordinary-compact-cohomology` gives each displayed cohomology
isomorphism, naturally in the input and in the degree.
-/
theorem properCompactCoincidence
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (Ω : Type u) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    (E₀ : Padic.FiniteCoefficientFields l Ω) (Y : Scheme.{u})
    [Y.Over (Spec (CommRingCat.of D.k))]
    [IsProper (Y ↘ Spec (CommRingCat.of D.k))]
    (c : Compactification (Y ↘ Spec (CommRingCat.of D.k)))
    (n : ℕ) (hn : 1 ≤ n) :
    Nonempty ((intrinsicFiniteTorsionConstructible l (Coefficient.{u} l Ω E₀)
        n hn Y).ι ⋙ @sfIntrinsicCompactSupport Y (Spec (CommRingCat.of D.k))
          (Y ↘ Spec (CommRingCat.of D.k)) c
          (Padic.coefficientExtensionRing l (Coefficient.{u} l Ω E₀) n)
          _ (Padic.finite_coefficientExtensionRing l (Coefficient.{u} l Ω E₀) n hn) ≅
      (intrinsicFiniteTorsionConstructible l (Coefficient.{u} l Ω E₀) n hn Y).ι ⋙
        proEtaleConstantDerivedDirectImage (Y ↘ Spec (CommRingCat.of D.k))
          (Padic.coefficientExtensionRing l (Coefficient.{u} l Ω E₀) n)) ∧
    Nonempty (sfCompactSupportFiniteIntegralFunctor l D.k (finiteFieldDatumPrimeUnit D l hl)
        c (Coefficient.{u} l Ω E₀) ⋙
          (sfIntegralConstructible l (Coefficient.{u} l Ω E₀) (Spec (.of D.k))).ι ≅
      (sfIntegralConstructible l (Coefficient.{u} l Ω E₀) Y).ι ⋙
        sfCompletedDerivedDirectImage l (Coefficient.{u} l Ω E₀) (Y ↘ Spec (.of D.k))) ∧
    Nonempty (sfCompactSupportFiniteFunctor l D.k (finiteFieldDatumPrimeUnit D l hl)
        c (Coefficient.{u} l Ω E₀) ≅
      sfCompactSupportFiniteFunctor l D.k (finiteFieldDatumPrimeUnit D l hl)
        (Compactification.ofIsProper (Y ↘ Spec (.of D.k))) (Coefficient.{u} l Ω E₀)) ∧
    (∀ S : SfCompactSupportCoefficientAction l D.k (finiteFieldDatumPrimeUnit D l hl) Ω c,
      ∀ S₀ : SfCompactSupportCoefficientAction l D.k (finiteFieldDatumPrimeUnit D l hl) Ω
          (Compactification.ofIsProper (Y ↘ Spec (.of D.k))),
        Nonempty (S.system.functor ≅ S₀.system.functor)) ∧
    (∀ K : (intrinsicFiniteTorsionConstructible l (Coefficient.{u} l Ω E₀) n hn
        Y).FullSubcategory,
      Nonempty (finiteCompactSections D l (Coefficient.{u} l Ω E₀) Y c n hn K.obj ≅
        finiteOrdinarySections D l (Coefficient.{u} l Ω E₀) Y n hn K.obj) ∧
      ∀ i : ℤ, Nonempty (finiteCompactCohomology D l
        (Coefficient.{u} l Ω E₀) Y c n hn K.obj i ≅
          finiteOrdinaryCohomology D l (Coefficient.{u} l Ω E₀) Y n hn K.obj i)) ∧
    (∀ K : sfIntegralConstructibleCategory l (Coefficient.{u} l Ω E₀) Y,
      Nonempty (sfIntegralCompactSupportValue l (Coefficient.{u} l Ω E₀) D.k
        (finiteFieldDatumPrimeUnit D l hl) c K ≅
          integralImage D l hl (Coefficient.{u} l Ω E₀) Y K) ∧
      Nonempty (integralCompactSections D l hl (Coefficient.{u} l Ω E₀) Y c K ≅
        integralOrdinarySections D l hl (Coefficient.{u} l Ω E₀) Y K) ∧
      ∀ i : ℤ, Nonempty (integralCompactCohomology D l hl (Coefficient.{u} l Ω E₀)
        Y c K i ≅ integralOrdinaryCohomology D l hl (Coefficient.{u} l Ω E₀) Y K i)) ∧
    (∀ K : sfRationalConstructibleCategory l (Coefficient.{u} l Ω E₀) Y,
      Nonempty (sfRationalCompactSupportValue l (Coefficient.{u} l Ω E₀) D.k
        (finiteFieldDatumPrimeUnit D l hl) c K.obj ≅
          rationalImage D l hl (Coefficient.{u} l Ω E₀) Y K) ∧
      Nonempty (rationalCompactSections D l hl (Coefficient.{u} l Ω E₀) Y c K ≅
        rationalOrdinarySections D l hl (Coefficient.{u} l Ω E₀) Y K) ∧
      ∀ i : ℤ, Nonempty (rationalCompactCohomology D l hl (Coefficient.{u} l Ω E₀)
        Y c K i ≅ rationalOrdinaryCohomology D l hl (Coefficient.{u} l Ω E₀) Y K i)) ∧
    (∀ K : generalAlgebraicallyClosedConstructibleCategory l Ω Y,
      Nonempty (sfQbarCompactSupportValue l D.k (finiteFieldDatumPrimeUnit D l hl)
        Ω c K.stage K.obj.obj ≅ qbarImage D l hl Y Ω K) ∧
      Nonempty (qbarCompactSections D l hl Y Ω c K ≅ qbarOrdinarySections D l hl Y Ω K) ∧
      ∀ i : ℤ, Nonempty (qbarCompactCohomology D l hl Y Ω c K i ≅
        qbarOrdinaryCohomology D l hl Y Ω K i)) := by
  classical
  let E := Coefficient.{u} l Ω E₀
  let A := Padic.coefficientExtensionRing l E n
  let : Finite A := Padic.finite_coefficientExtensionRing l E n hn
  obtain ⟨ec⟩ := finiteCompactificationComparison l E n hn c
    (Compactification.ofIsProper (Y ↘ Spec (.of D.k)))
  let e := ec ≪≫ Functor.isoWhiskerLeft _
    (PurityFiniteSetting.properFiniteIdentityNormalization A (Y ↘ Spec (.of D.k)))
  have hi := properCompactIntegralComparisons D l hl Y c E
  refine ⟨⟨e⟩, hi.1, properCompactRationalFunctorComparison D l hl Y c E,
    properCompactCoefficientActionComparison D l hl Ω Y c, ?_, ?_, ?_, ?_⟩
  · intro K
    let q := ((pointFiniteSections D.k A).mapDerivedCategory).mapIso (e.app K)
    refine ⟨⟨q⟩, fun i ↦ ⟨?_⟩⟩
    exact (DerivedCategory.homologyFunctor _ i).mapIso q
  · intro K
    obtain ⟨q⟩ := hi.2 K
    let r := (pointIntegralFibre D l hl E).mapIso q
    refine ⟨⟨q⟩, ⟨r⟩, fun i ↦ ⟨?_⟩⟩
    exact (DerivedCategory.coefficientFgCohomology _ _ i).mapIso r
  · intro K
    obtain ⟨q⟩ := hi.2 K.obj
    let r := (sfRationalConstructibleLocalization l E (Spec (.of D.k))).mapIso q
    let t := (pointRationalFibre D l hl E).mapIso r
    refine ⟨⟨r⟩, ⟨t⟩, fun i ↦ ⟨?_⟩⟩
    exact (DerivedCategory.coefficientFdCohomology E i).mapIso t
  · intro K
    obtain ⟨q⟩ := (properCompactIntegralComparisons D l hl Y c
      (Coefficient.{u} l Ω K.stage)).2 K.obj.obj
    let r := (sfRationalConstructibleLocalization l (Coefficient.{u} l Ω K.stage)
      (Spec (.of D.k))).mapIso q
    let t := (GeneralAlgebraicallyClosedCoefficients.inclusion
      (l := l) (Ω := Ω) (Y := Spec (.of D.k)) K.stage).mapIso r
    let v := (pointQbarFibre D l hl Ω).mapIso t
    refine ⟨⟨t⟩, ⟨v⟩, fun i ↦ ⟨?_⟩⟩
    exact (DerivedCategory.coefficientQbarCohomology l Ω i).mapIso v

end WeilConjectures
