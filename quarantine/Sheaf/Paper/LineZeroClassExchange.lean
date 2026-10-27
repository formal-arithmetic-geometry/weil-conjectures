/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q43
-/
module

public import Sheaf.Paper.PurityFiniteSetting
public import Sheaf.Paper.PurityVectorBundleZeroSection
public import Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted
public import Sheaf.AlgebraicGeometry.CartierKummerMap
public import Sheaf.AlgebraicGeometry.SfIntrinsicCompactSupport
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import Sheaf.AlgebraicGeometry.FixedEtaleOriginWitness
public import Sheaf.AlgebraicGeometry.ComparisonDerivedPullbackFixed
public import Sheaf.Paper.CanonicalOriginCompactSupportComposition
public import Sheaf.Paper.CanonicalFiniteLevelCompactSupportBaseChange
public import Sheaf.Paper.CompactFiberStalk
public import Sheaf.AlgebraicGeometry.CanonicalCompactSupportSiteComparison
public import Sheaf.AlgebraicGeometry.OrdinarySupportedCartierKummer
public import Sheaf.Paper.FiniteTorAmplitudeSites
public import Sheaf.Paper.LineKummerFieldRealization
public import Sheaf.Paper.SectionCompactSourceExchange
import Sheaf.Paper.SupportedCartierDerivedPullback

/-! # Exchange for the compact image of a line zero-section class

Source: blueprint latest, sec-smooth-purity/sk-prop-an,
thm-pur-rank-one-thom.proof.md, Step 3 and Step 2, first paragraph
(blueprint: lem-pur-line-zero-class-exchange).

The fixed-scalar D+ presentation is the one used by the recorded Kummer and
section-source interfaces. The positive coefficient exponent is written n+1;
the equality with P.level retains every positive level. A fibre basis is encoded
by a Cartesian square whose upper left corner is the affine line and whose
zero section is the pulled-back zero section. Thus every choice of basis is covered.
-/

@[expose] public noncomputable section
-- Replaying tactic states for this large derived-functor assembly costs ten seconds.
set_option linter.unusedTactic false
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.LineZeroClass
open Scheme LineKummerField

/-- Closedness of the existing chosen zero section, with no additional hypothesis.
Source: def-pur-vector-bundle-zero-section, zeroSection_spec
(blueprint: lem-pur-line-zero-class-exchange). -/
instance zeroClosed (P : WeilConjectures.PurityFiniteSetting.{u})
    {B : Scheme.{u}} {hB : B ⟶ Spec (.of P.field.k)}
    [IsSeparated hB] [LocallyOfFiniteType hB] [QuasiCompact hB]
    (V : PurityVectorBundle P B hB 1) : IsClosedImmersion V.zeroSection :=
  V.zeroSection_spec.2.1

variable (l : ℕ) [Fact l.Prime] (F : Type u) [Field F]
  [Algebra (Padic l) F] [FiniteDimensional (Padic l) F] (n : ℕ)

/-- The derived pullback of the prescribed twist comparison, including its shift.
Source: blueprint rank-one Thom proof, Step 3; exact inverse image commutes with shifts
(blueprint: lem-pur-line-zero-class-exchange). -/
@[irreducible]
def twistPull {X' X : Scheme.{u}} (v : X' ⟶ X)
    (p : (ProEtale.upperStar (ModuleCat.{u + 1} (finiteTateCoefficient l F n)) v).obj
      (finiteTateProSheaf l F n X 1) ≅ finiteTateProSheaf l F n X' 1) :
    (ProEtale.upperStar
      (ModuleCat.{u + 1} (finiteTateCoefficient l F n)) v).mapDerivedCategoryPlus.obj
        ((proLine l F n X)⟦(2 : ℤ)⟧) ≅ (proLine l F n X')⟦(2 : ℤ)⟧ :=
  ((ProEtale.upperStar
    (ModuleCat.{u + 1} (finiteTateCoefficient l F n)) v).mapDerivedCategoryPlus.commShiftIso
      (2 : ℤ)).app _ ≪≫
    (shiftFunctor _ (2 : ℤ)).mapIso
      ((Functor.mapDerivedCategoryPlusSingleFunctor
        (ProEtale.upperStar (ModuleCat.{u + 1} (finiteTateCoefficient l F n)) v) 0).app _ ≪≫
          (DerivedCategory.Plus.singleFunctor _ 0).mapIso p)

/-- Identity source exchange and equality of the actual compact zero-class arrows.
The target comparison is the root-normalized pullback of the prescribed Tate line.
Source: blueprint rank-one Thom proof, Step 3
(blueprint: lem-pur-line-zero-class-exchange). -/
@[irreducible]
def Exchange {B X B' X' : Scheme.{u}} {π : X ⟶ B}
    (c : Compactification π) (z : B ⟶ X) [IsClosedImmersion z] (hz : z ≫ π = 𝟙 B)
    (hI : z.ker.IsInvertible) (hX : IsUnit (l : Γ(X, ⊤)))
    (g : B' ⟶ B) (v : X' ⟶ X) (π' : X' ⟶ B') (sq : IsPullback v π' π g)
    (z' : B' ⟶ X') [IsClosedImmersion z'] (hz' : z' ≫ π' = 𝟙 B')
    (sqZ : ChosenCartesianSquare g z' z v)
    (hI' : z'.ker.IsInvertible) (hX' : IsUnit (l : Γ(X', ⊤)))
    (p : (ProEtale.upperStar (ModuleCat.{u + 1} (finiteTateCoefficient l F n)) v).obj
      (finiteTateProSheaf l F n X 1) ≅ finiteTateProSheaf l F n X' 1) : Prop :=
  (ProEtale.upperStar
    (ModuleCat.{u + 1} (finiteTateCoefficient l F n)) g).mapDerivedCategoryPlus.map
      (SectionCompactSource.proSource (finiteTateCoefficient l F n) c z hz) ≫
    SectionCompactSource.proExchange (finiteTateCoefficient l F n) sq c
      (SectionCompactSource.proSupported (finiteTateCoefficient l F n) z) ≫
    (ProEtale.rightDerivedLowerShriekOfCompactificationPlus
      (ModuleCat.{u + 1} (finiteTateCoefficient l F n)) (c.ofIsPullback sq)).map
        (SectionCompactSource.proBeta (finiteTateCoefficient l F n) sqZ) =
    (SectionCompactSource.proConstantPull (finiteTateCoefficient l F n) g).hom ≫
      SectionCompactSource.proSource (finiteTateCoefficient l F n)
        (c.ofIsPullback sq) z' hz' ∧
  IsIso (SectionCompactSource.proExchange (finiteTateCoefficient l F n) sq c
    ((proLine l F n X)⟦(2 : ℤ)⟧)) ∧
  (ProEtale.upperStar
    (ModuleCat.{u + 1} (finiteTateCoefficient l F n)) g).mapDerivedCategoryPlus.map
      (proTau l F n c z hz hI hX) ≫
    SectionCompactSource.proExchange (finiteTateCoefficient l F n) sq c
      ((proLine l F n X)⟦(2 : ℤ)⟧) ≫
    (ProEtale.rightDerivedLowerShriekOfCompactificationPlus
      (ModuleCat.{u + 1} (finiteTateCoefficient l F n)) (c.ofIsPullback sq)).map
        (twistPull l F n v p).hom =
    (SectionCompactSource.proConstantPull (finiteTateCoefficient l F n) g).hom ≫
      proTau l F n (c.ofIsPullback sq) z' hz' hI' hX'

/-- The geometric-stalk arrow, after compact-fibre exchange and the actual target
site comparison, is the realization of the ordinary etale compact origin class.
Source: blueprint rank-one Thom proof, Step 2, first paragraph
(blueprint: lem-pur-line-zero-class-exchange). -/
@[irreducible]
def FibreFormula
    (hA : ((l ^ (n + 1) : ℕ) : finiteTateCoefficient l F n) = 0)
    {B X : Scheme.{u}} {π : X ⟶ B} (c : Compactification π)
    (z : B ⟶ X) [IsClosedImmersion z] (hz : z ≫ π = 𝟙 B)
    (hI : z.ker.IsInvertible) (hX : IsUnit (l : Γ(X, ⊤)))
    (Ω : Type u) [Field Ω] (b : Spec (.of Ω) ⟶ B)
    (v : AffineSpace (ULift.{u} (Fin 1)) (Spec (.of Ω)) ⟶ X)
    (sq : IsPullback v
      (AffineSpace (ULift.{u} (Fin 1)) (Spec (.of Ω)) ↘ Spec (.of Ω)) π b)
    (hIΩ : (AffineSpace.zeroSection (ULift.{u} (Fin 1)) (Spec (.of Ω))).ker.IsInvertible)
    (hXΩ : IsUnit (l : Γ(AffineSpace (ULift.{u} (Fin 1)) (Spec (.of Ω)), ⊤)))
    (p : (ProEtale.upperStar (ModuleCat.{u + 1} (finiteTateCoefficient l F n)) v).obj
      (finiteTateProSheaf l F n X 1) ≅
        finiteTateProSheaf l F n (AffineSpace (ULift.{u} (Fin 1)) (Spec (.of Ω))) 1)
    (q : (ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} (finiteTateCoefficient l F n))
        (AffineSpace (ULift.{u} (Fin 1)) (Spec (.of Ω)))).obj
          (finiteEtaleTateLine (AffineSpace (ULift.{u} (Fin 1)) (Spec (.of Ω)))
            (l ^ (n + 1)) (finiteTateCoefficient l F n) hA) ≅
              finiteTateProSheaf l F n (AffineSpace (ULift.{u} (Fin 1)) (Spec (.of Ω))) 1) :
    Prop :=
  (ProEtale.upperStar
    (ModuleCat.{u + 1} (finiteTateCoefficient l F n)) b).mapDerivedCategoryPlus.map
      (proTau l F n c z hz hI hX) ≫
    SectionCompactSource.proExchange (finiteTateCoefficient l F n) sq c
      ((proLine l F n X)⟦(2 : ℤ)⟧) ≫
    (ProEtale.rightDerivedLowerShriekOfCompactificationPlus
      (ModuleCat.{u + 1} (finiteTateCoefficient l F n)) (c.ofIsPullback sq)).map
        (twistPull l F n v p).hom ≫
    (compactTarget l F n hA (c.ofIsPullback sq) q).hom =
    (SectionCompactSource.proConstantPull (finiteTateCoefficient l F n) b).hom ≫
      (SectionCompactSource.compareConstant (finiteTateCoefficient l F n) (Spec (.of Ω))).inv ≫
      (ProEtale.comparisonUpperStar
        (ModuleCat.{u + 1} (finiteTateCoefficient l F n))
          (Spec (.of Ω))).mapDerivedCategoryPlus.map
        (etaleTau l F n hA (c.ofIsPullback sq)
          (AffineSpace.zeroSection (ULift.{u} (Fin 1)) (Spec (.of Ω)))
          (AffineSpace.zeroSection_over (ULift.{u} (Fin 1)) (Spec (.of Ω))) hIΩ hXΩ)

end AlgebraicGeometry.LineZeroClass

namespace AlgebraicGeometry.LineZeroClass
open Scheme LineKummerField

private def exchangeNat (A : Type (u + 1)) [CommRing A] [Finite A]
    {X' X B' B : Scheme.{u}} {v : X' ⟶ X} {π' : X' ⟶ B'}
    {π : X ⟶ B} {g : B' ⟶ B} (sq : IsPullback v π' π g)
    (c : Compactification π) :
    ProEtale.rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} A) c ⋙
        (ProEtale.upperStar (ModuleCat.{u + 1} A) g).mapDerivedCategoryPlus ⟶
      (ProEtale.upperStar (ModuleCat.{u + 1} A) v).mapDerivedCategoryPlus ⋙
        ProEtale.rightDerivedLowerShriekOfCompactificationPlus
          (ModuleCat.{u + 1} A) (c.ofIsPullback sq) :=
  { app := SectionCompactSource.proExchange A sq c
    naturality := by
      intro M N f
      apply DerivedCategory.Plus.ι.map_injective
      simp only [Functor.map_comp, SectionCompactSource.proExchange, Functor.map_preimage]
      let R := ProEtale.rightDerivedLowerShriekOfCompactificationPlus
        (ModuleCat.{u + 1} A) c
      let R' := ProEtale.rightDerivedLowerShriekOfCompactification
        (ModuleCat.{u + 1} A) (c.ofIsPullback sq)
      let η := Functor.whiskerLeft R
          (ProEtale.upperStar (ModuleCat.{u + 1} A) g).mapDerivedCategoryPlusCompatibility.hom ≫
        Functor.whiskerRight
          (ProEtale.rightDerivedLowerShriekOfCompactificationPlusCompatibility
            (ModuleCat.{u + 1} A) c).hom _ ≫
        Functor.whiskerLeft (DerivedCategory.Plus.ι ⋙
          ProEtale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c)
          (ProEtale.leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) g).inv ≫
        Functor.whiskerLeft DerivedCategory.Plus.ι
          (ProEtale.rightDerivedLowerShriekOfCompactificationBaseChangeMap
            (ModuleCat.{u + 1} A) sq c) ≫
        Functor.whiskerRight (Functor.whiskerLeft DerivedCategory.Plus.ι
          (ProEtale.leftDerivedUpperStarIsoMapDerivedCategory
            (ModuleCat.{u + 1} A) v).hom ≫
          (ProEtale.upperStar (ModuleCat.{u + 1} A) v).mapDerivedCategoryPlusCompatibility.inv)
          R' ≫
        Functor.whiskerLeft
          (ProEtale.upperStar (ModuleCat.{u + 1} A) v).mapDerivedCategoryPlus
          (ProEtale.rightDerivedLowerShriekOfCompactificationPlusCompatibility
            (ModuleCat.{u + 1} A) (c.ofIsPullback sq)).inv
      convert η.naturality f using 1 <;>
        simp only [η, R, R', Functor.map_comp, NatTrans.comp_app, Functor.whiskerLeft_app,
        Functor.whiskerRight_app, Functor.comp_map, Functor.comp_obj, ObjectProperty.ι_obj,
          Category.assoc]
      }

private theorem exchange_isIso (A : Type (u + 1)) [CommRing A] [Finite A]
    {X' X B' B : Scheme.{u}} {v : X' ⟶ X} {π' : X' ⟶ B'}
    {π : X ⟶ B} {g : B' ⟶ B} (sq : IsPullback v π' π g)
    (c : Compactification π)
    (M : DerivedCategory.Plus (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)))
    (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (e : (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategoryPlus.obj
      L ≅ M) : IsIso (SectionCompactSource.proExchange A sq c M) := by
  have he : ProEtale.DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) X M.obj :=
    ⟨L.obj, L.property, ⟨(Functor.mapDerivedCategoryPlusCompatibility
      (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) X)).symm.app L ≪≫
        DerivedCategory.Plus.ι.mapIso e⟩⟩
  have := ProEtale.isIso_rightDerivedLowerShriekOfCompactificationBaseChangeMap_app A sq c
    M.obj he
  rw [← isIso_iff_of_reflects_iso _ DerivedCategory.Plus.ι]
  simp only [SectionCompactSource.proExchange, Functor.map_preimage]
  infer_instance

private theorem compact_realization (l : ℕ) [Fact l.Prime] (F : Type u) [Field F]
    [Algebra (Padic l) F] [FiniteDimensional (Padic l) F] (n : ℕ)
    (hA : ((l ^ (n + 1) : ℕ) : finiteTateCoefficient l F n) = 0)
    {B X : Scheme.{u}} {π : X ⟶ B} (c : Compactification π)
    (z : B ⟶ X) [IsClosedImmersion z] (hz : z ≫ π = 𝟙 B)
    (hI : z.ker.IsInvertible) (hX : IsUnit (l : Γ(X, ⊤)))
    (q : (ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} (finiteTateCoefficient l F n)) X).obj
        (finiteEtaleTateLine X (l ^ (n + 1)) (finiteTateCoefficient l F n) hA) ≅
          finiteTateProSheaf l F n X 1)
    (hpair : PairRealization l F n hA z hI hX q) :
    proTau l F n c z hz hI hX ≫ (compactTarget l F n hA c q).hom =
      (SectionCompactSource.compareConstant (finiteTateCoefficient l F n) B).inv ≫
        (ProEtale.comparisonUpperStar
          (ModuleCat.{u + 1} (finiteTateCoefficient l F n)) B).mapDerivedCategoryPlus.map
            (etaleTau l F n hA c z hz hI hX) := by
  unfold PairRealization at hpair
  have hp := hpair.2.2
  unfold proTau compactTarget etaleTau SectionCompactSource.proSource
    SectionCompactSource.sourceComparison
  simp only [Iso.trans_hom, Iso.app_hom, Iso.symm_hom, Functor.mapIso_hom,
    Functor.map_comp, Category.assoc]
  rw [← Functor.map_comp_assoc, ← hp, Functor.map_comp]
  simp only [Category.assoc, ← Functor.map_comp_assoc, Iso.hom_inv_id, Category.comp_id]
  have hn := (ProEtale.compactSupportSiteComparisonPlus
    (finiteTateCoefficient l F n) c).hom.naturality (etaleClass l F n hA z hI hX)
  dsimp only [Functor.comp_map] at hn
  erw [← reassoc_of% hn]
  simp

private theorem supported_pullback
    (l : ℕ) [Fact l.Prime] (F : Type u) [Field F]
    [Algebra (Padic l) F] [FiniteDimensional (Padic l) F] (n : ℕ)
    {B X B' X' : Scheme.{u}} {g : B' ⟶ B} {v : X' ⟶ X}
    (z : B ⟶ X) (z' : B' ⟶ X') [IsClosedImmersion z] [IsClosedImmersion z']
    (sqZ : ChosenCartesianSquare g z' z v)
    (hI : z.ker.IsInvertible) (hI' : z'.ker.IsInvertible)
    (hX : IsUnit (l : Γ(X, ⊤)))
    (hX' : IsUnit (l : Γ(X', ⊤)))
    (hnorm : ∀ d : (ProEtale.upperStar
        (ModuleCat.{u + 1} (finiteTateCoefficient l F n)) v).obj
          (SupportedConstantNormalization.supported (finiteTateCoefficient l F n) true z) ⟶
            SupportedConstantNormalization.supported (finiteTateCoefficient l F n) true z',
      (ProEtale.upperStar (ModuleCat.{u + 1} (finiteTateCoefficient l F n)) v).map
        (SupportedConstantNormalization.restriction (finiteTateCoefficient l F n) true z) ≫ d =
        (SupportedConstantNormalization.unitIso (finiteTateCoefficient l F n) true v).hom ≫
          SupportedConstantNormalization.restriction (finiteTateCoefficient l F n) true z' →
      d = SupportedConstantNormalization.exchange (finiteTateCoefficient l F n) true sqZ) :
    ∃ p : (ProEtale.upperStar
      (ModuleCat.{u + 1} (finiteTateCoefficient l F n)) v).obj
        (finiteTateProSheaf l F n X 1) ≅
          finiteTateProSheaf l F n X' 1,
      IsFiniteTateProPullback l F n X v 1 p ∧
      (ProEtale.upperStar
        (ModuleCat.{u + 1} (finiteTateCoefficient l F n))
          v).mapDerivedCategoryPlus.map (proClass l F n z hI hX) ≫
        (twistPull l F n v p).hom =
      SectionCompactSource.proBeta (finiteTateCoefficient l F n) sqZ ≫
        proClass l F n z' hI' hX' := by
  obtain ⟨p, hp, h⟩ :=
    SupportedCartierDerivedPullback.supported_cartier_derived_pullback
      l F n z z' sqZ hI hI' hX hX' hnorm
  refine ⟨p, hp, ?_⟩
  simpa only [twistPull, proLine] using h


private theorem compact_arrow_exchange
    {C : Type*} {D : Type*} {E : Type*} {F : Type*}
    [Category C] [Category D] [Category E] [Category F]
    (G : C ⥤ D) (H : E ⥤ F) (R : E ⥤ C) (R' : F ⥤ D)
    {S : C} {S' : D} {M N : E} {M' N' : F}
    (a : S ⟶ R.obj M) (a' : S' ⟶ R'.obj M') (b : G.obj S ⟶ S')
    (β : H.obj M ⟶ M') (f : M ⟶ N) (f' : M' ⟶ N') (t : H.obj N ⟶ N')
    (eM : G.obj (R.obj M) ⟶ R'.obj (H.obj M))
    (eN : G.obj (R.obj N) ⟶ R'.obj (H.obj N))
    (hn : G.map (R.map f) ≫ eN = eM ≫ R'.map (H.map f))
    (hs : G.map a ≫ eM ≫ R'.map β = b ≫ a')
    (hc : H.map f ≫ t = β ≫ f') :
    G.map (a ≫ R.map f) ≫ eN ≫ R'.map t = b ≫ (a' ≫ R'.map f') := by
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% hn, ← R'.map_comp, hc, Functor.map_comp]
  simpa only [Category.assoc] using congrArg (fun k ↦ k ≫ R'.map f') hs

private theorem exchange_class (l : ℕ) [Fact l.Prime] (F : Type u) [Field F]
    [Algebra (Padic l) F] [FiniteDimensional (Padic l) F] (n : ℕ)
    {B X B' X' : Scheme.{u}} {π : X ⟶ B} {π' : X' ⟶ B'}
    {g : B' ⟶ B} {v : X' ⟶ X} (sq : IsPullback v π' π g) (c : Compactification π)
    (z : B ⟶ X) (z' : B' ⟶ X') [IsClosedImmersion z] [IsClosedImmersion z']
    (hz : z ≫ π = 𝟙 B) (hz' : z' ≫ π' = 𝟙 B')
    (sqZ : ChosenCartesianSquare g z' z v)
    (hI : z.ker.IsInvertible) (hI' : z'.ker.IsInvertible)
    (hX : IsUnit (l : Γ(X, ⊤))) (hX' : IsUnit (l : Γ(X', ⊤)))
    (p : (ProEtale.upperStar (ModuleCat.{u + 1} (finiteTateCoefficient l F n)) v).obj
      (finiteTateProSheaf l F n X 1) ≅ finiteTateProSheaf l F n X' 1)
    (hs : (ProEtale.upperStar
        (ModuleCat.{u + 1} (finiteTateCoefficient l F n)) g).mapDerivedCategoryPlus.map
        (SectionCompactSource.proSource (finiteTateCoefficient l F n) c z hz) ≫
      SectionCompactSource.proExchange (finiteTateCoefficient l F n) sq c
        (SectionCompactSource.proSupported (finiteTateCoefficient l F n) z) ≫
      (ProEtale.rightDerivedLowerShriekOfCompactificationPlus
        (ModuleCat.{u + 1} (finiteTateCoefficient l F n)) (c.ofIsPullback sq)).map
          (SectionCompactSource.proBeta (finiteTateCoefficient l F n) sqZ) =
      (SectionCompactSource.proConstantPull (finiteTateCoefficient l F n) g).hom ≫
        SectionCompactSource.proSource (finiteTateCoefficient l F n)
          (c.ofIsPullback sq) z' hz')
    (hc : (ProEtale.upperStar
        (ModuleCat.{u + 1} (finiteTateCoefficient l F n)) v).mapDerivedCategoryPlus.map
        (proClass l F n z hI hX) ≫ (twistPull l F n v p).hom =
      SectionCompactSource.proBeta (finiteTateCoefficient l F n) sqZ ≫
        proClass l F n z' hI' hX') :
    (ProEtale.upperStar
        (ModuleCat.{u + 1} (finiteTateCoefficient l F n)) g).mapDerivedCategoryPlus.map
        (proTau l F n c z hz hI hX) ≫
      SectionCompactSource.proExchange (finiteTateCoefficient l F n) sq c
        ((proLine l F n X)⟦(2 : ℤ)⟧) ≫
      (ProEtale.rightDerivedLowerShriekOfCompactificationPlus
        (ModuleCat.{u + 1} (finiteTateCoefficient l F n)) (c.ofIsPullback sq)).map
          (twistPull l F n v p).hom =
      (SectionCompactSource.proConstantPull (finiteTateCoefficient l F n) g).hom ≫
        proTau l F n (c.ofIsPullback sq) z' hz' hI' hX' := by
  have hn := (exchangeNat (finiteTateCoefficient l F n) sq c).naturality
    (proClass l F n z hI hX)
  change (ProEtale.upperStar (ModuleCat.{u + 1} (finiteTateCoefficient l F n))
      g).mapDerivedCategoryPlus.map
      ((ProEtale.rightDerivedLowerShriekOfCompactificationPlus
        (ModuleCat.{u + 1} (finiteTateCoefficient l F n)) c).map
          (proClass l F n z hI hX)) ≫ _ =
    _ ≫ (ProEtale.rightDerivedLowerShriekOfCompactificationPlus
      (ModuleCat.{u + 1} (finiteTateCoefficient l F n)) (c.ofIsPullback sq)).map
        ((ProEtale.upperStar (ModuleCat.{u + 1} (finiteTateCoefficient l F n))
          v).mapDerivedCategoryPlus.map (proClass l F n z hI hX)) at hn
  unfold proTau
  exact compact_arrow_exchange
    (ProEtale.upperStar (ModuleCat.{u + 1} (finiteTateCoefficient l F n))
      g).mapDerivedCategoryPlus
    (ProEtale.upperStar (ModuleCat.{u + 1} (finiteTateCoefficient l F n))
      v).mapDerivedCategoryPlus
    (ProEtale.rightDerivedLowerShriekOfCompactificationPlus
      (ModuleCat.{u + 1} (finiteTateCoefficient l F n)) c)
    (ProEtale.rightDerivedLowerShriekOfCompactificationPlus
      (ModuleCat.{u + 1} (finiteTateCoefficient l F n)) (c.ofIsPullback sq))
    _ _ _ _ _ _ _ _ _ hn hs hc

private theorem section_exchange
    (l : ℕ) [Fact l.Prime] (F : Type u) [Field F]
    [Algebra (Padic l) F] [FiniteDimensional (Padic l) F] (n : ℕ)
    (K : Type u) [Field K] (hl : IsUnit (l : K))
    {B X : Scheme.{u}} [B.Over (Spec (.of K))] [X.Over (Spec (.of K))]
    [IsSeparated (B ↘ Spec (.of K))] [LocallyOfFiniteType (B ↘ Spec (.of K))]
    [QuasiCompact (B ↘ Spec (.of K))]
    [IsSeparated (X ↘ Spec (.of K))] [LocallyOfFiniteType (X ↘ Spec (.of K))]
    [QuasiCompact (X ↘ Spec (.of K))]
    (π : X ⟶ B) [π.IsOver (Spec (.of K))]
    [IsSeparated π] [LocallyOfFiniteType π] [QuasiCompact π]
    (z : B ⟶ X) [IsClosedImmersion z] (hz : z ≫ π = 𝟙 B)
    {B' X' : Scheme.{u}} [B'.Over (Spec (.of K))] [X'.Over (Spec (.of K))]
    (g : B' ⟶ B) [g.IsOver (Spec (.of K))]
    (v : X' ⟶ X) (π' : X' ⟶ B') (sq : IsPullback v π' π g)
    (z' : B' ⟶ X') [IsClosedImmersion z'] (hz' : z' ≫ π' = 𝟙 B')
    (sqZ : ChosenCartesianSquare g z' z v) (c : Compactification π) :
      IsIso (SectionCompactSource.proSource
        (finiteTateCoefficient l F n) c z
          hz) ∧
      (ProEtale.upperStar
        (ModuleCat.{u + 1} (finiteTateCoefficient l F n))
          g).mapDerivedCategoryPlus.map
        (SectionCompactSource.proSource
          (finiteTateCoefficient l F n) c z
            hz) ≫
      SectionCompactSource.proExchange (finiteTateCoefficient l F n)
        sq c (SectionCompactSource.proSupported
          (finiteTateCoefficient l F n) z) ≫
      (ProEtale.rightDerivedLowerShriekOfCompactificationPlus
        (ModuleCat.{u + 1} (finiteTateCoefficient l F n))
          (c.ofIsPullback sq)).map
        (SectionCompactSource.proBeta (finiteTateCoefficient l F n)
          sqZ) =
      (SectionCompactSource.proConstantPull
        (finiteTateCoefficient l F n) g).hom ≫
      SectionCompactSource.proSource (finiteTateCoefficient l F n)
        (c.ofIsPullback sq) z' hz' := by
  let : Fact (1 ≤ n + 1) := ⟨Nat.le_add_left 1 n⟩
  have hh := SectionCompactSource.section_compact_source_exchange
    l F (n + 1) K hl π c z hz g v π' sq z' hz' sqZ
  exact ⟨hh.1, hh.2.2.2.2.2⟩

set_option linter.unusedVariables false in
set_option maxHeartbeats 600000 in
-- The assembly elaborates several quantified coefficient and derived functor interfaces.
/-- Compact pushforward of the zero-section Kummer arrow commutes with every base
change, with identity-normalized source. Its geometric-stalk arrow is the ordinary
etale compact origin arrow, realized by the projection-normalized twist comparison.
Source: blueprint latest, rank-one Thom proof, Step 3 and Step 2, first paragraph
(blueprint: lem-pur-line-zero-class-exchange).

Proof: Apply field realization to the canonical total space and transport its
Cartier-pair data through the chosen total-space isomorphism. Cartier Kummer base
change, normalized by the supported constant restriction, gives the supported
class equation in D+. Naturality of the specified compactification exchange and
the normalized section-source equation give Exchange. Invertibility follows
from finite-level base change on the shifted etale-origin witness. On every
specified affine-line fibre, compose Exchange with the pair-realization equation
and naturality of compact-support site comparison to obtain FibreFormula. -/
theorem line_zero_class_exchange
    (P : WeilConjectures.PurityFiniteSetting.{u}) (n : ℕ) (_hn : P.level = n + 1)
    {B : Scheme.{u}} (hB : B ⟶ Spec (.of P.field.k))
    [IsSeparated hB] [LocallyOfFiniteType hB] [QuasiCompact hB]
    (V : PurityVectorBundle P B hB 1) :
    ∃ (hA : ((P.coefficients.l ^ (n + 1) : ℕ) :
        finiteTateCoefficient P.coefficients.l P.extension n) = 0)
      (hI : V.zeroSection.ker.IsInvertible)
      (hX : IsUnit (P.coefficients.l : Γ(V.E, ⊤))),
      ∀ c : Compactification V.p,
        IsIso (SectionCompactSource.proSource
          (finiteTateCoefficient P.coefficients.l P.extension n) c V.zeroSection
            V.zeroSection_spec.1) ∧
        (∀ {B' X' : Scheme.{u}} (g : B' ⟶ B) (v : X' ⟶ V.E) (π' : X' ⟶ B')
          (sq : IsPullback v π' V.p g) (z' : B' ⟶ X') [IsClosedImmersion z']
          (hz' : z' ≫ π' = 𝟙 B') (sqZ : ChosenCartesianSquare g z' V.zeroSection v),
          ∃ (hI' : z'.ker.IsInvertible) (hX' : IsUnit (P.coefficients.l : Γ(X', ⊤)))
            (p : (ProEtale.upperStar
              (ModuleCat.{u + 1} (finiteTateCoefficient P.coefficients.l P.extension n))
                v).obj (finiteTateProSheaf P.coefficients.l P.extension n V.E 1) ≅
                  finiteTateProSheaf P.coefficients.l P.extension n X' 1),
            IsFiniteTateProPullback P.coefficients.l P.extension n V.E v 1 p ∧
            Exchange P.coefficients.l P.extension n c V.zeroSection
              V.zeroSection_spec.1 hI hX g v π' sq z' hz' sqZ hI' hX' p) ∧
        (∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (b : Spec (.of Ω) ⟶ B)
          (v : AffineSpace (ULift.{u} (Fin 1)) (Spec (.of Ω)) ⟶ V.E)
          (sq : IsPullback v
            (AffineSpace (ULift.{u} (Fin 1)) (Spec (.of Ω)) ↘ Spec (.of Ω)) V.p b)
          (sqZ : ChosenCartesianSquare b
            (AffineSpace.zeroSection (ULift.{u} (Fin 1)) (Spec (.of Ω))) V.zeroSection v),
          ∃ (hIΩ : (AffineSpace.zeroSection
              (ULift.{u} (Fin 1)) (Spec (.of Ω))).ker.IsInvertible)
            (hXΩ : IsUnit (P.coefficients.l :
              Γ(AffineSpace (ULift.{u} (Fin 1)) (Spec (.of Ω)), ⊤)))
            (p : (ProEtale.upperStar
              (ModuleCat.{u + 1} (finiteTateCoefficient P.coefficients.l P.extension n))
                v).obj (finiteTateProSheaf P.coefficients.l P.extension n V.E 1) ≅
                  finiteTateProSheaf P.coefficients.l P.extension n
                    (AffineSpace (ULift.{u} (Fin 1)) (Spec (.of Ω))) 1)
            (q : (ProEtale.comparisonUpperStar
              (ModuleCat.{u + 1} (finiteTateCoefficient P.coefficients.l P.extension n))
                (AffineSpace (ULift.{u} (Fin 1)) (Spec (.of Ω)))).obj
                  (finiteEtaleTateLine (AffineSpace (ULift.{u} (Fin 1)) (Spec (.of Ω)))
                    (P.coefficients.l ^ (n + 1))
                    (finiteTateCoefficient P.coefficients.l P.extension n) hA) ≅
                      finiteTateProSheaf P.coefficients.l P.extension n
                        (AffineSpace (ULift.{u} (Fin 1)) (Spec (.of Ω))) 1),
            IsFiniteTateProPullback P.coefficients.l P.extension n V.E v 1 p ∧
            IsFiniteTateSiteComparison P.coefficients.l P.extension n
              (AffineSpace (ULift.{u} (Fin 1)) (Spec (.of Ω))) n hA 1 q ∧
            FibreFormula P.coefficients.l P.extension n hA c V.zeroSection
              V.zeroSection_spec.1 hI hX Ω b v sq hIΩ hXΩ p q) := by
  classical
  let : B.Over (Spec (.of P.field.k)) := ⟨hB⟩
  let : LocallyOfFiniteType (B ↘ Spec (.of P.field.k)) := ‹LocallyOfFiniteType hB›
  let : IsSeparated (B ↘ Spec (.of P.field.k)) := ‹IsSeparated hB›
  let : QuasiCompact (B ↘ Spec (.of P.field.k)) := ‹QuasiCompact hB›
  let : IsNoetherian B := isNoetherian_of_locallyOfFiniteType hB
  let := V.locallyFree
  have hl : IsUnit (P.coefficients.l : P.field.k) := by
    let : Fintype P.field.k₀ := Fintype.ofFinite _
    let : Fact P.field.p.Prime := ⟨P.field.prime⟩
    let : CharP P.field.k₀ P.field.p := charP_of_card_eq_prime_pow (by
      rw [← Nat.card_eq_fintype_card, P.field.card_base, P.field.cardinality_eq])
    let : CharP P.field.k P.field.p :=
      charP_of_injective_algebraMap' P.field.k₀ P.field.p
    exact isUnit_iff_ne_zero.mpr (CharP.cast_ne_zero_of_ne_of_prime _
      (Fact.out : P.coefficients.l.Prime) P.coefficients.different.symm)
  obtain ⟨hA, _, hb⟩ := line_kummer_field_realization P.coefficients.l P.extension n
    P.field.k hl
  obtain ⟨hNB, hr⟩ := hb B
  have hr := hr V.𝓔
  unfold BundleRealization at hr
  obtain ⟨hsep, hlft, hqc, _, hI₀, hX₀, q₀, _, _, _, _, hpull, _⟩ := hr
  let π₀ := VectorBundleZeroSection.π B 1 V.𝓔
  let z₀ := VectorBundleZeroSection.zero B 1 V.𝓔
  have hπ : V.phi.hom ≫ π₀ = V.p := V.over_commutes
  have hz₀ : V.zeroSection ≫ V.phi.hom = z₀ := by
    simp [PurityVectorBundle.zeroSection, z₀]
  have sq₀ : IsPullback V.phi.hom V.p π₀ (𝟙 B) :=
    IsPullback.of_horiz_isIso ⟨by simpa using hπ⟩
  have sz₀ : IsPullback (𝟙 B) V.zeroSection z₀ V.phi.hom :=
    IsPullback.of_horiz_isIso ⟨by simpa using hz₀.symm⟩
  let cz₀ : ChosenCartesianSquare (𝟙 B) V.zeroSection z₀ V.phi.hom :=
    ⟨sz₀.toCommSq, sz₀.isoPullback, sz₀.isoPullback_hom_fst, sz₀.isoPullback_hom_snd⟩
  obtain ⟨hI, hX, q, hq, _, hpair, _⟩ := hpull (𝟙 B) V.phi.hom V.p sq₀
    V.zeroSection cz₀
  let := hsep
  let := hlft
  let := hqc
  have hsep' : IsSeparated V.p := by rw [← hπ]; infer_instance
  have hlft' : LocallyOfFiniteType V.p := by rw [← hπ]; infer_instance
  have hqc' : QuasiCompact V.p := by rw [← hπ]; infer_instance
  let := hsep'
  let := hlft'
  let := hqc'
  let : V.E.Over (Spec (.of P.field.k)) := ⟨V.p ≫ hB⟩
  let : LocallyOfFiniteType (V.E ↘ Spec (.of P.field.k)) :=
    locallyOfFiniteType_comp V.p hB
  let : QuasiCompact (V.E ↘ Spec (.of P.field.k)) := quasiCompact_comp V.p hB
  let : IsSeparated (V.E ↘ Spec (.of P.field.k)) :=
    MorphismProperty.comp_mem (@IsSeparated) V.p hB hsep' ‹IsSeparated hB›
  have allpairs {B' X' : Scheme.{u}} (g : B' ⟶ B) (v : X' ⟶ V.E) (π' : X' ⟶ B')
      (sq : IsPullback v π' V.p g) (z' : B' ⟶ X') [IsClosedImmersion z']
      (sqZ : ChosenCartesianSquare g z' V.zeroSection v) :
      ∃ (hI' : z'.ker.IsInvertible) (hX' : IsUnit (P.coefficients.l : Γ(X', ⊤)))
        (q' : (ProEtale.comparisonUpperStar
          (ModuleCat.{u + 1} (finiteTateCoefficient P.coefficients.l P.extension n)) X').obj
            (finiteEtaleTateLine X' (P.coefficients.l ^ (n + 1))
              (finiteTateCoefficient P.coefficients.l P.extension n) hA) ≅
                finiteTateProSheaf P.coefficients.l P.extension n X' 1),
        IsFiniteTateSiteComparison P.coefficients.l P.extension n X' n hA 1 q' ∧
        PairRealization P.coefficients.l P.extension n hA z' hI' hX' q' := by
    have sp := sq.paste_horiz sq₀
    have spZ := (IsPullback.of_iso_pullback sqZ.toCommSq sqZ.isoPullback
      sqZ.hom_fst sqZ.hom_snd).paste_horiz sz₀
    have sp' : IsPullback (v ≫ V.phi.hom) π' π₀ g := by simpa using sp
    have spZ' : IsPullback g z' z₀ (v ≫ V.phi.hom) := by simpa using spZ
    let cpZ : ChosenCartesianSquare g z' z₀ (v ≫ V.phi.hom) :=
      ⟨spZ'.toCommSq, spZ'.isoPullback, spZ'.isoPullback_hom_fst,
        spZ'.isoPullback_hom_snd⟩
    obtain ⟨hi, hx, qq, hqq, _, hpp, _⟩ := hpull g (v ≫ V.phi.hom) π' sp' z' cpZ
    exact ⟨hi, hx, qq, hqq, hpp⟩
  have sections {B' X' : Scheme.{u}} (g : B' ⟶ B) (v : X' ⟶ V.E) (π' : X' ⟶ B')
      (sq : IsPullback v π' V.p g) (z' : B' ⟶ X') [IsClosedImmersion z']
      (hz' : z' ≫ π' = 𝟙 B') (sqZ : ChosenCartesianSquare g z' V.zeroSection v)
      (c : Compactification V.p) :
      IsIso (SectionCompactSource.proSource
        (finiteTateCoefficient P.coefficients.l P.extension n) c V.zeroSection
          V.zeroSection_spec.1) ∧
      (ProEtale.upperStar
        (ModuleCat.{u + 1} (finiteTateCoefficient P.coefficients.l P.extension n))
          g).mapDerivedCategoryPlus.map
        (SectionCompactSource.proSource
          (finiteTateCoefficient P.coefficients.l P.extension n) c V.zeroSection
            V.zeroSection_spec.1) ≫
      SectionCompactSource.proExchange (finiteTateCoefficient P.coefficients.l P.extension n)
        sq c (SectionCompactSource.proSupported
          (finiteTateCoefficient P.coefficients.l P.extension n) V.zeroSection) ≫
      (ProEtale.rightDerivedLowerShriekOfCompactificationPlus
        (ModuleCat.{u + 1} (finiteTateCoefficient P.coefficients.l P.extension n))
          (c.ofIsPullback sq)).map
        (SectionCompactSource.proBeta (finiteTateCoefficient P.coefficients.l P.extension n)
          sqZ) =
      (SectionCompactSource.proConstantPull
        (finiteTateCoefficient P.coefficients.l P.extension n) g).hom ≫
      SectionCompactSource.proSource (finiteTateCoefficient P.coefficients.l P.extension n)
        (c.ofIsPullback sq) z' hz' := by
    let : Fact (1 ≤ n + 1) := ⟨Nat.le_add_left 1 n⟩
    let : B'.Over (Spec (.of P.field.k)) := ⟨g ≫ hB⟩
    let : X'.Over (Spec (.of P.field.k)) := ⟨π' ≫ g ≫ hB⟩
    let : V.p.IsOver (Spec (.of P.field.k)) := ⟨rfl⟩
    let : g.IsOver (Spec (.of P.field.k)) := ⟨rfl⟩
    have hsec := section_exchange P.coefficients.l P.extension n P.field.k hl
      (B := B) (X := V.E) (B' := B') (X' := X') V.p
      V.zeroSection V.zeroSection_spec.1 g v π' sq z' hz' sqZ c
    exact hsec
  have basechange (c : Compactification V.p)
      {B' X' : Scheme.{u}} (g : B' ⟶ B) (v : X' ⟶ V.E) (π' : X' ⟶ B')
      (sq : IsPullback v π' V.p g) (z' : B' ⟶ X') [IsClosedImmersion z']
      (hz' : z' ≫ π' = 𝟙 B') (sqZ : ChosenCartesianSquare g z' V.zeroSection v) :
      ∃ (hI' : z'.ker.IsInvertible) (hX' : IsUnit (P.coefficients.l : Γ(X', ⊤)))
        (p : (ProEtale.upperStar
          (ModuleCat.{u + 1} (finiteTateCoefficient P.coefficients.l P.extension n)) v).obj
            (finiteTateProSheaf P.coefficients.l P.extension n V.E 1) ≅
              finiteTateProSheaf P.coefficients.l P.extension n X' 1),
        IsFiniteTateProPullback P.coefficients.l P.extension n V.E v 1 p ∧
        Exchange P.coefficients.l P.extension n c V.zeroSection V.zeroSection_spec.1
          hI hX g v π' sq z' hz' sqZ hI' hX' p := by
    obtain ⟨hI', hX', q', hq', hp'⟩ := allpairs g v π' sq z' sqZ
    obtain ⟨p, hp, hc⟩ := supported_pullback
      P.coefficients.l P.extension n V.zeroSection z' sqZ hI hI' hX hX'
      (SupportedConstantNormalization.scheme_normalization
        { P with level := n + 1, level_pos := Nat.le_add_left 1 n } true sqZ).2.2.2.2.2
    have hs := sections g v π' sq z' hz' sqZ c
    have hi := exchange_isIso (finiteTateCoefficient P.coefficients.l P.extension n) sq c
      ((proLine P.coefficients.l P.extension n V.E)⟦(2 : ℤ)⟧)
      ((etaleLine P.coefficients.l P.extension n hA V.E)⟦(2 : ℤ)⟧)
      (shiftedComparison P.coefficients.l P.extension n hA V.E q)
    have he : Exchange P.coefficients.l P.extension n c V.zeroSection
        V.zeroSection_spec.1 hI hX g v π' sq z' hz' sqZ hI' hX' p := by
      unfold Exchange
      exact ⟨hs.2, hi, exchange_class P.coefficients.l P.extension n sq c
        V.zeroSection z' V.zeroSection_spec.1 hz' sqZ hI hI' hX hX' p hs.2 hc⟩
    exact ⟨hI', hX', p, hp, he⟩
  refine ⟨hA, hI, hX, ?_⟩
  intro c
  refine ⟨?_, basechange c, ?_⟩
  · have si : IsPullback (𝟙 V.E) V.p V.p (𝟙 B) := IsPullback.of_id_fst
    have sz : IsPullback (𝟙 B) V.zeroSection V.zeroSection (𝟙 V.E) :=
      IsPullback.of_id_fst
    let cz : ChosenCartesianSquare (𝟙 B) V.zeroSection V.zeroSection (𝟙 V.E) :=
      ⟨sz.toCommSq, sz.isoPullback, sz.isoPullback_hom_fst, sz.isoPullback_hom_snd⟩
    exact (sections (𝟙 B) (𝟙 V.E) V.p si V.zeroSection V.zeroSection_spec.1 cz c).1
  · intro Ω _ _ b v sq sqZ
    obtain ⟨hIΩ, hXΩ, qΩ, hqΩ, hpΩ⟩ := allpairs b v _ sq _ sqZ
    obtain ⟨hIΩ', hXΩ', p, hp, he⟩ := basechange c b v _ sq _
      (AffineSpace.zeroSection_over _ _) sqZ
    refine ⟨hIΩ, hXΩ, p, qΩ, hp, hqΩ, ?_⟩
    unfold FibreFormula
    unfold Exchange at he
    have hc := compact_realization P.coefficients.l P.extension n hA
      (c.ofIsPullback sq) _ (AffineSpace.zeroSection_over _ _)
      hIΩ hXΩ qΩ hpΩ
    simpa only [Category.assoc] using (congrArg (fun f ↦ f ≫
      (compactTarget P.coefficients.l P.extension n hA (c.ofIsPullback sq) qΩ).hom)
      he.2.2).trans (by
        simpa only [Category.assoc] using congrArg
          (fun f ↦ (SectionCompactSource.proConstantPull
            (finiteTateCoefficient P.coefficients.l P.extension n) b).hom ≫ f) hc)

end AlgebraicGeometry.LineZeroClass
