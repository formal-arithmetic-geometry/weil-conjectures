/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NI
-/
module

public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.Compactification.RefinementCategory
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import Sheaf.AlgebraicGeometry.ProEtaleFiniteModules
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekPlusBaseChange
public import Sheaf.AlgebraicGeometry.SfIntrinsicCompactSupport
public import Sheaf.AlgebraicGeometry.ProperOpenInterchangeCoherence
public import Sheaf.Paper.EtaleDerivedDirectImageCoherence
public import Sheaf.Paper.CanonicalOriginCompactSupportComposition
public import Sheaf.AlgebraicGeometry.CanonicalCompactSupportSiteComparison
public import Sheaf.Paper.CanonicalFiniteLevelCompactSupportBaseChange
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekBaseChange
public import Sheaf.AlgebraicGeometry.SupportedConstantExchangeNormalization
public import WeilConjectures.SixFunctors.Etale.Derived.ProperOpenComparison.Defs
public import WeilConjectures.SixFunctors.Finite.Exact
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.ClosedImmersion
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusExact
public import Sheaf.Paper.FiniteCompactSiteCoherence

public import Sheaf.Paper.SectionCompactSourceMaps
import Sheaf.Paper.SectionSourceEtaleExchange
import Sheaf.Paper.SectionSourceProExchange
import Sheaf.Paper.SectionSupportedComparisonIso
import Sheaf.Paper.SectionSupportedProExchangeIso

/-! # Identity-normalized compact image of a closed section

Source: blueprint main-20261015, sec-smooth-purity/sk-prop-an,
thm-pur-rank-one-thom.proof.md, Step 3; Stacks Tags 0F7B, 0F7F and 0D6E
(blueprint: lem-pur-section-compact-source-exchange).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.SectionCompactSource

variable (A : Type (u + 1)) [CommRing A]

/-- On a Noetherian base the transported source is the inverse of the actual
compact-support compositor at the proper closed section and hs = id.
Source: blueprint rank-one Thom proof, Step 3; Stacks Tags 0F7J and 0D6E
(blueprint: lem-pur-section-compact-source-exchange).
Proof: the compact-support site coherence equation identifies the pro-etale
proper/open composition with the etale one on the retained constant witness.
The closed comparison is its counit mate and restricts to the identity on B.
The normalized direct-image compositor and the identity comparison reduce the
etale composition to the defining inverse of etaleSource. Cancel these invertible
factors and use the constant-unit comparison. Tower independence gives the
same equality for every T, so no choice of tower enters the source map. -/
theorem composition_normalization [Finite A] {B X : Scheme.{u}}
    [IsNoetherian B] [IsNoetherian X] {h : X ⟶ B}
    (c : Compactification h) (s : B ⟶ X) [IsClosedImmersion s]
    (hs : s ≫ h = 𝟙 B) (T : Compactification.Triangle s h) :
    proSource A c s hs ≫ proCompositionInverse A c s hs T = 𝟙 (proConstant A B) := by
  sorry

attribute [local instance 2000] Abelian.toPreadditive
attribute [local implicit_reducible] Functor.mapDerivedCategoryPlus
attribute [local irreducible] Functor.rightDerivedFunctorPlus Functor.rightDerivedFunctor
  Functor.mapDerivedCategory

private theorem compareSupported_isIso [Finite A] {B X : Scheme.{u}}
    (s : B ⟶ X) [IsClosedImmersion s] : IsIso (compareSupported A s) := by
  with_unfolding_all
    have := supported_comparison_isIso A s
    unfold compareSupported
    infer_instance

private theorem proSource_isIso [Finite A] {B X : Scheme.{u}} {h : X ⟶ B}
    (c : Compactification h) (s : B ⟶ X) [IsClosedImmersion s]
    (hs : s ≫ h = 𝟙 B) : IsIso (proSource A c s hs) := by
  with_unfolding_all
    have := compareSupported_isIso A s
    unfold proSource sourceComparison
    infer_instance

private theorem etaleBeta_isIso {B' B X' X : Scheme.{u}}
    {g : B' ⟶ B} {s' : B' ⟶ X'} {s : B ⟶ X} {v : X' ⟶ X}
    [IsClosedImmersion s] (sq : ChosenCartesianSquare g s' s v) :
    IsIso (etaleBeta A sq) := by
  with_unfolding_all
    have hs : IsPullback g s' s v := IsPullback.of_iso_pullback
      sq.toCommSq sq.isoPullback sq.hom_fst sq.hom_snd
    have := Etale.isIso_baseChangeMap_of_isFinite (ModuleCat.{u + 1} A) hs
    have : IsIso (SupportedConstantNormalization.exchange A false sq) := by
      unfold SupportedConstantNormalization.exchange
      infer_instance
    unfold etaleBeta
    infer_instance

private theorem proBeta_isIso [Finite A] {B' B X' X : Scheme.{u}}
    {g : B' ⟶ B} {s' : B' ⟶ X'} {s : B ⟶ X} {v : X' ⟶ X}
    [IsClosedImmersion s] [IsClosedImmersion s']
    (sq : ChosenCartesianSquare g s' s v) : IsIso (proBeta A sq) := by
  with_unfolding_all
    have := supported_pro_exchange_isIso A sq
    unfold proBeta
    infer_instance

/-- The specified sources are isomorphisms, and the actual compactification
exchanges on their section-supported inputs are the identity of the base constant
under those sources. The etale source is the inverse proper/open formula; the
pro-etale source uses the actual compact-support site comparison and the canonical
supported-constant mate, with the scalar unit on the base.
Source: blueprint main-20261015, rank-one Thom proof, Step 3;
Stacks Tags 0F7B, 0F7F and 0D6E
(blueprint: lem-pur-section-compact-source-exchange).
Proof: (1) Put q = sj. Since pq = id, q is a closed section of the separated
proper p, hence proper. The same holds after arbitrary base change. Exact
etale closed direct image identifies Rs_*A with s_*A.
(2) Apply normalized proper/open interchange to (id,j,s,q), followed by the
normalized direct-image compositor for (q,p) and the identity comparison.
This is the definition of etaleSource, including on B'.
(3) Proper/open base-change coherence identifies its exchange square. Paste the
q and p module mates and use the direct-image compositor. Their composite is
the mate of the identity square on g, which is the identity by the triangle law.
Cancel the inverse source maps to obtain the etale equation below.
(4) The supported-constant mate and the compact-support site comparison are
invertible and preserve the constant unit. They identify the actual sources,
as in composition_normalization on the unprimed Noetherian schemes.
(5) Finite type over a field makes B and X Noetherian; their complementary opens
are quasi-compact, and remain so after arbitrary base change. Closed direct image
is therefore exact also in the pro-etale comparison used here.
(6) The finite-level comparison identifies the actual pro-etale compactification
exchange with transport of the etale exchange. Coherence of comparison pullback
and supported-constant exchange makes the target endpoint the same proBeta.
Substitute the etale equation; cancellation gives the pro-etale equation. On an
arbitrary B' the source is defined by this transport, without a Noetherian,
flatness, finite-type or separation hypothesis on B'. -/
theorem section_compact_source_exchange
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (n : ℕ) [Fact (1 ≤ n)] (K₀ : Type u) [Field K₀] (_hl : IsUnit (l : K₀))
    {B X : Scheme.{u}} [B.Over (Spec (.of K₀))] [X.Over (Spec (.of K₀))]
    [LocallyOfFiniteType (B ↘ Spec (.of K₀))] [QuasiCompact (B ↘ Spec (.of K₀))]
    [LocallyOfFiniteType (X ↘ Spec (.of K₀))] [QuasiCompact (X ↘ Spec (.of K₀))]
    [IsSeparated (B ↘ Spec (.of K₀))] [IsSeparated (X ↘ Spec (.of K₀))]
    (h : X ⟶ B) [h.IsOver (Spec (.of K₀))]
    [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
    (c : Compactification h) (s : B ⟶ X) [IsClosedImmersion s]
    (hs : s ≫ h = 𝟙 B)
    {B' X' : Scheme.{u}} [B'.Over (Spec (.of K₀))] [X'.Over (Spec (.of K₀))]
    (g : B' ⟶ B) [g.IsOver (Spec (.of K₀))]
    (v : X' ⟶ X) (h' : X' ⟶ B') (sq : IsPullback v h' h g)
    (s' : B' ⟶ X') [IsClosedImmersion s'] (hs' : s' ≫ h' = 𝟙 B')
    (sqS : ChosenCartesianSquare g s' s v) :
    IsIso (proSource (Coefficient l E n) c s hs) ∧
    IsIso (proSource (Coefficient l E n) (c.ofIsPullback sq) s' hs') ∧
    IsIso (etaleBeta (Coefficient l E n) sqS) ∧
    IsIso (proBeta (Coefficient l E n) sqS) ∧
    (Etale.upperStar (ModuleCat.{u + 1} (Coefficient l E n)) g).mapDerivedCategoryPlus.map
        (etaleSource (Coefficient l E n) c s hs).hom ≫
      (Etale.rightDerivedLowerShriekOfCompactificationPlusBaseChangeMap
        (Coefficient l E n) sq c).app (etaleSupported (Coefficient l E n) s) ≫
      (Etale.rightDerivedLowerShriekOfCompactificationPlus
        (ModuleCat.{u + 1} (Coefficient l E n)) (c.ofIsPullback sq)).map
        (etaleBeta (Coefficient l E n) sqS) =
      (constantPull (Coefficient l E n) g).hom ≫
        (etaleSource (Coefficient l E n) (c.ofIsPullback sq) s' hs').hom ∧
    (ProEtale.upperStar (ModuleCat.{u + 1} (Coefficient l E n)) g).mapDerivedCategoryPlus.map
        (proSource (Coefficient l E n) c s hs) ≫
      proExchange (Coefficient l E n) sq c (proSupported (Coefficient l E n) s) ≫
      (ProEtale.rightDerivedLowerShriekOfCompactificationPlus
        (ModuleCat.{u + 1} (Coefficient l E n)) (c.ofIsPullback sq)).map
        (proBeta (Coefficient l E n) sqS) =
      (proConstantPull (Coefficient l E n) g).hom ≫
        proSource (Coefficient l E n) (c.ofIsPullback sq) s' hs' := by
  refine ⟨proSource_isIso _ c s hs, proSource_isIso _ _ s' hs',
    etaleBeta_isIso _ sqS, proBeta_isIso _ sqS, ?_, ?_⟩
  · exact etale_section_exchange_component _ sq c s s' hs hs' sqS
  · exact pro_section_exchange_component _ sq c s s' hs hs' sqS
      (etale_section_exchange_component _ sq c s s' hs hs' sqS)

end AlgebraicGeometry.SectionCompactSource
