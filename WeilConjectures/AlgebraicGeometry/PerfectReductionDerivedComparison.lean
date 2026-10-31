/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.PerfectReductionKoszulComparison

/-! # Descent of perfect reduction on the category of whole strict towers

Source: Bhatt--Scholze, Lemma 3.5.5, perfect-complex comparison a.
(blueprint: lem-sp-perfect-reduction-derived-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u v r wR wA a b w
open CategoryTheory CategoryTheory.Limits Opposite
open SheafOfModules SheafOfModules.RegularQuotientCone SheafOfModules.TotalTensorSigns
open scoped ChangeOfRings

namespace CategoryTheory.PerfectReductionRoos

variable {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
  {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasSheafify J AddCommGrpCat.{r}]
  [HasSheafify J CommRingCat.{r}]
  (R : Sheaf J CommRingCat.{r})
  (t : (unit (derivedChangeRingIndependentCoefficients J R)).sections)


variable [HasDerivedCategory.{wR} (RegularQuotientCone.Modules R)]
  [HasDerivedCategory.{wR} (ℕᵒᵖ ⥤ RegularQuotientCone.Modules R)]
  [∀ m, HasDerivedCategory.{wA} (RegularQuotientCone.Modules (powerRing R t m))]
  [∀ m, HasDerivedCategory.{wA} (ℕᵒᵖ ⥤ RegularQuotientCone.Modules (powerRing R t m))]
  [HasCountableProducts (RegularQuotientCone.Modules R)]
  [∀ m, HasCountableProducts (RegularQuotientCone.Modules (powerRing R t m))]

/-- Derive scalar extension on the whole strict tower and descend the normalized
perfect comparison, retaining its actual quotient-change maps.

Source: Bhatt--Scholze, The pro-etale topology for schemes, Lemma 3.5.5, comparison a
(blueprint: lem-sp-perfect-reduction-derived-comparison).

Proof:
1. Use a simultaneous flat-term K-flat resolution on the ringed sequence site
of the constant coefficient system. The supplied whole-tower universal extension
computes on these levelwise K-flat complexes by he. Thus its counit identifies the
ordinary extended strict tower with the whole derived scalar extension.
2. On such a resolution P, write M for its strict Roos complex. Exact countable
products preserve the coefficient short exact sequences of the flat terms of P.
Hence t^(m+1) is injective on every term of M, and ordinary reduction of M is the
Roos complex of the ordinarily reduced strict tower. The latter carries its actual
quotient-module action and its actual tower transitions.
3. Apply the derived coefficient adjunction to the whole-system coefficient unit.
Its normalized adjunct defines the natural transformation theta; this is a map
in the quotient coefficient category. The universal counits and the two chosen
Roos localization comparisons give exactly epsilon_M followed by the additive
Roos comparison on every strict model, not only on resolutions. Uniqueness of
localization and derived-functor factorization extends it to every derived tower.
4. Resolve M by a K-flat flat-term Q. Tensoring Q to M with the finite-free
Koszul complex is a quasi-isomorphism. The Koszul augmentations at Q and M are
quasi-isomorphisms, the latter by the degreewise regular coefficient sequence.
Their strict commuting square implies the restricted adjunct is a
quasi-isomorphism. Exact restriction detects it, so the quotient-linear adjunct
and hence theta are invertible. Independence of the chosen Roos localizations
follows from their specified kappa comparisons and localization uniqueness.
5. For l <= m sheafify the ordinary quotient A_m to A_l. Normalize its ordinary
extension/restriction comparison on pure tensors a tensor x to bar(a) tensor x.
Restriction is exact, so it localizes with the comparison w. Derive this ordinary
comparison with the universal counits to obtain qD and its required equation.
Both strict coefficient units are x mapping to 1 tensor x; their quotient-change
square commutes. Derived coefficient adjunction and uniqueness of descent give
the square of the model maps. This also covers l=m and does not use faithfulness
of restriction on derived morphisms. -/
theorem exists_derivedComparison
    [HasExactLimitsOfShape (Discrete ℕ) (RegularQuotientCone.Modules R)]
    (ht : Mono (globalSectionMultiplication R t))
    (d : ∀ m, DerivedChangeOfRingsCochainModel (powerProjection R t m))
    (c : CoefficientUnits R t d)
    (k : KoszulComparison R t d c)
    (cR : RoosModel (RegularQuotientCone.Modules R))
    (cA : ∀ m, RoosModel (RegularQuotientCone.Modules (powerRing R t m)))
    (e : ∀ m, TowerExtension (d m).E)
    (he : ∀ m (P : CochainComplex (ℕᵒᵖ ⥤ RegularQuotientCone.Modules R) ℤ),
      (∀ n, CochainComplex.IsKFlatIndependentCoefficients (R := R)
        (P.asFunctor.obj (op n))) → IsIso ((e m).ε.app P)) :
    ∃ θ : ∀ m, cR.F ⋙ (d m).T ≅ (e m).F ⋙ (cA m).F,
      ComparisonData.normalization R t d cR cA (k.withDerived R t cR cA e θ) ∧
      ComparisonData.quotient_changes R t d cR cA (k.withDerived R t cR cA e θ) := by
  sorry

end CategoryTheory.PerfectReductionRoos
