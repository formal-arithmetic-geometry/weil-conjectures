/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF groups N6 and Q97
-/
module

public import Sheaf.Algebra.Homology.InternalHomLocalizationComparison

/-! # Localization continuity and evaluation-defined internal-Hom comparisons

Source: Bhatt--Scholze, Lemma 6.8.12 and Proposition 6.8.14(2), pp. 61--62,
conditional internal-sheaf formulation; Stacks Project, Tags 03DB, 07A4, 07A6,
08J7, 08J9 and 0A95
(blueprint: def-sfb-localization-hom-comparison-data).

The five constructions of this node are the published declarations of
`Sheaf.Algebra.Homology.InternalHomLocalizationComparison`, reexported here unchanged:
`localizationHomComplex` (the fixed functorial K-injective Hom representatives
`Γ_K(P) = Hom_R(Q_R⁻¹K, I_R(P))`), `localizationHomContinuityMap` (Q of `colimit.post`),
`HasLocalizationHomContinuity` (that map is invertible for every sequential diagram with a
common termwise lower bound), `localizationHomComparison` (χ, the transpose over S of
extended evaluation composed with the inverse strong tensor comparison) and
`localizationHomRestrictedComparison` (ρ = α ∘ U(χ)).
They are not redeclared, so that one definition per notion is kept.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe c v r w

open CategoryTheory CategoryTheory.Limits Opposite WeilConjectures SheafOfModules

namespace CategoryTheory

variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [J.HasSheafCompose (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})]
  [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  [∀ R : Sheaf J CommRingCat.{max c v r}, HasDerivedCategory.{w} (scalarModules J R)]

/-- The sequential-continuity predicate of this node under its descriptive name: the
transparent name of the published `HasLocalizationHomContinuity`. The evaluation-induced
map `Q(colimit.post D Γ_K)` is invertible for every ℕ-diagram `D` of complexes with one
common termwise lower bound. Source: Bhatt--Scholze 6.8.12, conditional internal-sheaf
formulation; Stacks 03DB and 08J9
(blueprint: def-sfb-localization-hom-comparison-data). -/
abbrev HasLocalizationHomSequentialContinuity (R : Sheaf J CommRingCat.{max c v r})
    (K : DerivedCategory (scalarModules J R)) : Prop :=
  HasLocalizationHomContinuity.{c, v, r, w} J R K

end CategoryTheory
