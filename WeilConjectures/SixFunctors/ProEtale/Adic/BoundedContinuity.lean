/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Triangulated.HomologicalFilteredColimit
public import WeilConjectures.SixFunctors.ProEtale.Adic.ClosedSupport

/-!
# Bounded-below continuity of cohomology for `ℓ`-adic sheaves

For a quasi-compact quasi-separated scheme `Y` and a filtered diagram `(K_i)` of complexes of
sheaves of `ℚ̄_ℓ,Y`-modules on `Y_proét`, all vanishing below a fixed degree `a`, with termwise
colimit `K`:

1. `colim_i H^q(Y, K_i) ≅ H^q(Y, K)` for every `q`
   (`AlgebraicGeometry.ProEtale.isIso_colimitDesc_hypercohomology`, blueprint
   `det-lem-bounded-continuity-sections` (3)); here `H^q(Y, K) = Hom_{D(Y)}(ℚ̄_ℓ,Y, K[q])`;
2. for `g : Y ⟶ Z` quasi-compact and quasi-separated, `colim_i R^q g_* K_i ≅ R^q g_* K`
   (`AlgebraicGeometry.ProEtale.isIso_colimitDesc_homology_rightDerivedLowerStar`, blueprint
   `det-lem-bounded-continuity-direct-image`).

These belong to the chapter on pro-étale coefficients (`sk-cor-pe-bounded-continuity`), stated
there for sheaves of modules over any sheaf of rings; they are stated here with `sorry` for the
constant `ℓ`-adic sheaf of rings.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.ProEtale

variable {l : ℕ} [Fact l.Prime]

/-- The cohomology functor `H^0(Y, -) = Hom_{D(Y)}(ℚ̄_ℓ,Y, -)` on the derived category of sheaves
of `ℚ̄_ℓ,Y`-modules; its shifts are the `H^q(Y, -)`. -/
noncomputable abbrev adicHypercohomology (Y : Scheme.{u}) :
    DerivedCategory (AdicSheaf l Y) ⥤ AddCommGrpCat.{u + 1} :=
  preadditiveCoyoneda.obj
    (op ((DerivedCategory.singleFunctor (AdicSheaf l Y) 0).obj (Mod.regular _)))

/-- Blueprint `det-lem-bounded-continuity-sections` (3): **hypercohomology on a quasi-compact
quasi-separated scheme commutes with bounded-below filtered colimits.** For a filtered diagram
`(K_i)` of complexes of sheaves of `ℚ̄_ℓ,Y`-modules vanishing in degrees `< a`, with colimit `K`,
the map `colim_i H^q(Y, K_i) ⟶ H^q(Y, K)` is an isomorphism for every `q`. -/
theorem isIso_colimitDesc_hypercohomology (Y : Scheme.{u}) [CompactSpace Y]
    [QuasiSeparatedSpace Y] {I : Type (u + 1)} [SmallCategory I] [IsFiltered I]
    (K : I ⥤ CochainComplex (AdicSheaf l Y) ℤ) (a : ℤ) (hK : ∀ i, (K.obj i).IsStrictlyGE a)
    (c : Cocone K) (hc : IsColimit c) (q : ℤ) :
    IsIso (colimit.desc ((K ⋙ DerivedCategory.Q) ⋙ shiftFunctor _ q ⋙ adicHypercohomology Y)
      ((shiftFunctor _ q ⋙ adicHypercohomology Y).mapCocone (DerivedCategory.Q.mapCocone c))) :=
  sorry

/-- Blueprint `det-lem-bounded-continuity-direct-image`: **higher direct images commute with
bounded-below filtered colimits.** For a quasi-compact quasi-separated morphism `g : Y ⟶ Z` and
a filtered diagram `(K_i)` of complexes of sheaves of `ℚ̄_ℓ,Y`-modules vanishing in degrees
`< a`, with colimit `K`, the map `colim_i R^q g_* K_i ⟶ R^q g_* K` is an isomorphism for every
`q`. -/
theorem isIso_colimitDesc_homology_rightDerivedLowerStar {Y Z : Scheme.{u}} (g : Y ⟶ Z)
    [QuasiCompact g] [QuasiSeparated g] {I : Type (u + 1)} [SmallCategory I] [IsFiltered I]
    (K : I ⥤ CochainComplex (AdicSheaf l Y) ℤ) (a : ℤ) (hK : ∀ i, (K.obj i).IsStrictlyGE a)
    (c : Cocone K) (hc : IsColimit c) (q : ℤ) :
    IsIso (colimit.desc ((K ⋙ DerivedCategory.Q ⋙ (g)_*ᵃ[l].rightDerivedFunctor) ⋙
        DerivedCategory.homologyFunctor _ q)
      ((DerivedCategory.homologyFunctor _ q).mapCocone
        ((DerivedCategory.Q ⋙ (g)_*ᵃ[l].rightDerivedFunctor).mapCocone c))) :=
  sorry

end AlgebraicGeometry.ProEtale
