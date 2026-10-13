/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence
import WeilConjectures.AlgebraicGeometry.DerivedCategories
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs

/-!
# Vanishing descends to a retract

Source: blueprint `sec-proper-base-change/sk-thm-reduction/`
`lem-weil-pbc-vanishing-descends-retract.md`, order 1188; Stacks Project,
Etale Cohomology, Tag 0A4C (lemma-sandwich), first paragraph of the proof
(blueprint: lem-weil-pbc-vanishing-descends-retract).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- Higher direct images of the underlying abelian sheaf vanish on a retract of an
acyclic sheaf of modules over a constant commutative coefficient ring.
The category of module sheaves is encoded by module-valued sheaves, as in the
six-functor convention of `def-weil-pbc-derived-categories`.

Source: blueprint `sec-proper-base-change/sk-thm-reduction/`
`lem-weil-pbc-vanishing-descends-retract.md`, order 1188; Stacks Project,
Etale Cohomology, Tag 0A4C (lemma-sandwich), first paragraph of the proof
(blueprint: lem-weil-pbc-vanishing-descends-retract).

Proof:
1. Forget the module structure using `sheafCompose` with `forget₂`. This functor
preserves the retraction equation, so the underlying abelian sheaf of `I` is a
retract of that of `M` (def-weil-sheaf-of-modules-category,
def-weil-pbc-abelian-etale-sheaves, lem-weil-pbc-functor-preserves-retract).
2. For each positive `q`, apply the composite of the degree-zero single functor,
`rightDerivedLowerStarPlus`, and the degree-`q` homology functor. It preserves
retractions by functoriality (def-weil-pbc-direct-image,
def-weil-pbc-derived-categories, lem-weil-pbc-functor-preserves-retract).
3. The resulting higher direct image of `I` is a retract of the zero object given
by `hM`. It is zero by lem-weil-pbc-retract-of-zero-object, in the abelian category
of def-weil-pbc-abelian-etale-sheaves. Since `q > 0` was arbitrary, conclude. -/
theorem vanishing_descends_retract
    {X Y : Scheme.{u}} (h : X ⟶ Y) (Λ : Type (u + 1)) [CommRing Λ]
    {I M : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)}
    (ι : I ⟶ M) (ρ : M ⟶ I) (hρ : ι ≫ ρ = 𝟙 I)
    (hM : ∀ q : ℕ, 0 < q → IsZero
      ((DerivedCategory.Plus.homologyFunctor
        (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℤ)).obj
        ((rightDerivedLowerStarPlus AddCommGrpCat.{u + 1} h).obj
          ((DerivedCategory.Plus.singleFunctor
            (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) 0).obj
            ((sheafCompose X.smallEtaleTopology
              (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj M))))) :
    ∀ q : ℕ, 0 < q → IsZero
      ((DerivedCategory.Plus.homologyFunctor
        (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℤ)).obj
        ((rightDerivedLowerStarPlus AddCommGrpCat.{u + 1} h).obj
          ((DerivedCategory.Plus.singleFunctor
            (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) 0).obj
            ((sheafCompose X.smallEtaleTopology
              (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj I)))) := by
  intro q hq
  let G := sheafCompose X.smallEtaleTopology
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}) ⋙
    DerivedCategory.Plus.singleFunctor (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) 0 ⋙
    rightDerivedLowerStarPlus AddCommGrpCat.{u + 1} h ⋙
    DerivedCategory.Plus.homologyFunctor (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) q
  have : IsSplitMono (G.map ι) := .mk' ⟨G.map ρ, by rw [← G.map_comp, hρ, G.map_id]⟩
  exact IsZero.of_mono (G.map ι) (hM q hq)

end AlgebraicGeometry.Etale
