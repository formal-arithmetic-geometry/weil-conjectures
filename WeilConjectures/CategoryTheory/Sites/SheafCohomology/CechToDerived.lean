/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Limits.Constructions.Over.Products
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Cech
public import WeilConjectures.CategoryTheory.SpectralSequence.Grothendieck

@[expose] public section

/-!
# The Čech-to-derived spectral sequence

Let `C` be a site with fibre products, `X : C` and `𝔘 = {Uᵢ ⟶ X}` a covering of `X`. For an
abelian sheaf `F` on `C` there is a first quadrant cohomological spectral sequence
`E₂^{p, q} = Ȟ^p(𝔘, ℋ^q(F)) ⟹ H^{p + q}(X, F)`, where `ℋ^q(F)` is the presheaf
`V ↦ H^q(V, F)`.

Both sides are taken from mathlib: `ℋ^q(F)` is `CategoryTheory.Sheaf.cohomologyPresheaf`,
`H^n(X, F)` is `CategoryTheory.Sheaf.H'`, and the Čech complex of the covering is
`CategoryTheory.cechComplexFunctor` applied to the family `fun i ↦ Over.mk (π i)` of objects of
`Over X` — the finite products of `Over X` used there are exactly the fibre products
`Uᵢ ×[X] Uⱼ ×[X] ⋯` of the blueprint, so `Ȟ^p(𝔘, P)` is the `p`-th cohomology of that complex,
evaluated on the restriction of `P` to `Over X`.

## Main statements

- `CategoryTheory.Sheaf.exists_cechToDerivedSpectralSequence`: the Čech-to-derived spectral
  sequence of a covering.
-/

universe w v u

namespace CategoryTheory

open Limits

attribute [local instance] Over.ConstructProducts.over_finiteProducts_of_finiteWidePullbacks

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} [HasFiniteWidePullbacks C]
  [HasSheafify J AddCommGrpCat.{v}] [HasExt.{w} (Sheaf J AddCommGrpCat.{v})]

/-- Blueprint `sk-thm-picard-cech`: Čech-to-derived.

Let `C` be a site with fibre products, `X : C` and `𝔘 = {π i : U i ⟶ X}` a family of morphisms
generating a covering sieve of `X`. For an abelian sheaf `F` on `C` there is a first quadrant
cohomological spectral sequence with `E₂^{p, q} ≅ Ȟ^p(𝔘, ℋ^q(F))` abutting to `H^{p + q}(X, F)`,
where `ℋ^q(F)` is the presheaf `V ↦ H^q(V, F)`.

The `E₂`-term is the `p`-th cohomology of the Čech complex of the family `fun i ↦ Over.mk (π i)`
of objects of `Over X` with coefficients in the restriction of `ℋ^q(F)` to `Over X`. -/
theorem Sheaf.exists_cechToDerivedSpectralSequence (F : Sheaf J AddCommGrpCat.{v}) (X : C)
    {ι : Type w} {U : ι → C} (π : ∀ i, U i ⟶ X) (hπ : Sieve.ofArrows U π ∈ J X) :
    ∃ E : E₂CohomologicalSpectralSequenceNat AddCommGrpCat.{w},
      (∀ p q : ℕ, Nonempty ((E.page 2).X (p, q) ≅
        ((cechComplexFunctor fun i ↦ Over.mk (π i)).obj
          ((Over.forget X).op ⋙ F.cohomologyPresheaf q)).homology p)) ∧
      E.AbutsTo fun n ↦ F.H' n X :=
  sorry

end CategoryTheory
