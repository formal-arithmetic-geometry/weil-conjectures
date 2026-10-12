/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Limits.Constructions.Over.Products
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Cech
public import WeilConjectures.Mathlib.Algebra.Homology.TotalComplex
import Sheaf.CategoryTheory.SiteInjectiveCechAcyclic

/-!
# The Čech-to-derived spectral sequence

Let `C` be a site with fibre products, `X : C` and `𝔘 = {Uᵢ ⟶ X}` a covering of `X`. For an
abelian sheaf `F` on `C` there is a first quadrant cohomological spectral sequence
`E₂^{p, q} = Ȟ^p(𝔘, ℋ^q(F)) ⟹ H^{p + q}(X, F)`, where `ℋ^q(F)` is the presheaf
`V ↦ H^q(V, F)`.

Both sides are taken from Mathlib: `ℋ^q(F)` is `CategoryTheory.Sheaf.cohomologyPresheaf`,
`H^n(X, F)` is `CategoryTheory.Sheaf.H'`, and the Čech complex of the covering is
`CategoryTheory.cechComplexFunctor` applied to the family `fun i ↦ Over.mk (π i)` of objects of
`Over X` — the finite products of `Over X` used there are exactly the fibre products
`Uᵢ ×[X] Uⱼ ×[X] ⋯`, so `Ȟ^p(𝔘, P)` is the `p`-th cohomology of that complex, evaluated on the
restriction of `P` to `Over X`.

## Main statements

- `CategoryTheory.Sheaf.exists_cechToDerivedSpectralSequence`: the Čech-to-derived spectral
  sequence of a covering.
- `CategoryTheory.Sheaf.exists_cechDoubleComplex`: when abelian sheaves have enough injectives,
  the double complex `C^p(𝔘, I^q)` attached to an injective resolution `F → I^•`, through its
  column cohomology and the cohomology of its total complex.
- `CategoryTheory.Sheaf.exists_cechToDerivedSpectralSequence_of_enoughInjectives`: the
  Čech-to-derived spectral sequence when abelian sheaves have enough injectives and all
  universes agree, as the first spectral sequence `HomologicalComplex₂.exists_spectralSequence`
  of that double complex.

## Implementation notes

The general statement `exists_cechToDerivedSpectralSequence` allows a large site, a covering
indexed by `ι : Type w` and cohomology computed in `AddCommGrpCat.{w}`. The proof through the
double complex `C^p(𝔘, I^q)` needs an injective resolution of `F`, and the groups `I^q(V)` are
only `v`-small, so it is carried out under `EnoughInjectives (Sheaf J AddCommGrpCat.{v})` with
`w = v`.
-/

@[expose] public section

universe w v u

namespace CategoryTheory

open Limits

attribute [local instance] Over.ConstructProducts.over_finiteProducts_of_finiteWidePullbacks

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} [HasFiniteWidePullbacks C]
  [HasSheafify J AddCommGrpCat.{v}]

/-- **The Čech-to-derived spectral sequence.** Let `C` be a site with fibre products, `X : C` and
`𝔘 = {π i : U i ⟶ X}` a family of morphisms generating a covering sieve of `X`. For an abelian
sheaf `F` on `C` there is a first quadrant cohomological spectral sequence with
`E₂^{p, q} ≅ Ȟ^p(𝔘, ℋ^q(F))` abutting to `H^{p + q}(X, F)`, where `ℋ^q(F)` is the presheaf
`V ↦ H^q(V, F)`.

The `E₂`-term is the `p`-th cohomology of the Čech complex of the family `fun i ↦ Over.mk (π i)`
of objects of `Over X` with coefficients in the restriction of `ℋ^q(F)` to `Over X`.

(blueprint: `sk-thm-picard-cech`, `lem-sc-cech-spectral`) -/
theorem Sheaf.exists_cechToDerivedSpectralSequence [HasExt.{w} (Sheaf J AddCommGrpCat.{v})]
    (F : Sheaf J AddCommGrpCat.{v}) (X : C)
    {ι : Type w} {U : ι → C} (π : ∀ i, U i ⟶ X) (hπ : Sieve.ofArrows U π ∈ J X) :
    ∃ E : E₂CohomologicalSpectralSequenceNat AddCommGrpCat.{w},
      (∀ p q : ℕ, Nonempty ((E.page 2).X (p, q) ≅
        ((cechComplexFunctor fun i ↦ Over.mk (π i)).obj
          ((Over.forget X).op ⋙ F.cohomologyPresheaf q)).homology p)) ∧
      E.AbutsTo fun n ↦ F.H' n X :=
  sorry

/-- **The Čech double complex of a covering.** Let `𝔘 = {π i : U i ⟶ X}` generate a covering
sieve of `X` and let `F` be an abelian sheaf, on a site whose abelian sheaves have enough
injectives. There is a first quadrant double complex `D` of abelian groups such that

* for every `q`, the complex `p ↦ H^q(D^{p, •})` is the Čech complex `C^•(𝔘, ℋ^q(F))` of the
  presheaf `ℋ^q(F) : V ↦ H^q(V, F)`;
* the total complex of `D` computes the cohomology `H^n(X, F)`.

It is `D^{p, q} = C^p(𝔘, I^q)` for an injective resolution `F → I^•`: restricting `I^•` to
`V = U i₀ ×[X] ⋯ ×[X] U iₚ` is again an injective resolution, so the columns compute
`C^p(𝔘, ℋ^q(F))` (Step 2), and the Čech complex of the injective sheaf `I^q` is a resolution of
`I^q(X)` (Stacks `03F6`, `03AW`), so the total complex computes `H^n(I^•(X)) = H^n(X, F)`
(Step 3).

The groups `I^q(V)` are only `v`-small, so `D` lives in `AddCommGrpCat.{v}`; this is why the
covering is indexed by `ι : Type v` and the cohomology is computed in `AddCommGrpCat.{v}`.

(blueprint: `sk-thm-picard-cech`, Steps 1 to 3 of the proof) -/
theorem Sheaf.exists_cechDoubleComplex [HasExt.{v} (Sheaf J AddCommGrpCat.{v})]
    [EnoughInjectives (Sheaf J AddCommGrpCat.{v})] (F : Sheaf J AddCommGrpCat.{v}) (X : C)
    {ι : Type v} {U : ι → C} (π : ∀ i, U i ⟶ X) (hπ : Sieve.ofArrows U π ∈ J X) :
    ∃ D : HomologicalComplex₂ AddCommGrpCat.{v} (ComplexShape.up ℕ) (ComplexShape.up ℕ),
      (∀ q : ℕ, Nonempty
        (((HomologicalComplex.homologyFunctor _ (ComplexShape.up ℕ) q).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj D ≅
        (cechComplexFunctor fun i ↦ Over.mk (π i)).obj
          ((Over.forget X).op ⋙ F.cohomologyPresheaf q))) ∧
      ∀ n : ℕ, Nonempty ((D.total (ComplexShape.up ℕ)).homology n ≅ F.H' n X) :=
  sorry

/-- **The Čech-to-derived spectral sequence, with enough injectives.** The special case of
`Sheaf.exists_cechToDerivedSpectralSequence` where abelian sheaves on `C` have enough injectives,
the covering is indexed by `ι : Type v` and cohomology is computed in `AddCommGrpCat.{v}`.

It is the first spectral sequence of the double complex `Sheaf.exists_cechDoubleComplex`.

(blueprint: `sk-thm-picard-cech`, `lem-sc-cech-spectral`) -/
theorem Sheaf.exists_cechToDerivedSpectralSequence_of_enoughInjectives
    [HasExt.{v} (Sheaf J AddCommGrpCat.{v})] [EnoughInjectives (Sheaf J AddCommGrpCat.{v})]
    (F : Sheaf J AddCommGrpCat.{v}) (X : C)
    {ι : Type v} {U : ι → C} (π : ∀ i, U i ⟶ X) (hπ : Sieve.ofArrows U π ∈ J X) :
    ∃ E : E₂CohomologicalSpectralSequenceNat AddCommGrpCat.{v},
      (∀ p q : ℕ, Nonempty ((E.page 2).X (p, q) ≅
        ((cechComplexFunctor fun i ↦ Over.mk (π i)).obj
          ((Over.forget X).op ⋙ F.cohomologyPresheaf q)).homology p)) ∧
      E.AbutsTo fun n ↦ F.H' n X := by
  obtain ⟨D, hcol, htot⟩ := F.exists_cechDoubleComplex X π hπ
  obtain ⟨E, hE₂, hE⟩ := D.exists_spectralSequence
  refine ⟨E, fun p q ↦ ?_, hE.of_iso fun n ↦ (htot n).some⟩
  obtain ⟨e⟩ := hE₂ p q
  exact ⟨e ≪≫ (HomologicalComplex.homologyFunctor _ _ p).mapIso (hcol q).some⟩

end CategoryTheory
