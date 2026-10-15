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
import Sheaf.CategoryTheory.CechResolutionColumns
import Sheaf.CategoryTheory.CechResolutionTotal
import WeilConjectures.Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import Mathlib.Algebra.Category.Grp.AB

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

The statement `exists_cechToDerivedSpectralSequence` records the source's
small-site convention by assuming `EssentiallySmall.{v} C`. Its covering indices,
cohomology groups and sheaf values are all in universe `v`. Enough injectives
follows from Grothendieck abelianness; it is not an additional hypothesis there.
The two helpers allow arbitrary `C`, assuming enough injectives explicitly.
-/

@[expose] public section

universe v u

namespace CategoryTheory

open Limits

attribute [local instance] Over.ConstructProducts.over_finiteProducts_of_finiteWidePullbacks

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} [HasFiniteWidePullbacks C]
  [HasSheafify J AddCommGrpCat.{v}]

/-- **The Čech-to-derived spectral sequence on an essentially small site.**
Let `C` be an essentially `v`-small site with fibre products, `X : C`, and
`𝔘 = {π i : U i ⟶ X}` a `v`-small family generating a covering sieve. For an
abelian sheaf `F` there is a first quadrant cohomological spectral sequence with
`E₂^{p, q} ≅ Ȟ^p(𝔘, ℋ^q(F))` abutting to `H^{p + q}(X, F)`.

The `E₂`-term is the cohomology of Mathlib's Čech complex on `Over X`, with
coefficients in the restriction of the cohomology presheaf.

Source: Stacks Tags 03AZ and 00VI; blueprint sk-thm-picard-cech, Steps 1--4.
The smallness assumption records the source's site convention (00VI). The
category of abelian sheaves is Grothendieck abelian, hence has enough injectives.
Choose an injective resolution and form its Čech double complex. Exact products
identify column cohomology with the Čech complex of the cohomology presheaf;
injective Čech acyclicity identifies total cohomology with sheaf cohomology.
Apply the first bicomplex spectral sequence and transport these identifications.
This corrects the previous unsupported large-site, independent-universe assertion;
it does not claim that assertion follows from `HasExt` alone.
(blueprint: lem-sc-cech-spectral) -/
theorem Sheaf.exists_cechToDerivedSpectralSequence [EssentiallySmall.{v} C]
    [HasExt.{v} (Sheaf J AddCommGrpCat.{v})]
    (F : Sheaf J AddCommGrpCat.{v}) (X : C)
    {ι : Type v} {U : ι → C} (π : ∀ i, U i ⟶ X) (hπ : Sieve.ofArrows U π ∈ J X) :
    ∃ E : E₂CohomologicalSpectralSequenceNat AddCommGrpCat.{v},
      (∀ p q : ℕ, Nonempty ((E.page 2).X (p, q) ≅
        ((cechComplexFunctor fun i ↦ Over.mk (π i)).obj
          ((Over.forget X).op ⋙ F.cohomologyPresheaf q)).homology p)) ∧
      E.AbutsTo fun n ↦ F.H' n X := by
  let := Sheaf.isGrothendieckAbelian_of_essentiallySmall' J AddCommGrpCat.{v}
  let I := injectiveResolution F
  let D := Sheaf.cechResolutionDoubleComplex I X π
  obtain ⟨E, hE₂, hE⟩ := D.exists_spectralSequence
  refine ⟨E, fun p q ↦ ?_, hE.of_nonempty_iso fun n ↦
    Sheaf.cechResolutionDoubleComplex_total I X π hπ n⟩
  obtain ⟨e⟩ := hE₂ p q
  exact ⟨e ≪≫ (HomologicalComplex.homologyFunctor _ _ p).mapIso
    (Sheaf.cechResolutionDoubleComplex_columns I X π q).some⟩

/-- **The Čech double complex of a covering.** Let `𝔘 = {π i : U i ⟶ X}` generate a covering
sieve of `X` and let `F` be an abelian sheaf, on a site whose abelian sheaves have enough
injectives. There is a first quadrant double complex `D` of abelian groups such that

* for every `q`, the complex `p ↦ H^q(D^{p, •})` is the Čech complex `C^•(𝔘, ℋ^q(F))` of the
  presheaf `ℋ^q(F) : V ↦ H^q(V, F)`;
* the total complex of `D` computes the cohomology `H^n(X, F)`.

It is `D^{p, q} = C^p(𝔘, I^q)` for an injective resolution `F → I^•`. The
sheafification/free-abelian Yoneda adjunction identifies evaluation at each
`V = U i₀ ×[X] ⋯ ×[X] U iₚ` with Hom from its free abelian sheaf. Computing Ext
with `I^•` and commuting cohomology with products gives the columns
`C^p(𝔘, ℋ^q(F))` (Step 2). The Čech complex of the injective sheaf `I^q` resolves
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
      ∀ n : ℕ, Nonempty ((D.total (ComplexShape.up ℕ)).homology n ≅ F.H' n X) := by
  let I := injectiveResolution F
  refine ⟨Sheaf.cechResolutionDoubleComplex I X π, ?_, ?_⟩
  · exact fun q ↦ Sheaf.cechResolutionDoubleComplex_columns I X π q
  · exact fun n ↦ Sheaf.cechResolutionDoubleComplex_total I X π hπ n

/-- **The Čech-to-derived spectral sequence, with enough injectives.** The
spectral-sequence conclusion on any site whose abelian sheaves have enough injectives,
with covering indices and cohomology in universe `v`. Unlike the small-site theorem,
this helper assumes enough injectives directly and needs no smallness of the site.

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
