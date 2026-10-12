/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Abelian.Injective.Resolution
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Products
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Cech
public import WeilConjectures.Algebra.Homology.TotalComplexRowResolution
public import WeilConjectures.CategoryTheory.Sites.CechSheaf
public import WeilConjectures.CategoryTheory.Sites.SheafCohomology.InjectiveResolution
public import WeilConjectures.Mathlib.Algebra.Homology.TotalComplex
public import WeilConjectures.Mathlib.Algebra.Homology.SpectralSequence.Basic

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

## Implementation notes

The general statement `exists_cechToDerivedSpectralSequence` allows a large site, a covering
indexed by `ι : Type w` and cohomology computed in `AddCommGrpCat.{w}`. The proof through the
double complex `C^p(𝔘, I^q)` needs an injective resolution of `F`, and the groups `I^q(V)` are
only `v`-small, so it is carried out under `EnoughInjectives (Sheaf J AddCommGrpCat.{v})` with
`w = v`; the resulting spectral sequence is
`CategoryTheory.Sheaf.exists_cechToDerivedSpectralSequence_of_enoughInjectives`, in
`WeilConjectures.CategoryTheory.Sites.CechSpectralSequence`.
-/

@[expose] public section

universe w v u

namespace CategoryTheory

open Limits Opposite

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

It is `D^{p, q} = C^p(𝔘, I^q)` for an injective resolution `F → I^•`: the cohomology of the
complex `I^•(V)` is `H^•(V, F)` (`Sheaf.cohomologyPresheafIso`) and cohomology commutes with the
products defining the Čech complex, so the columns compute `C^p(𝔘, ℋ^q(F))` (Step 2); the
augmented Čech complex of the injective sheaf `I^q` is exact (Stacks `03F6`, `03AW`), so
`I^•(X) ⟶ Tot D` is a quasi-isomorphism and the total complex computes
`H^n(I^•(X)) = H^n(X, F)` (Step 3).

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
  let R : InjectiveResolution F := injectiveResolution F
  let V : ι → Over X := fun i ↦ Over.mk (π i)
  -- the presheaf of complexes `V ↦ I^•(V)` on `Over X`
  let Pc : (Over X)ᵒᵖ ⥤ CochainComplex AddCommGrpCat.{v} ℕ :=
    (Over.forget X).op ⋙ Sheaf.complexSections R.cocomplex
  let D : HomologicalComplex₂ AddCommGrpCat.{v} (ComplexShape.up ℕ) (ComplexShape.up ℕ) :=
    (cechComplexFunctor V).obj Pc
  refine ⟨D, fun q ↦ ⟨?_⟩, fun n ↦ ⟨?_⟩⟩
  · exact cechComplexFunctorMapIso V (HomologicalComplex.homologyFunctor _ _ q) Pc ≪≫
      (cechComplexFunctor V).mapIso
        (Functor.isoWhiskerLeft (Over.forget X).op (Sheaf.cohomologyPresheafIso R q))
  -- the rows of `D` are the Čech complexes of the injective sheaves `I^q`
  let e (q : ℕ) := cechComplexFunctorMapIso V (HomologicalComplex.eval _ _ q) Pc
  let ε := cechAugmentation V Over.mkIdTerminal Pc
  have hε : ε ≫ D.d 0 1 = 0 := cechAugmentation_d V Over.mkIdTerminal Pc
  have hfac (q : ℕ) : ε.f q ≫ (e q).hom.f 0 =
      cechAugmentation V Over.mkIdTerminal ((Over.forget X).op ⋙ (R.cocomplex.X q).obj) :=
    map_cechAugmentation_comp V Over.mkIdTerminal (HomologicalComplex.eval _ _ q) Pc
  have h₀ (q : ℕ) : Mono (ε.f q) := by
    have : Mono (ε.f q ≫ (e q).hom.f 0) := by
      rw [hfac]
      exact Presheaf.mono_cechAugmentation_of_isSheaf (V := V) (R.cocomplex.X q).property hπ
    exact mono_of_mono _ ((e q).hom.f 0)
  have h₁ (q : ℕ) : (ShortComplex.mk (ε.f q) ((D.d 0 1).f q)
      (by rw [← HomologicalComplex.comp_f, hε, HomologicalComplex.zero_f])).Exact := by
    have h := Presheaf.exact_cechAugmentation_of_isSheaf (V := V) (R.cocomplex.X q).property hπ
    refine (ShortComplex.exact_iff_of_iso ?_).2 h
    refine ShortComplex.isoMk (Iso.refl _) (HomologicalComplex.Hom.isoApp (e q) 0)
      (HomologicalComplex.Hom.isoApp (e q) 1) ?_ ((e q).hom.comm 0 1)
    rw [Iso.refl_hom, Category.id_comp]
    exact (hfac q).symm
  have hrow (p q : ℕ) : (ShortComplex.mk ((D.d p (p + 1)).f q) ((D.d (p + 1) (p + 2)).f q)
      (by rw [← HomologicalComplex.comp_f, HomologicalComplex.d_comp_d,
        HomologicalComplex.zero_f])).Exact := by
    have := Sheaf.injective_obj (R.cocomplex.X q)
    exact (ShortComplex.exact_iff_of_iso
      ((HomologicalComplex.shortComplexFunctor' _ _ p (p + 1) (p + 2)).mapIso (e q))).2
      (Presheaf.exact_cechComplexFunctor_of_injective V (R.cocomplex.X q).obj p)
  have := HomologicalComplex₂.quasiIso_toTotalOfAugmentation (hε := hε) h₀ h₁ hrow
  exact (isoOfQuasiIsoAt (D.toTotalOfAugmentation ε hε) n).symm ≪≫
    Sheaf.cohomologyPresheafIsoApp R n (op X)

end CategoryTheory
