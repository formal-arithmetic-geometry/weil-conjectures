/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.PerfectReductionCoefficientUnits

/-! # Raw coordinates of the strict Koszul/Roos comparison

Source: Bhatt--Scholze, The pro-etale topology for schemes, Lemma 3.5.5 (comparison a)
(blueprint: lem-sp-perfect-reduction-koszul-delta-raw-data).

The comparison maps from the total tensor of the two-term Koszul complex with a strict Roos
limit to the strict Roos limit of the levelwise tensor tower, together with their shifted
(signed) and unshifted coordinate formulas. That these maps are isomorphisms is the separate
statement `nonempty_koszulDeltaIso`.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v r wR wA
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
  [∀ m, HasDerivedCategory.{wA} (RegularQuotientCone.Modules (powerRing R t m))]
  [HasDerivedCategory.{wR} (ℕᵒᵖ ⥤ RegularQuotientCone.Modules R)]
  [∀ m, HasDerivedCategory.{wA} (ℕᵒᵖ ⥤ RegularQuotientCone.Modules (powerRing R t m))]
  [HasCountableProducts (RegularQuotientCone.Modules R)]
  [∀ m, HasCountableProducts (RegularQuotientCone.Modules (powerRing R t m))]

/-- Chain maps `K ⊗ R lim P ⟶ R lim (K ⊗ P)` for the Koszul complexes `K = principalKoszul R t m`,
with their coordinates on every summand `K^p ⊗ (R lim P)^(i+1)`: into the shifted product the
coordinate is `(-1)^p` times the tensor of the shifted Roos coordinate, into the unshifted product
it is the tensor of the unshifted Roos coordinate. Since the summands `ι` are jointly epimorphic
and the products and biproduct are jointly monomorphic, the two formulas determine `hom`.
Source: Bhatt--Scholze 3.5.5 (blueprint: lem-sp-perfect-reduction-koszul-delta-raw-data). -/
structure KoszulDeltaRawData where
  hom : ∀ m P, ((total R).obj (principalKoszul R t m)).obj (roosF.obj P) ⟶
    roosF.obj (tensorTower R (principalKoszul R t m) P)
  shifted : ∀ m P i p n (h : p + (i + 1) = n + 1) j,
      ι R (principalKoszul R t m) (roosF.obj P) p (i + 1) (n + 1) h ≫
          (hom m P).f (n + 1) ≫
          (roosχ (tensorTower R (principalKoszul R t m) P) n).hom ≫ biprod.fst ≫
          (Pi.π (fun k : ℕ ↦ (tensorTower R (principalKoszul R t m) P).asFunctor.obj
            (op k)) j).f n =
        p.negOnePow • ((tensor R).obj ((principalKoszul R t m).X p)).map
          ((roosχ P i).hom ≫ biprod.fst ≫
            (Pi.π (fun k : ℕ ↦ P.asFunctor.obj (op k)) j).f i) ≫
          ι R (principalKoszul R t m) (P.asFunctor.obj (op j)) p i n (by omega)
  unshifted : ∀ m P i p n (h : p + (i + 1) = n + 1) j,
      ι R (principalKoszul R t m) (roosF.obj P) p (i + 1) (n + 1) h ≫
          (hom m P).f (n + 1) ≫
          (roosχ (tensorTower R (principalKoszul R t m) P) n).hom ≫ biprod.snd ≫
          (Pi.π (fun k : ℕ ↦ (tensorTower R (principalKoszul R t m) P).asFunctor.obj
            (op k)) j).f (n + 1) =
        ((tensor R).obj ((principalKoszul R t m).X p)).map
          ((roosχ P i).hom ≫ biprod.snd ≫
            (Pi.π (fun k : ℕ ↦ P.asFunctor.obj (op k)) j).f (i + 1)) ≫
          ι R (principalKoszul R t m) (P.asFunctor.obj (op j)) p (i + 1) (n + 1) h

/-- The raw finite Koszul/Roos comparison maps exist with their two coordinate formulas.
Source: Bhatt--Scholze, Lemma 3.5.5, comparison a.

Proof: in total degree `n+1` the source is the coproduct of the summands
`K^p ⊗ (R lim P)^(i+1)` with `p + (i+1) = n+1` (only `p ∈ {-1, 0}` are nonzero), and
`(R lim P)^(i+1) = ∏_j P_j^i ⊞ ∏_j P_j^(i+1)`; the target in degree `n+1` is
`∏_j (K ⊗ P_j)^n ⊞ ∏_j (K ⊗ P_j)^(n+1)`. Define `hom` on each summand by the displayed
formulas: tensor the Roos coordinate with `K^p`, include it as the summand of `K ⊗ P_j`, and
multiply the shifted component by `(-1)^p` (the total tensor sign moving the degree shift
past `K^p`). Checking the chain-map equation on each summand and coordinate is the sign
calculation of the total tensor differential against the Roos differential `1 - transition`:
the Koszul differential has degree `p` constant on the factor, the Roos differential commutes
with `K^p ⊗ -`, and the sign `(-1)^p` is exactly the one of the total differential on the
shifted factor. The two fields are then the defining formulas.
(blueprint: lem-sp-perfect-reduction-koszul-delta-raw-data) -/
theorem nonempty_koszulDeltaRawData
    (ht : Mono (globalSectionMultiplication R t))
    (d : ∀ m, DerivedChangeOfRingsCochainModel (powerProjection R t m))
    (c : CoefficientUnits R t d) : Nonempty (KoszulDeltaRawData R t) := by
  sorry
end CategoryTheory.PerfectReductionRoos
