/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N9
-/
module

public import Sheaf.Algebra.Category.Ring.Sheaf.PrincipalPowerQuotients
public import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Sheaf.Algebra.Homology.SuccessiveQuotientFlatTensorSequence
import Mathlib.Algebra.Homology.DerivedCategory.ShortExact

/-! # Successive derived quotients with the quotient-ring action

Source: blueprint main-20261015, integral criterion reductions, second paragraph
(blueprint: lem-pe-successive-quotient-linear-triangle).
The endpoints are localized termwise restrictions of the specified K-flat tensor models.
The counit equations identify these models with the derived reductions of the given K.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v r wB wS wPrev wN wOne
open CategoryTheory CategoryTheory.Pretriangulated
open scoped ChangeOfRings

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
  {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasSheafify J AddCommGrpCat.{r}]

/-- Localization with its module category specified before elaborating the complex.
Source: Stacks 05RU (blueprint: lem-pe-successive-quotient-linear-triangle). -/
abbrev successiveQuotientLocalization (R : Sheaf J CommRingCat.{r})
    [HasDerivedCategory.{wS} (ringedSiteModules.{r}
      (derivedChangeRingIndependentCoefficients J R))] :
    CochainComplex (ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J R)) ℤ ⥤
      DerivedCategory (ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J R)) :=
  DerivedCategory.Q


section TriangleData
variable {B SPrev SN SOne : Sheaf J CommRingCat.{r}}
  [HasDerivedCategory.{wB} (ringedSiteModules.{r}
    (derivedChangeRingIndependentCoefficients J B))]
  [HasDerivedCategory.{wPrev} (ringedSiteModules.{r}
    (derivedChangeRingIndependentCoefficients J SPrev))]
  [HasDerivedCategory.{wN} (ringedSiteModules.{r}
    (derivedChangeRingIndependentCoefficients J SN))]
  [HasDerivedCategory.{wOne} (ringedSiteModules.{r}
    (derivedChangeRingIndependentCoefficients J SOne))]

/-- The witnesses and equations of the quotient-linear triangle assertion, packaged
before specializing the three coefficient sheaves to the principal-power quotients.
Every coefficient arrow and every tensor arrow is fixed by the displayed equations.
This structure constructs no additional derived functor or coefficient ring.
Source: blueprint, integral criterion reductions, second paragraph; Stacks 06YY, 0152
(blueprint: lem-pe-successive-quotient-linear-triangle). -/
structure SuccessiveQuotientLinearTriangle
    (t : (B.obj ⋙ CategoryTheory.forget CommRingCat.{r}).sections)
    (πPrev : B ⟶ SPrev) (πN : B ⟶ SN) (πOne : B ⟶ SOne)
    (FPrev : DerivedChangeOfRingsCochainModel.{u, v, r, wB, wPrev} πPrev)
    (FN : DerivedChangeOfRingsCochainModel.{u, v, r, wB, wN} πN)
    (FOne : DerivedChangeOfRingsCochainModel.{u, v, r, wB, wOne} πOne)
    (K : DerivedCategory (ringedSiteModules.{r}
      (derivedChangeRingIndependentCoefficients J B)))
    (G P : CochainComplex (ringedSiteModules.{r}
      (derivedChangeRingIndependentCoefficients J B)) ℤ)
    (e : DerivedCategory.Q.obj G ≅ K) (f : P ⟶ G) where
  /-- Quotient to the preceding coefficient ring. -/
  rPrev : SN ⟶ SPrev
  /-- Quotient to the first coefficient ring. -/
  rOne : SN ⟶ SOne
  /-- The canonical normalization of the first quotient map. -/
  rPrev_projection : πN ≫ rPrev = πPrev
  /-- The canonical normalization of the second quotient map. -/
  rOne_projection : πN ≫ rOne = πOne
  /-- Derived computation of the preceding quotient. -/
  ePrev : FPrev.T.obj K ≅ DerivedCategory.Q.obj (successiveQuotientTensorModel FPrev P)
  /-- Derived computation of the middle quotient. -/
  eN : FN.T.obj K ≅ DerivedCategory.Q.obj (successiveQuotientTensorModel FN P)
  /-- Derived computation of the first quotient. -/
  eOne : FOne.T.obj K ≅ DerivedCategory.Q.obj (successiveQuotientTensorModel FOne P)
  /-- The preceding computation is the one induced by the universal counit. -/
  computesPrev : FPrev.T.map (DerivedCategory.Q.map f ≫ e.hom) ≫ ePrev.hom = FPrev.ε.app P
  /-- The middle computation is the one induced by the universal counit. -/
  computesN : FN.T.map (DerivedCategory.Q.map f ≫ e.hom) ≫ eN.hom = FN.ε.app P
  /-- The first computation is the one induced by the universal counit. -/
  computesOne : FOne.T.map (DerivedCategory.Q.map f ≫ e.hom) ≫ eOne.hom = FOne.ε.app P
  /-- The termwise multiplication map, linear over the middle coefficient ring. -/
  α : successiveQuotientRestrictedModel rPrev FPrev P ⟶ successiveQuotientTensorModel FN P
  /-- The termwise quotient map, linear over the middle coefficient ring. -/
  β : successiveQuotientTensorModel FN P ⟶ successiveQuotientRestrictedModel rOne FOne P
  /-- The connecting morphism in the middle coefficient derived category. -/
  δ : (successiveQuotientLocalization SN).obj
        (successiveQuotientRestrictedModel rOne FOne P) ⟶
      ((successiveQuotientLocalization SN).obj
        (successiveQuotientRestrictedModel rPrev FPrev P))⟦(1 : ℤ)⟧
  /-- Distinguishedness over the middle coefficient ring. -/
  distinguished : Triangle.mk ((successiveQuotientLocalization SN).map α)
      ((successiveQuotientLocalization SN).map β) δ ∈
    distTriang (DerivedCategory (ringedSiteModules.{r}
      (derivedChangeRingIndependentCoefficients J SN)))
  /-- Multiplication by t on the coefficient tensor factor. -/
  alpha_formula : ∀ (i : ℤ) (U : Cᵒᵖ) (b : B.obj.obj U) (x : (P.X i).val.obj U),
    (α.f i).val.app U (successiveQuotientTensorSection FPrev (P.X i) U
      (πPrev.hom.app U b) x) =
    successiveQuotientTensorSection FN (P.X i) U
      (πN.hom.app U ((@id (B.obj.obj U) (t.val U)) * b)) x
  /-- Quotient on the coefficient tensor factor. -/
  beta_formula : ∀ (i : ℤ) (U : Cᵒᵖ) (b : B.obj.obj U) (x : (P.X i).val.obj U),
    (β.f i).val.app U (successiveQuotientTensorSection FN (P.X i) U (πN.hom.app U b) x) =
    successiveQuotientTensorSection FOne (P.X i) U (πOne.hom.app U b) x
end TriangleData

variable [HasSheafify J CommRingCat.{r}]
  (B : Sheaf J CommRingCat.{r}) (t : (B.obj ⋙ CategoryTheory.forget CommRingCat.{r}).sections)

omit [HasSheafify J CommRingCat.{r}] in
private theorem canonical_computation
    {S : Sheaf J CommRingCat.{r}} {φ : B ⟶ S}
    [HasDerivedCategory.{wB} (ringedSiteModules.{r}
      (derivedChangeRingIndependentCoefficients J B))]
    [HasDerivedCategory.{wS} (ringedSiteModules.{r}
      (derivedChangeRingIndependentCoefficients J S))]
    (F : DerivedChangeOfRingsCochainModel φ)
    (K : DerivedCategory (ringedSiteModules.{r}
      (derivedChangeRingIndependentCoefficients J B)))
    (G P : CochainComplex (ringedSiteModules.{r}
      (derivedChangeRingIndependentCoefficients J B)) ℤ)
    (e : DerivedCategory.Q.obj G ≅ K) (f : P ⟶ G)
    (hf : CochainComplex.IsKFlatResolutionIndependentCoefficients (R := B) f) :
    ∃ eP : F.T.obj K ≅ DerivedCategory.Q.obj
        ((F.E.mapHomologicalComplex (.up ℤ)).obj P),
      F.T.map (DerivedCategory.Q.map f ≫ e.hom) ≫ eP.hom = F.ε.app P := by
  have : QuasiIso f := hf.1
  have : IsIso (F.ε.app P) := F.computes P hf.2
  let q := asIso (DerivedCategory.Q.map f) ≪≫ e
  refine ⟨(F.T.mapIso q).symm ≪≫ asIso (F.ε.app P), ?_⟩
  change F.T.map q.hom ≫ _ = _
  simp

/-- Successive derived reductions form the specified distinguished triangle in D(B/t^n).
The statement uses any representative G of K and any flat-term K-flat resolution P to G.
The three e's are the canonical derived computations: their equations explicitly use
that resolution, the representative isomorphism and the universal cochain counit.
Restriction is termwise, exactly as specified in the node. The pure-tensor equations
characterize the first two maps even when quotient sections lift only locally.

Source: blueprint main-20261015, integral criterion reductions, second paragraph;
Stacks 03D7, 03ER, 06YS, 06YY, 0152
(blueprint: lem-pe-successive-quotient-linear-triangle).

Proof:
1. Apply successive_quotient_flat_tensor_sequence to the supplied flat-term complex P.
It constructs the quotient ring maps, the two normalized cochain maps and a short exact
sequence in modules over R_n. Its ordinary coefficient proof cancels t, sheafifies,
and uses the exact sheaf tensor functor in each flat degree; it makes no assumption
that section modules of P are flat.
2. Apply DerivedCategory.triangleOfSES_distinguished to this short exact sequence.
The connecting morphism and distinguishedness are constructed directly over R_n.
3. For each supplied derived-change-of-rings model, the universal counit is invertible
on the K-flat P. The quasi-isomorphism f followed by e identifies Q(P) with K. Apply
the derived functor, invert this identification and compose with the counit to obtain
the canonical computation isomorphism. Cancellation gives its prescribed equation.
4. Package the three counit comparisons, the SES triangle and its normalized maps.
No new resolution is chosen, and neither boundedness nor completeness is used. -/
theorem successive_quotient_linear_triangle (n : ℕ) (hn : 1 < n)
    (ht : ∀ U : Cᵒᵖ, Function.Injective
      (fun b : B.obj.obj U ↦ (@id (B.obj.obj U) (t.val U)) * b))
    [HasDerivedCategory.{wB} (ringedSiteModules.{r}
      (derivedChangeRingIndependentCoefficients J B))]
    [HasDerivedCategory.{wPrev} (ringedSiteModules.{r}
      (derivedChangeRingIndependentCoefficients J (principalPowerRingQuotient B t (n - 1))))]
    [HasDerivedCategory.{wN} (ringedSiteModules.{r}
      (derivedChangeRingIndependentCoefficients J (principalPowerRingQuotient B t n)))]
    [HasDerivedCategory.{wOne} (ringedSiteModules.{r}
      (derivedChangeRingIndependentCoefficients J (principalPowerRingQuotient B t 1)))]
    (FPrev : DerivedChangeOfRingsCochainModel.{u, v, r, wB, wPrev}
      (principalPowerRingProjection B t (n - 1)))
    (FN : DerivedChangeOfRingsCochainModel.{u, v, r, wB, wN}
      (principalPowerRingProjection B t n))
    (FOne : DerivedChangeOfRingsCochainModel.{u, v, r, wB, wOne}
      (principalPowerRingProjection B t 1))
    (K : DerivedCategory (ringedSiteModules.{r}
      (derivedChangeRingIndependentCoefficients J B)))
    (G P : CochainComplex (ringedSiteModules.{r}
      (derivedChangeRingIndependentCoefficients J B)) ℤ)
    (e : DerivedCategory.Q.obj G ≅ K) (f : P ⟶ G)
    (hf : CochainComplex.IsKFlatResolutionIndependentCoefficients (R := B) f)
    (hflat : ∀ i : ℤ, IsFlatOnSite (R := B) (P.X i)) :
    Nonempty (SuccessiveQuotientLinearTriangle t
      (principalPowerRingProjection B t (n - 1)) (principalPowerRingProjection B t n)
      (principalPowerRingProjection B t 1) FPrev FN FOne K G P e f) := by
  obtain ⟨S⟩ :=
    successive_quotient_flat_tensor_sequence B t n hn ht FPrev FN FOne P hflat
  obtain ⟨ePrev, hePrev⟩ := canonical_computation B FPrev K G P e f hf
  obtain ⟨eN, heN⟩ := canonical_computation B FN K G P e f hf
  obtain ⟨eOne, heOne⟩ := canonical_computation B FOne K G P e f hf
  exact ⟨{
    rPrev := S.rPrev
    rOne := S.rOne
    rPrev_projection := S.rPrev_projection
    rOne_projection := S.rOne_projection
    ePrev := ePrev
    eN := eN
    eOne := eOne
    computesPrev := hePrev
    computesN := heN
    computesOne := heOne
    α := S.α
    β := S.β
    δ := DerivedCategory.triangleOfSESδ S.shortExact
    distinguished := DerivedCategory.triangleOfSES_distinguished S.shortExact
    alpha_formula := S.alpha_formula
    beta_formula := S.beta_formula }⟩

end SheafOfModules
