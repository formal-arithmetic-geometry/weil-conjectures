/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.SixFunctors.OrdinaryDerivedChangeOfRings
public import WeilConjectures.Algebra.Homology.RegularQuotientCone.RegularQuotientConeBasic
public import WeilConjectures.CategoryTheory.Principal.PrincipalKoszulQuotientTowersSupplement
public import WeilConjectures.Algebra.Homology.TotalTensorSigns.TotalTensorHomotopyConeSigns
public import WeilConjectures.CategoryTheory.Principal.PrincipalPowerQuotients
public import WeilConjectures.CategoryTheory.Roos.RoosComparisonHorizontalCoherenceSupplement
public import WeilConjectures.CategoryTheory.CofinalRoos.CofinalRoosRestriction
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit

/-! # Perfect reduction and the strict Roos limit

Source: Bhatt--Scholze, The pro-etale topology for schemes, Lemma 3.5.5 (comparison a)
and Proposition 3.1.11 (blueprint: def-sp-perfect-reduction-roos-comparison-data).

Positive powers are indexed by their predecessors. The comparison is a natural
isomorphism on the derived category of strict towers. Its model equation uses the
universal coefficient counits, and therefore specifies actual coefficient-linear maps.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u v r wR wA a b w
open CategoryTheory CategoryTheory.Limits Opposite
open SheafOfModules SheafOfModules.RegularQuotientCone
open SheafOfModules.TotalTensorSigns
open scoped ChangeOfRings

namespace CategoryTheory.PerfectReductionRoos

/-- A localization of the fixed strict Roos model, including its comparison.
Source: Bhatt--Scholze 3.1.11; Stacks 0941
(blueprint: def-sp-perfect-reduction-roos-comparison-data). -/
structure RoosModel (A : Type a) [Category.{b} A] [Abelian A]
    [HasCountableProducts A] [HasDerivedCategory.{w} A]
    [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ A)] where
  F : DerivedCategory (ℕᵒᵖ ⥤ A) ⥤ DerivedCategory A
  κ : roosF ⋙ DerivedCategory.Q ≅ DerivedCategory.Q ⋙ F

/-- The derived extension of the entire strict tower, with its universal counit.
Source: Bhatt--Scholze 3.5.5; Stacks 06YY on the sequence site
(blueprint: def-sp-perfect-reduction-roos-comparison-data). -/
structure TowerExtension {A : Type a} [Category.{b} A] [Abelian A]
    {B : Type u} [Category.{v} B] [Abelian B]
    [HasCountableProducts A] [HasCountableProducts B]
    [HasDerivedCategory.{wR} (ℕᵒᵖ ⥤ A)] [HasDerivedCategory.{wA} (ℕᵒᵖ ⥤ B)]
    (E : A ⥤ B) [E.Additive] where
  F : DerivedCategory (ℕᵒᵖ ⥤ A) ⥤ DerivedCategory (ℕᵒᵖ ⥤ B)
  ε : DerivedCategory.Q ⋙ F ⟶ roosTowerAction E ⋙ DerivedCategory.Q
  universal : F.IsLeftDerivedFunctor ε
    (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ A) (.up ℤ))

variable {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
  {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasSheafify J AddCommGrpCat.{r}]
  [HasSheafify J CommRingCat.{r}]
  (R : Sheaf J CommRingCat.{r})
  (t : (unit (derivedChangeRingIndependentCoefficients J R)).sections)

/-- The same global section viewed in the underlying ring sheaf.
Source: Bhatt--Scholze 3.5.5, regular quotient
(blueprint: def-sp-perfect-reduction-roos-comparison-data). -/
def ringSection : (R.obj ⋙ forget CommRingCat.{r}).sections :=
  ⟨t.val, t.property⟩

/-- The actual ring quotient of exponent `m+1`.
Source: Bhatt--Scholze 3.5.5
(blueprint: def-sp-perfect-reduction-roos-comparison-data). -/
abbrev powerRing (m : ℕ) := principalPowerRingQuotient R (ringSection R t) (m + 1)

/-- The actual quotient homomorphism of exponent `m+1`.
Source: Bhatt--Scholze 3.5.5
(blueprint: def-sp-perfect-reduction-roos-comparison-data). -/
abbrev powerProjection (m : ℕ) :=
  principalPowerRingProjection R (ringSection R t) (m + 1)

/-- Tensor the levels of a tower with a specified coefficient complex, without changing
its strict transitions. Source: Bhatt--Scholze 3.5.5, finite-free calculation
(blueprint: def-sp-perfect-reduction-roos-comparison-data). -/
def tensorTower (K : CochainComplex (RegularQuotientCone.Modules R) ℤ)
    (P : CochainComplex (ℕᵒᵖ ⥤ RegularQuotientCone.Modules R) ℤ) :=
  koszulTowerComplex R (P.asFunctor ⋙ (total R).obj K)

variable [HasDerivedCategory.{wR} (RegularQuotientCone.Modules R)]
  [HasDerivedCategory.{wR} (ℕᵒᵖ ⥤ RegularQuotientCone.Modules R)]
  [∀ m, HasDerivedCategory.{wA} (RegularQuotientCone.Modules (powerRing R t m))]
  [∀ m, HasDerivedCategory.{wA} (ℕᵒᵖ ⥤ RegularQuotientCone.Modules (powerRing R t m))]
  [HasCountableProducts (RegularQuotientCone.Modules R)]
  [∀ m, HasCountableProducts (RegularQuotientCone.Modules (powerRing R t m))]

/-- The component of a derived comparison on a strict model, transported using the
same Roos identifications and the whole-tower coefficient counit.
Source: Bhatt--Scholze 3.5.5, comparison a
(blueprint: def-sp-perfect-reduction-roos-comparison-data). -/
def modelMap {m : ℕ}
    (d : DerivedChangeOfRingsCochainModel (powerProjection R t m))
    (cR : RoosModel (RegularQuotientCone.Modules R))
    (cA : RoosModel (RegularQuotientCone.Modules (powerRing R t m)))
    (e : TowerExtension d.E) (θ : cR.F ⋙ d.T ≅ e.F ⋙ cA.F)
    (P : CochainComplex (ℕᵒᵖ ⥤ RegularQuotientCone.Modules R) ℤ) :
    d.T.obj (DerivedCategory.Q.obj (roosF.obj P)) ⟶
      DerivedCategory.Q.obj (roosF.obj ((roosTowerAction d.E).obj P)) :=
  d.T.map (cR.κ.hom.app P) ≫ θ.hom.app (DerivedCategory.Q.obj P) ≫
    cA.F.map (e.ε.app P) ≫ cA.κ.inv.app ((roosTowerAction d.E).obj P)

/-- The maps underlying the normalized perfect-reduction comparison.
Source: Bhatt--Scholze 3.5.5, comparison a
(blueprint: def-sp-perfect-reduction-roos-comparison-data). -/
structure ComparisonData
    (d : ∀ m, DerivedChangeOfRingsCochainModel (powerProjection R t m))
    (cR : RoosModel (RegularQuotientCone.Modules R))
    (cA : ∀ m, RoosModel (RegularQuotientCone.Modules (powerRing R t m))) where
  extension : ∀ m, TowerExtension (d m).E
  θ : ∀ m, cR.F ⋙ (d m).T ≅ (extension m).F ⋙ (cA m).F
  δ : ∀ m P, ((total R).obj (principalKoszul R t m)).obj (roosF.obj P) ≅
    roosF.obj (tensorTower R (principalKoszul R t m) P)
  ρ : ∀ m, 𝟭 (CochainComplex (RegularQuotientCone.Modules R) ℤ) ⟶
    (d m).E.mapHomologicalComplex (.up ℤ) ⋙
      (restriction (powerProjection R t m)).mapHomologicalComplex (.up ℤ)
  α : ∀ m, (total R).obj (principalKoszul R t m) ⟶
    (d m).E.mapHomologicalComplex (.up ℤ) ⋙
      (restriction (powerProjection R t m)).mapHomologicalComplex (.up ℤ)
  V : ∀ m, DerivedCategory (RegularQuotientCone.Modules (powerRing R t m)) ⥤
    DerivedCategory (RegularQuotientCone.Modules R)
  v : ∀ m, DerivedCategory.Q ⋙ V m ≅
    (restriction (powerProjection R t m)).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q

/-- The `finite_free` condition of the fixed perfect-reduction comparison.
Source: Bhatt--Scholze 3.5.5 and 3.1.11
(blueprint: def-sp-perfect-reduction-roos-comparison-data). -/
@[irreducible] def ComparisonData.finite_free
    (d : ∀ m, DerivedChangeOfRingsCochainModel (powerProjection R t m))
    (cR : RoosModel (RegularQuotientCone.Modules R))
    (cA : ∀ m, RoosModel (RegularQuotientCone.Modules (powerRing R t m)))
    (b : ComparisonData R t d cR cA) : Prop :=
  ∀ m P (Q : CochainComplex (RegularQuotientCone.Modules R) ℤ)
    (q : Q ⟶ roosF.obj P),
    CochainComplex.IsKFlatIndependentCoefficients (R := R) Q → QuasiIso q →
    ∀ (bQ : DerivedCategory.Q.obj
        (((total R).obj (principalKoszul R t m)).obj Q) ≅
      DerivedCategory.Q.obj
        (((restriction (powerProjection R t m)).mapHomologicalComplex (.up ℤ)).obj
          (((d m).E.mapHomologicalComplex (.up ℤ)).obj Q))),
    bQ.hom = DerivedCategory.Q.map ((b.α m).app Q) →
    (b.V m).map ((d m).T.map (DerivedCategory.Q.map q) ≫
      modelMap R t (d m) cR (cA m) (b.extension m) (b.θ m) P) ≫
      (b.v m).hom.app (roosF.obj ((roosTowerAction (d m).E).obj P)) ≫
      DerivedCategory.Q.map (roosAdditiveComparison
        (restriction (powerProjection R t m)) ((roosTowerAction (d m).E).obj P)) =
    (b.V m).map ((d m).ε.app Q) ≫
      (b.v m).hom.app (((d m).E.mapHomologicalComplex (.up ℤ)).obj Q) ≫
      bQ.inv ≫
      DerivedCategory.Q.map (((total R).obj (principalKoszul R t m)).map q) ≫
      DerivedCategory.Q.map (b.δ m P).hom ≫
      DerivedCategory.Q.map (roosF.map
        (koszulTowerComplexMap R (Functor.whiskerLeft P.asFunctor (b.α m))))

end CategoryTheory.PerfectReductionRoos
