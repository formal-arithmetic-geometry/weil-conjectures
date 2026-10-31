/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.OrdinaryDerivedChangeOfRings
public import WeilConjectures.Algebra.Homology.RegularQuotientConeBasic
public import WeilConjectures.Algebra.Homology.PrincipalKoszulQuotientTowersSupplement
public import WeilConjectures.Algebra.Homology.TotalTensorHomotopyConeSigns
public import WeilConjectures.Algebra.Category.Ring.Sheaf.PrincipalPowerQuotients
public import WeilConjectures.CategoryTheory.RoosComparisonHorizontalCoherenceSupplement
public import WeilConjectures.CategoryTheory.CofinalRoosRestriction
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

/-- Change the finite coefficient complex of a strict tensor tower by its actual map.
Source: Bhatt--Scholze 3.5.5, quotient-change calculation
(blueprint: def-sp-perfect-reduction-roos-comparison-data). -/
def tensorTowerMap {K K' : CochainComplex (RegularQuotientCone.Modules R) ℤ}
    (f : K ⟶ K') (P : CochainComplex (ℕᵒᵖ ⥤ RegularQuotientCone.Modules R) ℤ) :
    tensorTower R K P ⟶ tensorTower R K' P :=
  koszulTowerComplexMap R (Functor.whiskerLeft P.asFunctor ((total R).map f))

/-- The degree-zero Koszul inclusion of the unit, with the specified cone normalization.
Source: Bhatt--Scholze 3.5.5, two-term resolution
(blueprint: def-sp-perfect-reduction-roos-comparison-data). -/
def koszulZeroInclusion (m : ℕ) :
    unit (derivedChangeRingIndependentCoefficients J R) ⟶ (principalKoszul R t m).X 0 :=
  (HomologicalComplex.singleObjXSelf (.up ℤ) 0
    (unit (derivedChangeRingIndependentCoefficients J R))).inv ≫
      (CochainComplex.mappingCone.inr (principalKoszulScalarComplex R t m)).f 0

/-- The tail starting at predecessor index `N`; it retains the original indices.
Source: Bhatt--Scholze 3.1.11 and 3.5.5
(blueprint: def-sp-perfect-reduction-roos-comparison-data). -/
def tailEmbedding (N : ℕ) : ℕ ↪o ℕ where
  toFun n := n + N
  inj' := fun {_ _} h ↦ Nat.add_right_cancel h
  map_rel_iff' := Nat.add_le_add_iff_right

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

/-- The ordinary quotient-change map on complexes, with the composite target exposed.
Source: Bhatt--Scholze 3.5.5, quotient-change calculation
(blueprint: def-sp-perfect-reduction-roos-comparison-data). -/
@[irreducible] def coefficientComplexMap {l m : ℕ}
    (dm : DerivedChangeOfRingsCochainModel (powerProjection R t m))
    (dl : DerivedChangeOfRingsCochainModel (powerProjection R t l))
    (f : powerRing R t m ⟶ powerRing R t l)
    (qE : dm.E ⟶ dl.E ⋙ restriction f)
    (Z : CochainComplex (RegularQuotientCone.Modules R) ℤ) :
    (dm.E.mapHomologicalComplex (.up ℤ)).obj Z ⟶
      ((restriction f).mapHomologicalComplex (.up ℤ)).obj
        ((dl.E.mapHomologicalComplex (.up ℤ)).obj Z) where
  f i := qE.app (Z.X i)
  comm' i j _ := (qE.naturality (Z.d i j)).symm

/-- The ordinary quotient-change map on entire strict towers. Both the strict
transitions and the complex differentials use the same ordinary natural transformation.
Source: Bhatt--Scholze 3.5.5, quotient-change calculation
(blueprint: def-sp-perfect-reduction-roos-comparison-data). -/
@[irreducible] def coefficientTowerMap {l m : ℕ}
    (dm : DerivedChangeOfRingsCochainModel (powerProjection R t m))
    (dl : DerivedChangeOfRingsCochainModel (powerProjection R t l))
    (f : powerRing R t m ⟶ powerRing R t l)
    (qE : dm.E ⟶ dl.E ⋙ restriction f)
    (P : CochainComplex (ℕᵒᵖ ⥤ RegularQuotientCone.Modules R) ℤ) :
    (roosTowerAction dm.E).obj P ⟶
      (roosTowerAction (restriction f)).obj ((roosTowerAction dl.E).obj P) where
  f i := { app := fun n ↦ qE.app ((P.X i).obj n)
           naturality := fun {_ _} g ↦ qE.naturality ((P.X i).map g) }
  comm' i j _ := NatTrans.ext (by
    funext n
    exact (qE.naturality ((P.d i j).app n)).symm)

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

/-- The `extension_computes` condition of the fixed perfect-reduction comparison.
Source: Bhatt--Scholze 3.5.5 and 3.1.11
(blueprint: def-sp-perfect-reduction-roos-comparison-data). -/
@[irreducible] def ComparisonData.extension_computes
    (d : ∀ m, DerivedChangeOfRingsCochainModel (powerProjection R t m))
    (cR : RoosModel (RegularQuotientCone.Modules R))
    (cA : ∀ m, RoosModel (RegularQuotientCone.Modules (powerRing R t m)))
    (b : ComparisonData R t d cR cA) : Prop :=
  ∀ m P,
    (∀ n, CochainComplex.IsKFlatIndependentCoefficients (R := R)
      (P.asFunctor.obj (op n))) → IsIso ((b.extension m).ε.app P)

/-- The `normalization` condition of the fixed perfect-reduction comparison.
Source: Bhatt--Scholze 3.5.5 and 3.1.11
(blueprint: def-sp-perfect-reduction-roos-comparison-data). -/
@[irreducible] def ComparisonData.normalization
    (d : ∀ m, DerivedChangeOfRingsCochainModel (powerProjection R t m))
    (cR : RoosModel (RegularQuotientCone.Modules R))
    (cA : ∀ m, RoosModel (RegularQuotientCone.Modules (powerRing R t m)))
    (b : ComparisonData R t d cR cA) : Prop :=
  ∀ m P,
    modelMap R t (d m) cR (cA m) (b.extension m) (b.θ m) P =
      (d m).ε.app (roosF.obj P) ≫
        DerivedCategory.Q.map (roosAdditiveComparison (d m).E P)

/-- The `projections` condition of the fixed perfect-reduction comparison.
Source: Bhatt--Scholze 3.5.5 and 3.1.11
(blueprint: def-sp-perfect-reduction-roos-comparison-data). -/
@[irreducible] def ComparisonData.projections
    (d : ∀ m, DerivedChangeOfRingsCochainModel (powerProjection R t m))
    (cR : RoosModel (RegularQuotientCone.Modules R))
    (cA : ∀ m, RoosModel (RegularQuotientCone.Modules (powerRing R t m)))
    (b : ComparisonData R t d cR cA) : Prop :=
  ∀ m P n,
    modelMap R t (d m) cR (cA m) (b.extension m) (b.θ m) P ≫
      DerivedCategory.Q.map (roosEval ((roosTowerAction (d m).E).obj P) n) =
        (d m).T.map (DerivedCategory.Q.map (roosEval P n)) ≫
          (d m).ε.app (P.asFunctor.obj (op n))

/-- The `δ_shifted` condition of the fixed perfect-reduction comparison.
Source: Bhatt--Scholze 3.5.5 and 3.1.11
(blueprint: def-sp-perfect-reduction-roos-comparison-data). -/
@[irreducible] def ComparisonData.δ_shifted
    (d : ∀ m, DerivedChangeOfRingsCochainModel (powerProjection R t m))
    (cR : RoosModel (RegularQuotientCone.Modules R))
    (cA : ∀ m, RoosModel (RegularQuotientCone.Modules (powerRing R t m)))
    (b : ComparisonData R t d cR cA) : Prop :=
  ∀ m P i p n (h : p + (i + 1) = n + 1) j,
    ι R (principalKoszul R t m) (roosF.obj P) p (i + 1) (n + 1) h ≫
      (b.δ m P).hom.f (n + 1) ≫
      (roosχ (tensorTower R (principalKoszul R t m) P) n).hom ≫ biprod.fst ≫
      (Pi.π (fun k : ℕ ↦ (tensorTower R (principalKoszul R t m) P).asFunctor.obj
        (op k)) j).f n =
      p.negOnePow • ((tensor R).obj ((principalKoszul R t m).X p)).map
        ((roosχ P i).hom ≫ biprod.fst ≫
          (Pi.π (fun k : ℕ ↦ P.asFunctor.obj (op k)) j).f i) ≫
        ι R (principalKoszul R t m) (P.asFunctor.obj (op j)) p i n (by omega)

/-- The `δ_unshifted` condition of the fixed perfect-reduction comparison.
Source: Bhatt--Scholze 3.5.5 and 3.1.11
(blueprint: def-sp-perfect-reduction-roos-comparison-data). -/
@[irreducible] def ComparisonData.δ_unshifted
    (d : ∀ m, DerivedChangeOfRingsCochainModel (powerProjection R t m))
    (cR : RoosModel (RegularQuotientCone.Modules R))
    (cA : ∀ m, RoosModel (RegularQuotientCone.Modules (powerRing R t m)))
    (b : ComparisonData R t d cR cA) : Prop :=
  ∀ m P i p n (h : p + (i + 1) = n + 1) j,
    ι R (principalKoszul R t m) (roosF.obj P) p (i + 1) (n + 1) h ≫
      (b.δ m P).hom.f (n + 1) ≫
      (roosχ (tensorTower R (principalKoszul R t m) P) n).hom ≫ biprod.snd ≫
      (Pi.π (fun k : ℕ ↦ (tensorTower R (principalKoszul R t m) P).asFunctor.obj
        (op k)) j).f (n + 1) =
      ((tensor R).obj ((principalKoszul R t m).X p)).map
        ((roosχ P i).hom ≫ biprod.snd ≫
          (Pi.π (fun k : ℕ ↦ P.asFunctor.obj (op k)) j).f (i + 1)) ≫
        ι R (principalKoszul R t m) (P.asFunctor.obj (op j)) p (i + 1) (n + 1) h

/-- The `ρ_sections` condition of the fixed perfect-reduction comparison.
Source: Bhatt--Scholze 3.5.5 and 3.1.11
(blueprint: def-sp-perfect-reduction-roos-comparison-data). -/
@[irreducible] def ComparisonData.ρ_sections
    (d : ∀ m, DerivedChangeOfRingsCochainModel (powerProjection R t m))
    (cR : RoosModel (RegularQuotientCone.Modules R))
    (cA : ∀ m, RoosModel (RegularQuotientCone.Modules (powerRing R t m)))
    (b : ComparisonData R t d cR cA) : Prop :=
  ∀ m Z i (U : Cᵒᵖ) (x : (Z.X i).val.obj U),
    (eqToHom ((d m).obj_eq (Z.X i))).val.app U ((((b.ρ m).app Z).f i).val.app U x) =
      (toSheafify J (changeOfRingsPresheaf (powerProjection R t m) (Z.X i)).presheaf).app U
        ((1 : (powerRing R t m).obj.obj U) ⊗ₜ[R.obj.obj U,
          ((powerProjection R t m).hom.app U).hom] x)

/-- The `α_zero` condition of the fixed perfect-reduction comparison.
Source: Bhatt--Scholze 3.5.5 and 3.1.11
(blueprint: def-sp-perfect-reduction-roos-comparison-data). -/
@[irreducible] def ComparisonData.α_zero
    (d : ∀ m, DerivedChangeOfRingsCochainModel (powerProjection R t m))
    (cR : RoosModel (RegularQuotientCone.Modules R))
    (cA : ∀ m, RoosModel (RegularQuotientCone.Modules (powerRing R t m)))
    (b : ComparisonData R t d cR cA) : Prop :=
  ∀ m Z i p n (h : p + i = n), p ≠ 0 →
    ι R (principalKoszul R t m) Z p i n h ≫ ((b.α m).app Z).f n = 0

/-- The `α_unit` condition of the fixed perfect-reduction comparison.
Source: Bhatt--Scholze 3.5.5 and 3.1.11
(blueprint: def-sp-perfect-reduction-roos-comparison-data). -/
@[irreducible] def ComparisonData.α_unit
    (d : ∀ m, DerivedChangeOfRingsCochainModel (powerProjection R t m))
    (cR : RoosModel (RegularQuotientCone.Modules R))
    (cA : ∀ m, RoosModel (RegularQuotientCone.Modules (powerRing R t m)))
    (b : ComparisonData R t d cR cA) : Prop :=
  ∀ m Z n,
    ((tensor R).map (koszulZeroInclusion R t m)).app (Z.X n) ≫
      ι R (principalKoszul R t m) Z 0 n n (zero_add n) ≫ ((b.α m).app Z).f n =
        ((SheafOfModules.monoidalCategory R).leftUnitor (Z.X n)).hom ≫
          ((b.ρ m).app Z).f n

/-- The `α_quasiIso` condition of the fixed perfect-reduction comparison.
Source: Bhatt--Scholze 3.5.5 and 3.1.11
(blueprint: def-sp-perfect-reduction-roos-comparison-data). -/
@[irreducible] def ComparisonData.α_quasiIso
    (d : ∀ m, DerivedChangeOfRingsCochainModel (powerProjection R t m))
    (cR : RoosModel (RegularQuotientCone.Modules R))
    (cA : ∀ m, RoosModel (RegularQuotientCone.Modules (powerRing R t m)))
    (b : ComparisonData R t d cR cA) : Prop :=
  ∀ m Z,
    CochainComplex.IsKFlatIndependentCoefficients (R := R) Z → QuasiIso ((b.α m).app Z)

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

/-- The `koszul_changes` condition of the fixed perfect-reduction comparison.
Source: Bhatt--Scholze 3.5.5 and 3.1.11
(blueprint: def-sp-perfect-reduction-roos-comparison-data). -/
@[irreducible] def ComparisonData.koszul_changes
    (d : ∀ m, DerivedChangeOfRingsCochainModel (powerProjection R t m))
    (cR : RoosModel (RegularQuotientCone.Modules R))
    (cA : ∀ m, RoosModel (RegularQuotientCone.Modules (powerRing R t m)))
    (b : ComparisonData R t d cR cA) : Prop :=
  ∀ l m (h : l ≤ m) P,
    ((total R).map
      ((principalKoszulTower R t).map (homOfLE h).op)).app (roosF.obj P) ≫ (b.δ l P).hom =
      (b.δ m P).hom ≫ roosF.map
        (tensorTowerMap R ((principalKoszulTower R t).map (homOfLE h).op) P)

set_option maxHeartbeats 1000000 in
-- The kernel checks several independent coefficient-category endpoints here.
/-- The `quotient_changes` condition of the fixed perfect-reduction comparison.
Source: Bhatt--Scholze 3.5.5 and 3.1.11
(blueprint: def-sp-perfect-reduction-roos-comparison-data). -/
@[irreducible] def ComparisonData.quotient_changes
    (d : ∀ m, DerivedChangeOfRingsCochainModel (powerProjection R t m))
    (cR : RoosModel (RegularQuotientCone.Modules R))
    (cA : ∀ m, RoosModel (RegularQuotientCone.Modules (powerRing R t m)))
    (b : ComparisonData R t d cR cA) : Prop :=
  ∀ l m, l ≤ m →
    ∃ (f : powerRing R t m ⟶ powerRing R t l)
      (qE : (d m).E ⟶ (d l).E ⋙ restriction f)
      (W : DerivedCategory (RegularQuotientCone.Modules (powerRing R t l)) ⥤
        DerivedCategory (RegularQuotientCone.Modules (powerRing R t m)))
      (w : DerivedCategory.Q ⋙ W ≅
        (restriction f).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
      (qD : (d m).T ⟶ (d l).T ⋙ W),
      powerProjection R t m ≫ f = powerProjection R t l ∧
      (∀ M (U : Cᵒᵖ) (a : (powerRing R t m).obj.obj U) (x : M.val.obj U),
        (qE.app M).val.app U
          ((eqToHom ((d m).obj_eq M).symm).val.app U
            ((toSheafify J (changeOfRingsPresheaf (powerProjection R t m) M).presheaf).app U
              (a ⊗ₜ[R.obj.obj U, ((powerProjection R t m).hom.app U).hom] x))) =
        (eqToHom ((d l).obj_eq M).symm).val.app U
          ((toSheafify J (changeOfRingsPresheaf (powerProjection R t l) M).presheaf).app U
            ((f.hom.app U a) ⊗ₜ[R.obj.obj U,
              ((powerProjection R t l).hom.app U).hom] x))) ∧
      (∀ Z, qD.app (DerivedCategory.Q.obj Z) ≫ W.map ((d l).ε.app Z) ≫
          w.hom.app (((d l).E.mapHomologicalComplex (.up ℤ)).obj Z) =
        (d m).ε.app Z ≫
          DerivedCategory.Q.map (coefficientComplexMap R t (d m) (d l) f qE Z)) ∧
      (∀ P,
        modelMap R t (d m) cR (cA m) (b.extension m) (b.θ m) P ≫
          DerivedCategory.Q.map (roosF.map (coefficientTowerMap R t (d m) (d l) f qE P)) =
        qD.app (DerivedCategory.Q.obj (roosF.obj P)) ≫
          W.map (modelMap R t (d l) cR (cA l) (b.extension l) (b.θ l) P) ≫
          w.hom.app (roosF.obj ((roosTowerAction (d l).E).obj P)) ≫
          DerivedCategory.Q.map (roosAdditiveComparison (restriction f)
            ((roosTowerAction (d l).E).obj P)))

/-- The `tails` condition of the fixed perfect-reduction comparison.
Source: Bhatt--Scholze 3.5.5 and 3.1.11
(blueprint: def-sp-perfect-reduction-roos-comparison-data). -/
@[irreducible] def ComparisonData.tails
    (d : ∀ m, DerivedChangeOfRingsCochainModel (powerProjection R t m))
    (cR : RoosModel (RegularQuotientCone.Modules R))
    (cA : ∀ m, RoosModel (RegularQuotientCone.Modules (powerRing R t m)))
    (b : ComparisonData R t d cR cA) : Prop :=
  ∀ m P N,
    ∃ (bR : roosF.obj P ⟶
        roosF.obj ((CofinalRoos.restriction _ (tailEmbedding N)).obj P))
      (bA : roosF.obj ((roosTowerAction (d m).E).obj P) ⟶
        roosF.obj ((roosTowerAction (d m).E).obj
          ((CofinalRoos.restriction _ (tailEmbedding N)).obj P))),
      QuasiIso bR ∧ QuasiIso bA ∧
      (∀ i, bR.f (i + 1) ≫
          (roosχ ((CofinalRoos.restriction _ (tailEmbedding N)).obj P) i).hom =
        (roosχ P i).hom ≫ biprod.map
          ((CofinalRoos.selection P (tailEmbedding N)).f i)
          ((CofinalRoos.selection P (tailEmbedding N)).f (i + 1))) ∧
      (∀ i, bA.f (i + 1) ≫
          (roosχ ((roosTowerAction (d m).E).obj
            ((CofinalRoos.restriction _ (tailEmbedding N)).obj P)) i).hom =
        (roosχ ((roosTowerAction (d m).E).obj P) i).hom ≫ biprod.map
          ((CofinalRoos.selection ((roosTowerAction (d m).E).obj P)
            (tailEmbedding N)).f i)
          ((CofinalRoos.selection ((roosTowerAction (d m).E).obj P)
            (tailEmbedding N)).f (i + 1))) ∧
      (∀ n, bR ≫ roosEval ((CofinalRoos.restriction _ (tailEmbedding N)).obj P) n =
        roosEval P (n + N)) ∧
      (d m).T.map (DerivedCategory.Q.map bR) ≫
          modelMap R t (d m) cR (cA m) (b.extension m) (b.θ m)
            ((CofinalRoos.restriction _ (tailEmbedding N)).obj P) =
        modelMap R t (d m) cR (cA m) (b.extension m) (b.θ m) P ≫ DerivedCategory.Q.map bA

/-- The `amplitude` condition of the fixed perfect-reduction comparison.
Source: Bhatt--Scholze 3.5.5 and 3.1.11
(blueprint: def-sp-perfect-reduction-roos-comparison-data). -/
@[irreducible] def ComparisonData.amplitude
    (d : ∀ m, DerivedChangeOfRingsCochainModel (powerProjection R t m))
    (cR : RoosModel (RegularQuotientCone.Modules R))
    (cA : ∀ m, RoosModel (RegularQuotientCone.Modules (powerRing R t m)))
    (_b : ComparisonData R t d cR cA) : Prop :=
  ∀ (P : CochainComplex (ℕᵒᵖ ⥤ RegularQuotientCone.Modules R) ℤ)
    (a b : ℤ),
    (∀ n i, i < a ∨ b < i →
      IsZero ((HomologicalComplex.homologyFunctor _ (.up ℤ) i).obj
        (P.asFunctor.obj (op n)))) →
    ∀ i, i < a ∨ b + 1 < i →
      IsZero ((HomologicalComplex.homologyFunctor _ (.up ℤ) i).obj (roosF.obj P))

/-- The normalized perfect-reduction comparison, including every coordinate equation.
Source: Bhatt--Scholze 3.5.5 and 3.1.11
(blueprint: def-sp-perfect-reduction-roos-comparison-data). -/
structure Comparison
    (d : ∀ m, DerivedChangeOfRingsCochainModel (powerProjection R t m))
    (cR : RoosModel (RegularQuotientCone.Modules R))
    (cA : ∀ m, RoosModel (RegularQuotientCone.Modules (powerRing R t m))) where
  data : ComparisonData R t d cR cA
  extension_computes : ComparisonData.extension_computes R t d cR cA data
  normalization : ComparisonData.normalization R t d cR cA data
  projections : ComparisonData.projections R t d cR cA data
  δ_shifted : ComparisonData.δ_shifted R t d cR cA data
  δ_unshifted : ComparisonData.δ_unshifted R t d cR cA data
  ρ_sections : ComparisonData.ρ_sections R t d cR cA data
  α_zero : ComparisonData.α_zero R t d cR cA data
  α_unit : ComparisonData.α_unit R t d cR cA data
  α_quasiIso : ComparisonData.α_quasiIso R t d cR cA data
  finite_free : ComparisonData.finite_free R t d cR cA data
  koszul_changes : ComparisonData.koszul_changes R t d cR cA data
  quotient_changes : ComparisonData.quotient_changes R t d cR cA data
  tails : ComparisonData.tails R t d cR cA data
  amplitude : ComparisonData.amplitude R t d cR cA data

end CategoryTheory.PerfectReductionRoos
