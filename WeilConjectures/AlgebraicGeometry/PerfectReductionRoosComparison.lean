/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.PerfectReductionRoosData
import all WeilConjectures.CategoryTheory.CofinalRoosRestriction
import all WeilConjectures.CategoryTheory.RoosComparisonHorizontalCoherenceSupplement
import WeilConjectures.CategoryTheory.RoosCohomologicalAmplitude
import WeilConjectures.AlgebraicGeometry.PerfectReductionDerivedComparison
import WeilConjectures.AlgebraicGeometry.PerfectReductionTowerExtension

/-! # Perfect reduction and the strict Roos limit

Source: Bhatt--Scholze, The pro-etale topology for schemes, Lemma 3.5.5 (comparison a)
and Proposition 3.1.11 (blueprint: lem-sp-perfect-reduction-roos-comparison).

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

variable {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
  {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasSheafify J AddCommGrpCat.{r}]
  [HasSheafify J CommRingCat.{r}]
  (R : Sheaf J CommRingCat.{r})
  (t : (unit (derivedChangeRingIndependentCoefficients J R)).sections)


variable [HasDerivedCategory.{wR} (RegularQuotientCone.Modules R)]
  [HasDerivedCategory.{wR} (ℕᵒᵖ ⥤ RegularQuotientCone.Modules R)]
  [∀ m, HasDerivedCategory.{wA} (RegularQuotientCone.Modules (powerRing R t m))]
  [∀ m, HasDerivedCategory.{wA} (ℕᵒᵖ ⥤ RegularQuotientCone.Modules (powerRing R t m))]
  [HasCountableProducts (RegularQuotientCone.Modules R)]
  [∀ m, HasCountableProducts (RegularQuotientCone.Modules (powerRing R t m))]


private theorem tail_block
    {A : Type a} [Category.{b} A] [Abelian A] [HasCountableProducts A]
    (P : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (N : ℕ) :
    CofinalRoos.block P (tailEmbedding N) = CofinalRoos.selection P (tailEmbedding N) := by
  apply Pi.hom_ext
  intro n
  simp only [CofinalRoos.block, CofinalRoos.selection, Pi.lift_π]
  have h : tailEmbedding N (n + 1) - tailEmbedding N n = 1 := by
    change n + 1 + N - (n + N) = 1
    omega
  rw [h]
  simp

private noncomputable def tailMap
    {A : Type a} [Category.{b} A] [Abelian A] [HasCountableProducts A]
    (P : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (N : ℕ) :
    roosF.obj P ⟶ roosF.obj ((CofinalRoos.restriction A (tailEmbedding N)).obj P) :=
  CofinalRoos.rho P (tailEmbedding N)

private theorem tailMap_coord
    {A : Type a} [Category.{b} A] [Abelian A] [HasCountableProducts A]
    (P : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (N : ℕ) (i : ℤ) :
    (tailMap P N).f (i + 1) ≫
        (roosχ ((CofinalRoos.restriction A (tailEmbedding N)).obj P) i).hom =
      (roosχ P i).hom ≫ biprod.map
        ((CofinalRoos.selection P (tailEmbedding N)).f i)
        ((CofinalRoos.selection P (tailEmbedding N)).f (i + 1)) := by
  exact (CofinalRoos.rho_coord P (tailEmbedding N) i).trans
    (by rw [tail_block])

private theorem tailMap_quasiIso
    {A : Type a} [Category.{b} A] [Abelian A] [HasCountableProducts A]
    (P : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (N : ℕ) : QuasiIso (tailMap P N) :=
  CofinalRoos.rho_quasiIso P (tailEmbedding N)

private theorem tailMap_eval
    {A : Type a} [Category.{b} A] [Abelian A] [HasCountableProducts A]
    (P : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (N n : ℕ) :
    tailMap P N ≫
        roosEval ((CofinalRoos.restriction A (tailEmbedding N)).obj P) n =
      roosEval P (n + N) := by
  ext k : 1
  obtain ⟨i, rfl⟩ : ∃ i : ℤ, k = i + 1 := ⟨k - 1, by omega⟩
  simp only [HomologicalComplex.comp_f, roosEval_f,
    reassoc_of% tailMap_coord, biprod.map_snd_assoc]
  have h := congrArg (fun f ↦ f.f (i + 1))
    (Pi.lift_π (fun n ↦ Pi.π (fun k : ℕ ↦ P.asFunctor.obj (op k))
      (tailEmbedding N n)) n)
  simp only [HomologicalComplex.comp_f] at h
  exact congrArg (fun z ↦ (roosχ P i).hom ≫ biprod.snd ≫ z) h

private theorem additiveComparison_eval
    {A : Type a} [Category.{b} A] [Abelian A] [HasCountableProducts A]
    {B : Type u} [Category.{v} B] [Abelian B] [HasCountableProducts B]
    (E : A ⥤ B) [E.Additive] (P : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (n : ℕ) :
    roosAdditiveComparison E P ≫ roosEval ((roosTowerAction E).obj P) n =
      (E.mapHomologicalComplex (.up ℤ)).map (roosEval P n) := by
  ext k : 1
  obtain ⟨i, rfl⟩ : ∃ i : ℤ, k = i + 1 := ⟨k - 1, by omega⟩
  simp only [HomologicalComplex.comp_f, roosEval_f,
    Functor.mapHomologicalComplex_map_f]
  rw [reassoc_of% roosAdditiveComparison_coordinates E P i]
  simp only [biprod.map_snd_assoc, Functor.biprodComparison_snd_assoc]
  have h := congrArg (fun f ↦ f.f (i + 1))
    (piComparison_comp_π (E.mapHomologicalComplex (.up ℤ))
      (fun k : ℕ ↦ P.asFunctor.obj (op k)) n)
  simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f] at h
  simpa only [roosProductComparison, roosTowerAction, HomologicalComplex.asFunctor,
    Functor.mapHomologicalComplex,
    Functor.whiskeringRight, Functor.comp_obj, Functor.whiskerRight_app,
    Functor.map_comp, Category.assoc] using
    congrArg (fun z ↦ E.map (roosχ P i).hom ≫ E.map biprod.snd ≫ z) h

private theorem productDegree_ext
    {A : Type a} [Category.{b} A] [Abelian A] [HasCountableProducts A]
    (K : ℕ → CochainComplex A ℤ) (i : ℤ) {Z : A}
    (f g : Z ⟶ (∏ᶜ K).X i)
    (h : ∀ n, f ≫ (Pi.π K n).f i = g ≫ (Pi.π K n).f i) : f = g := by
  apply (cancel_mono (piComparison (HomologicalComplex.eval A (.up ℤ) i) K)).mp
  apply Pi.hom_ext
  intro n
  simp only [Category.assoc, piComparison_comp_π]
  exact h n

private theorem tailMap_fst
    {A : Type a} [Category.{b} A] [Abelian A] [HasCountableProducts A]
    (P : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (N n : ℕ) (i : ℤ) :
    (tailMap P N).f (i + 1) ≫
        (roosχ ((CofinalRoos.restriction A (tailEmbedding N)).obj P) i).hom ≫
        biprod.fst ≫ (Pi.π (fun k : ℕ ↦
          ((CofinalRoos.restriction A (tailEmbedding N)).obj P).asFunctor.obj (op k)) n).f i =
      (roosχ P i).hom ≫ biprod.fst ≫
        (Pi.π (fun k : ℕ ↦ P.asFunctor.obj (op k)) (n + N)).f i := by
  rw [reassoc_of% tailMap_coord]
  simp only [biprod.map_fst_assoc]
  have h := congrArg (fun f ↦ f.f i)
    (Pi.lift_π (fun n ↦ Pi.π (fun k : ℕ ↦ P.asFunctor.obj (op k))
      (tailEmbedding N n)) n)
  simp only [HomologicalComplex.comp_f] at h
  exact congrArg (fun z ↦ (roosχ P i).hom ≫ biprod.fst ≫ z) h

private theorem tailMap_snd
    {A : Type a} [Category.{b} A] [Abelian A] [HasCountableProducts A]
    (P : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (N n : ℕ) (i : ℤ) :
    (tailMap P N).f (i + 1) ≫
        (roosχ ((CofinalRoos.restriction A (tailEmbedding N)).obj P) i).hom ≫
        biprod.snd ≫ (Pi.π (fun k : ℕ ↦
          ((CofinalRoos.restriction A (tailEmbedding N)).obj P).asFunctor.obj (op k)) n).f
            (i + 1) =
      (roosχ P i).hom ≫ biprod.snd ≫
        (Pi.π (fun k : ℕ ↦ P.asFunctor.obj (op k)) (n + N)).f (i + 1) := by
  have h := congrArg (fun f ↦ f.f (i + 1)) (tailMap_eval P N n)
  simpa only [HomologicalComplex.comp_f, roosEval_f, Category.assoc] using h

private theorem additiveComparison_fst
    {A : Type a} [Category.{b} A] [Abelian A] [HasCountableProducts A]
    {B : Type u} [Category.{v} B] [Abelian B] [HasCountableProducts B]
    (E : A ⥤ B) [E.Additive] (P : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (n : ℕ) (i : ℤ) :
    (roosAdditiveComparison E P).f (i + 1) ≫
        (roosχ ((roosTowerAction E).obj P) i).hom ≫ biprod.fst ≫
        (Pi.π (fun k : ℕ ↦ ((roosTowerAction E).obj P).asFunctor.obj (op k)) n).f i =
      E.map ((roosχ P i).hom ≫ biprod.fst ≫
        (Pi.π (fun k : ℕ ↦ P.asFunctor.obj (op k)) n).f i) := by
  rw [reassoc_of% CategoryTheory.comparison_fst E P i]
  have h := congrArg (fun f ↦ f.f i)
    (piComparison_comp_π (E.mapHomologicalComplex (.up ℤ))
      (fun k : ℕ ↦ P.asFunctor.obj (op k)) n)
  simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f] at h
  simpa only [roosProductComparison, roosTowerAction, HomologicalComplex.asFunctor,
    Functor.mapHomologicalComplex,
    Functor.whiskeringRight, Functor.comp_obj, Functor.whiskerRight_app,
    Functor.map_comp, Category.assoc] using
    congrArg (fun z ↦ E.map ((roosχ P i).hom ≫ biprod.fst) ≫ z) h

private theorem additiveComparison_snd
    {A : Type a} [Category.{b} A] [Abelian A] [HasCountableProducts A]
    {B : Type u} [Category.{v} B] [Abelian B] [HasCountableProducts B]
    (E : A ⥤ B) [E.Additive] (P : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (n : ℕ) (i : ℤ) :
    (roosAdditiveComparison E P).f (i + 1) ≫
        (roosχ ((roosTowerAction E).obj P) i).hom ≫ biprod.snd ≫
        (Pi.π (fun k : ℕ ↦ ((roosTowerAction E).obj P).asFunctor.obj (op k)) n).f (i + 1) =
      E.map ((roosχ P i).hom ≫ biprod.snd ≫
        (Pi.π (fun k : ℕ ↦ P.asFunctor.obj (op k)) n).f (i + 1)) := by
  have h := congrArg (fun f ↦ f.f (i + 1)) (additiveComparison_eval E P n)
  simpa only [HomologicalComplex.comp_f, roosEval_f,
    Functor.mapHomologicalComplex_map_f, Category.assoc] using h

private theorem tailMap_comparison
    {A : Type a} [Category.{b} A] [Abelian A] [HasCountableProducts A]
    {B : Type u} [Category.{v} B] [Abelian B] [HasCountableProducts B]
    (E : A ⥤ B) [E.Additive] (P : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (N : ℕ) :
    (E.mapHomologicalComplex (.up ℤ)).map (tailMap P N) ≫
        roosAdditiveComparison E ((CofinalRoos.restriction A (tailEmbedding N)).obj P) =
      roosAdditiveComparison E P ≫ tailMap ((roosTowerAction E).obj P) N := by
  ext k : 1
  obtain ⟨i, rfl⟩ : ∃ i : ℤ, k = i + 1 := ⟨k - 1, by omega⟩
  apply (cancel_mono
    (roosχ ((roosTowerAction E).obj
      ((CofinalRoos.restriction A (tailEmbedding N)).obj P)) i).hom).mp
  simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
    Category.assoc]
  apply biprod.hom_ext
  · apply productDegree_ext
    intro n
    let P' := (CofinalRoos.restriction A (tailEmbedding N)).obj P
    let EP := (roosTowerAction E).obj P
    have hl := additiveComparison_fst E P' n i
    have hr := tailMap_fst EP N n i
    have hs := tailMap_fst P N n i
    have ht := additiveComparison_fst E P (n + N) i
    calc
      _ = E.map ((tailMap P N).f (i + 1)) ≫ E.map
          ((roosχ P' i).hom ≫ biprod.fst ≫
            (Pi.π (fun k : ℕ ↦ P'.asFunctor.obj (op k)) n).f i) := by
        simpa only [Category.assoc] using
          congrArg (fun z ↦ E.map ((tailMap P N).f (i + 1)) ≫ z) hl
      _ = E.map ((roosχ P i).hom ≫ biprod.fst ≫
          (Pi.π (fun k : ℕ ↦ P.asFunctor.obj (op k)) (n + N)).f i) := by
        rw [← E.map_comp]
        exact congrArg E.map hs
      _ = (roosAdditiveComparison E P).f (i + 1) ≫
          (roosχ EP i).hom ≫ biprod.fst ≫
            (Pi.π (fun k : ℕ ↦ EP.asFunctor.obj (op k)) (n + N)).f i := ht.symm
      _ = _ := by
        simpa only [EP, CofinalRoos.restriction, roosTowerAction,
          HomologicalComplex.asFunctor, Functor.mapHomologicalComplex,
          Functor.whiskeringLeft, Functor.whiskeringRight, Functor.comp_obj,
          Functor.comp_map, Functor.whiskerRight, Functor.whiskerLeft,
          Functor.comp, Category.assoc] using
          congrArg (fun z ↦ (roosAdditiveComparison E P).f (i + 1) ≫ z) hr.symm
  · apply productDegree_ext
    intro n
    let P' := (CofinalRoos.restriction A (tailEmbedding N)).obj P
    let EP := (roosTowerAction E).obj P
    have hl := additiveComparison_snd E P' n i
    have hr := tailMap_snd EP N n i
    have hs := tailMap_snd P N n i
    have ht := additiveComparison_snd E P (n + N) i
    calc
      _ = E.map ((tailMap P N).f (i + 1)) ≫ E.map
          ((roosχ P' i).hom ≫ biprod.snd ≫
            (Pi.π (fun k : ℕ ↦ P'.asFunctor.obj (op k)) n).f (i + 1)) := by
        simpa only [Category.assoc] using
          congrArg (fun z ↦ E.map ((tailMap P N).f (i + 1)) ≫ z) hl
      _ = E.map ((roosχ P i).hom ≫ biprod.snd ≫
          (Pi.π (fun k : ℕ ↦ P.asFunctor.obj (op k)) (n + N)).f (i + 1)) := by
        rw [← E.map_comp]
        exact congrArg E.map hs
      _ = (roosAdditiveComparison E P).f (i + 1) ≫
          (roosχ EP i).hom ≫ biprod.snd ≫
            (Pi.π (fun k : ℕ ↦ EP.asFunctor.obj (op k)) (n + N)).f (i + 1) := ht.symm
      _ = _ := by
        simpa only [EP, CofinalRoos.restriction, roosTowerAction,
          HomologicalComplex.asFunctor, Functor.mapHomologicalComplex,
          Functor.whiskeringLeft, Functor.whiskeringRight, Functor.comp_obj,
          Functor.comp_map, Functor.whiskerRight, Functor.whiskerLeft,
          Functor.comp, Category.assoc] using
          congrArg (fun z ↦ (roosAdditiveComparison E P).f (i + 1) ≫ z) hr.symm

private theorem tails_of_normalization
    (d : ∀ m, DerivedChangeOfRingsCochainModel (powerProjection R t m))
    (cR : RoosModel (RegularQuotientCone.Modules R))
    (cA : ∀ m, RoosModel (RegularQuotientCone.Modules (powerRing R t m)))
    (b : ComparisonData R t d cR cA)
    (h : ComparisonData.normalization R t d cR cA b) :
    ComparisonData.tails R t d cR cA b := by
  unfold ComparisonData.normalization at h
  unfold ComparisonData.tails
  intro m P N
  refine ⟨tailMap P N, tailMap ((roosTowerAction (d m).E).obj P) N,
    tailMap_quasiIso P N, tailMap_quasiIso _ N, tailMap_coord P N,
    tailMap_coord _ N, tailMap_eval P N, ?_⟩
  rw [h, h]
  have hnat := (d m).ε.naturality (tailMap P N)
  dsimp only [Functor.comp_map] at hnat
  rw [← Category.assoc, hnat, Category.assoc,
    ← DerivedCategory.Q.map_comp, tailMap_comparison]
  simp only [DerivedCategory.Q.map_comp, Category.assoc]

private theorem projections_of_normalization
    (d : ∀ m, DerivedChangeOfRingsCochainModel (powerProjection R t m))
    (cR : RoosModel (RegularQuotientCone.Modules R))
    (cA : ∀ m, RoosModel (RegularQuotientCone.Modules (powerRing R t m)))
    (b : ComparisonData R t d cR cA)
    (h : ComparisonData.normalization R t d cR cA b) :
    ComparisonData.projections R t d cR cA b := by
  unfold ComparisonData.normalization at h
  unfold ComparisonData.projections
  intro m P n
  rw [h m P, Category.assoc, ← DerivedCategory.Q.map_comp, additiveComparison_eval]
  exact ((d m).ε.naturality (roosEval P n)).symm

set_option maxHeartbeats 1000000 in
-- Normalizing the tensor/derived composites traverses large sheaf definitions.
private theorem finiteFree_of_normalization
    (d : ∀ m, DerivedChangeOfRingsCochainModel (powerProjection R t m))
    (cR : RoosModel (RegularQuotientCone.Modules R))
    (cA : ∀ m, RoosModel (RegularQuotientCone.Modules (powerRing R t m)))
    (b : ComparisonData R t d cR cA)
    (hn : ComparisonData.normalization R t d cR cA b)
    (hsq : ∀ m P,
      ((b.α m).app (roosF.obj P)) ≫
        ((restriction (powerProjection R t m)).mapHomologicalComplex (.up ℤ)).map
          (roosAdditiveComparison (d m).E P) ≫
        roosAdditiveComparison (restriction (powerProjection R t m))
          ((roosTowerAction (d m).E).obj P) =
      (b.δ m P).hom ≫ roosF.map
        (koszulTowerComplexMap R (Functor.whiskerLeft P.asFunctor (b.α m)))) :
    ComparisonData.finite_free R t d cR cA b := by
  unfold ComparisonData.normalization at hn
  unfold ComparisonData.finite_free
  intro m P Q q _hQ _hq bQ hbQ
  let E := (d m).E.mapHomologicalComplex (.up ℤ)
  let U := (restriction (powerProjection R t m)).mapHomologicalComplex (.up ℤ)
  let F := (total R).obj (principalKoszul R t m)
  let f := roosAdditiveComparison (d m).E P
  let g := roosAdditiveComparison (restriction (powerProjection R t m))
    ((roosTowerAction (d m).E).obj P)
  let s := roosF.map
    (koszulTowerComplexMap R (Functor.whiskerLeft P.asFunctor (b.α m)))
  let j := U.map (E.map q ≫ f) ≫ g
  let k := F.map q ≫ (b.δ m P).hom ≫ s
  have hs : (b.α m).app Q ≫ j = k := by
    dsimp only [j, k]
    rw [Functor.map_comp]
    have ha := (b.α m).naturality q
    change F.map q ≫ (b.α m).app (roosF.obj P) =
      (b.α m).app Q ≫ U.map (E.map q) at ha
    rw [← Category.assoc, ← Category.assoc, ← ha, Category.assoc, Category.assoc]
    exact congrArg (fun z ↦ F.map q ≫ z) (hsq m P)
  have hj : DerivedCategory.Q.map j = bQ.inv ≫ DerivedCategory.Q.map k := by
    apply (cancel_epi bQ.hom).mp
    rw [← Category.assoc, bQ.hom_inv_id, Category.id_comp, hbQ,
      ← DerivedCategory.Q.map_comp, hs]
  have he : (d m).T.map (DerivedCategory.Q.map q) ≫
      modelMap R t (d m) cR (cA m) (b.extension m) (b.θ m) P =
      (d m).ε.app Q ≫ DerivedCategory.Q.map (E.map q ≫ f) := by
    have hnat := (d m).ε.naturality q
    dsimp only [Functor.comp_map] at hnat
    rw [hn m P, ← Category.assoc, hnat,
      Category.assoc, ← DerivedCategory.Q.map_comp]
  rw [he, Functor.map_comp, Category.assoc]
  have hv := (b.v m).hom.naturality (E.map q ≫ f)
  change (b.V m).map (DerivedCategory.Q.map (E.map q ≫ f)) ≫
      (b.v m).hom.app _ =
    (b.v m).hom.app _ ≫ DerivedCategory.Q.map (U.map (E.map q ≫ f)) at hv
  rw [reassoc_of% hv, ← DerivedCategory.Q.map_comp, hj]
  simp only [k, DerivedCategory.Q.map_comp]
  rfl

/-- Perfect regular-quotient reduction commutes with the total derived limit of any
strict tower. All comparison maps and their normalizations are packaged in `Comparison`.
There is no cohomological boundedness or surjectivity hypothesis.

Source: Bhatt--Scholze, The pro-etale topology for schemes, Lemma 3.5.5, comparison a,
and Proposition 3.1.11 (blueprint: lem-sp-perfect-reduction-roos-comparison).

Proof:
1. Use the normalized ordinary coefficient adjunction to obtain units rho and exact
restriction localizations V,v. The strict Koszul calculation supplies delta, alpha,
the two coordinate signs, alpha's unit/zero identities and its strict Roos square.
2. Resolve constant-coefficient towers simultaneously by levelwise K-flat flat-term
complexes. The resolving-class derived-functor construction gives a universal tower
extension computing on every levelwise K-flat complex. The derived adjunct comparison
supplies theta with normalization and quotient changes for those chosen extensions.
3. The additive Roos comparison followed by evaluation at n is ordinary extension
of the original evaluation. The normalized model equation and counit naturality
therefore give the projection identity, for every strict tower complex.
4. Given q:Q→Roos(P), alpha naturality and its strict Roos square identify the two
ordinary maps after alpha_Q. Cancel the specified localized augmentation isomorphism
bQ. Naturality of the coefficient counit and of v gives the exact finite-free equation.
5. Apply generic cofinal strict Roos restriction to n↦n+N. Every block has length
one, so both coordinates select the required original coordinates, the map is a
quasi-isomorphism and evaluation retains leg n+N. Check the additive comparison square
on both product coordinates. Normalization and counit naturality give the tail square.
6. Exact products and the distinguished mapping-cocone triangle give cohomological
amplitude [a,b+1]. Package these proofs with the supplied ordinary and derived clauses. -/
theorem nonempty_comparison
    [HasExactLimitsOfShape (Discrete ℕ) (RegularQuotientCone.Modules R)]
    (_ht : Mono (globalSectionMultiplication R t))
    (d : ∀ m, DerivedChangeOfRingsCochainModel (powerProjection R t m))
    (cR : RoosModel (RegularQuotientCone.Modules R))
    (cA : ∀ m, RoosModel (RegularQuotientCone.Modules (powerRing R t m))) :
    Nonempty (Comparison R t d cR cA) := by
  obtain ⟨c⟩ := nonempty_coefficientUnits R t d
  obtain ⟨k⟩ := nonempty_koszulComparison R t _ht d c
  choose e he using (fun m ↦ exists_towerExtension R t m (d m))
  obtain ⟨θ, hn, hq⟩ := exists_derivedComparison R t _ht d c k cR cA e he
  let b := k.withDerived R t cR cA e θ
  refine ⟨{
    data := b
    extension_computes := by
      unfold ComparisonData.extension_computes
      exact he
    normalization := hn
    projections := projections_of_normalization R t d cR cA b hn
    δ_shifted := ?_
    δ_unshifted := ?_
    ρ_sections := ?_
    α_zero := ?_
    α_unit := ?_
    α_quasiIso := ?_
    finite_free := finiteFree_of_normalization R t d cR cA b hn k.augmentation_square
    koszul_changes := ?_
    quotient_changes := hq
    tails := tails_of_normalization R t d cR cA b hn
    amplitude := ?_ }⟩
  · unfold ComparisonData.δ_shifted
    exact k.δ_shifted
  · unfold ComparisonData.δ_unshifted
    exact k.δ_unshifted
  · unfold ComparisonData.ρ_sections
    exact c.ρ_sections
  · unfold ComparisonData.α_zero
    exact k.α_zero
  · unfold ComparisonData.α_unit
    exact k.α_unit
  · unfold ComparisonData.α_quasiIso
    exact k.α_quasiIso
  · unfold ComparisonData.koszul_changes
    exact k.koszul_changes
  · unfold ComparisonData.amplitude
    intro P a b hP i hi
    exact roosCohomologicalAmplitude P a b hP i hi

end CategoryTheory.PerfectReductionRoos
