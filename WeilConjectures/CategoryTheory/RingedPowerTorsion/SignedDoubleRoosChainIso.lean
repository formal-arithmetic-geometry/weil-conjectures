/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.Algebra.Homology.BifunctorShift
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.CategoryTheory.PrincipalQuotientCompletion.PrincipalQuotientCompletionModel
public import WeilConjectures.Algebra.Homology.RegularQuotientCone.RegularQuotientConeBasic
public import WeilConjectures.Algebra.Homology.SixFunctors.OrdinaryDerivedChangeOfRings
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import all WeilConjectures.CategoryTheory.RoosConeCalculus.RoosConeCalculus

/-! Strict signed interchange of the two Roos directions.

Source: Bhatt--Scholze, Lemma 3.4.13; Stacks Tag 0941.
(blueprint: lem-sp-signed-double-roos-chain-iso)

The proof distributes the two mapping-cocone biproducts and the two countable
products, reindexes `(n,j)` to `(j,n)`, and inserts the Koszul sign in the
`(true,true)` component. The four coordinate calculations prove the chain
condition, and product extensionality proves the inverse and naturality laws.
The degreewise swap `transposeX`, its inverse identity `transposeX_square`, its
naturality `transposeX_natural` and the coordinate differential formulas
`doubleCoordinate_d00`, `coordinate_d_true` are proved below (private, reachable
by `import all`), together with the shifted-coordinate differential formulas
`c01_d`, `c10_d`, `c11_d` and their `XIsoOfEq` degree transports, from which the
chain condition of the swap follows.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open CochainComplex

namespace CategoryTheory.RingedPowerTorsion

universe u v r

variable {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
  {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [HasSheafify J AddCommGrpCat.{r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
  (R : Sheaf J CommRingCat.{r})

/- Coordinate calculus of the double Roos complex: extensionality, lifts, the
degreewise signed swap `transposeX` with its inverse identity and naturality,
and the coordinate formulas for the differential. -/
set_option hygiene false in
local notation "A" => ringedSiteModules.{r}
  (SheafOfModules.derivedChangeRingIndependentCoefficients J R)
set_option hygiene false in
local notation "Section" => (SheafOfModules.unit
  (SheafOfModules.derivedChangeRingIndependentCoefficients J R)).sections

omit [EssentiallySmall.{r} C] in
private theorem coordinate_ext (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (k : ℤ)
    {B : A} {f g : B ⟶ (roosF.obj X).X k}
    (h : ∀ b, f ≫ coordinate R X k b = g ≫ coordinate R X k b) : f = g := by
  change B ⟶ (mappingCocone (roosU X)).X k at f g
  have hi := CochainComplex.mappingCocone.id_X (roosU X) k (k - 1) (by omega)
  calc
    f = f ≫ 𝟙 _ := (Category.comp_id f).symm
    _ = g ≫ 𝟙 _ := by
      rw [← hi, Preadditive.comp_add, Preadditive.comp_add]
      simp only [← Category.assoc]
      rw [show f ≫ (CochainComplex.mappingCocone.fst (roosU X)).f k =
        g ≫ (CochainComplex.mappingCocone.fst (roosU X)).f k from h false]
      rw [show f ≫ (CochainComplex.mappingCocone.snd (roosU X)).v k (k - 1)
          (by omega) =
        g ≫ (CochainComplex.mappingCocone.snd (roosU X)).v k (k - 1)
          (by omega) from h true]
    _ = g := Category.comp_id g

omit [EssentiallySmall.{r} C] [HasSheafify J AddCommGrpCat]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}] in
private theorem product_degree_ext (K : ℕ → CochainComplex A ℤ) (k : ℤ)
    {B : A} {f g : B ⟶ (∏ᶜ K).X k}
    (h : ∀ n, f ≫ (Pi.π K n).f k = g ≫ (Pi.π K n).f k) : f = g := by
  apply (isLimitOfHasProductOfPreservesLimit
    (HomologicalComplex.eval A (.up ℤ) k) K).hom_ext
  rintro ⟨n⟩
  exact h n

private def product_degree_lift (K : ℕ → CochainComplex A ℤ) (k : ℤ)
    {B : A} (f : ∀ n, B ⟶ (K n).X k) : B ⟶ (∏ᶜ K).X k :=
  (isLimitOfHasProductOfPreservesLimit
    (HomologicalComplex.eval A (.up ℤ) k) K).lift (Fan.mk B f)

omit [EssentiallySmall.{r} C] [HasSheafify J AddCommGrpCat]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}] in
@[reassoc (attr := simp)]
private theorem product_degree_lift_π (K : ℕ → CochainComplex A ℤ) (k : ℤ)
    {B : A} (f : ∀ n, B ⟶ (K n).X k) (n : ℕ) :
    product_degree_lift R K k f ≫ (Pi.π K n).f k = f n :=
  (isLimitOfHasProductOfPreservesLimit
    (HomologicalComplex.eval A (.up ℤ) k) K).fac (Fan.mk B f) ⟨n⟩

private def coordinateLift (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (k : ℤ)
    {B : A} (f : ∀ b, B ⟶ (roosP X).X (degree k b)) : B ⟶ (roosF.obj X).X k :=
  f false ≫ (CochainComplex.mappingCocone.inl (roosU X)).v k k (add_zero k) +
    f true ≫ (CochainComplex.mappingCocone.inr (roosU X)).1.v (k - 1) k (by omega)

omit [EssentiallySmall.{r} C] in
private theorem doubleCoordinate_ext
    (V : ℕᵒᵖ ⥤ ℕᵒᵖ ⥤ CochainComplex A ℤ) (k : ℤ)
    {B : A} {f g : B ⟶ (doubleLimit R V).X k}
    (h : ∀ p q n j, f ≫ doubleCoordinate R V k p q n j =
      g ≫ doubleCoordinate R V k p q n j) : f = g := by
  apply coordinate_ext R _ k
  intro p
  apply product_degree_ext R
    (fun n ↦ (limitComplex R).obj (V.obj (op n))) (degree k p)
  intro n
  apply coordinate_ext R _ (degree k p)
  intro q
  apply product_degree_ext R
    (fun j ↦ (V.obj (op n)).obj (op j)) (degree (degree k p) q)
  intro j
  simpa only [doubleCoordinate, PrincipalQuotientCompletion.transpose,
    Functor.comp_obj, Category.assoc] using h p q n j

private def doubleLift (V : ℕᵒᵖ ⥤ ℕᵒᵖ ⥤ CochainComplex A ℤ) (k : ℤ)
    {B : A} (f : ∀ p q n j, B ⟶ ((V.obj (op n)).obj (op j)).X
      (degree (degree k p) q)) : B ⟶ (doubleLimit R V).X k :=
  coordinateLift R (koszulTowerComplex R (V ⋙ limitComplex R)) k (fun p ↦
    product_degree_lift R (fun n ↦ (limitComplex R).obj (V.obj (op n)))
      (degree k p) (fun n ↦
        coordinateLift R (koszulTowerComplex R (V.obj (op n))) (degree k p) (fun q ↦
          product_degree_lift R (fun j ↦ (V.obj (op n)).obj (op j))
            (degree (degree k p) q) (fun j ↦ f p q n j))))

@[reassoc (attr := simp)]
private theorem doubleLift_coordinate (V : ℕᵒᵖ ⥤ ℕᵒᵖ ⥤ CochainComplex A ℤ)
    (k : ℤ) {B : A} (f : ∀ p q n j, B ⟶ ((V.obj (op n)).obj (op j)).X
      (degree (degree k p) q)) (p q : Bool) (n j : ℕ) :
    doubleLift R V k f ≫ doubleCoordinate R V k p q n j = f p q n j := by
  simp only [doubleLift, doubleCoordinate, coordinateLift_coordinate_assoc,
    product_degree_lift_π_assoc, product_degree_lift_π]

private def transposeCoordinates (V : ℕᵒᵖ ⥤ ℕᵒᵖ ⥤ CochainComplex A ℤ) (k : ℤ) :
    ∀ p q n j, (doubleLimit R V.flip).X k ⟶
      ((V.obj (op n)).obj (op j)).X (degree (degree k p) q)
  | false, false, n, j => doubleCoordinate R V.flip k false false j n
  | false, true, n, j => doubleCoordinate R V.flip k true false j n
  | true, false, n, j => doubleCoordinate R V.flip k false true j n
  | true, true, n, j => -doubleCoordinate R V.flip k true true j n

private def transposeX (V : ℕᵒᵖ ⥤ ℕᵒᵖ ⥤ CochainComplex A ℤ) (k : ℤ) :
    (doubleLimit R V.flip).X k ⟶ (doubleLimit R V).X k :=
  doubleLift R V k (transposeCoordinates R V k)

@[reassoc (attr := simp)]
private theorem transposeX_00 (V : ℕᵒᵖ ⥤ ℕᵒᵖ ⥤ CochainComplex A ℤ)
    (k : ℤ) (n j : ℕ) :
    transposeX R V k ≫ doubleCoordinate R V k false false n j =
      doubleCoordinate R V.flip k false false j n := by
  exact doubleLift_coordinate R V k _ false false n j

@[reassoc (attr := simp)]
private theorem transposeX_01 (V : ℕᵒᵖ ⥤ ℕᵒᵖ ⥤ CochainComplex A ℤ)
    (k : ℤ) (n j : ℕ) :
    transposeX R V k ≫ doubleCoordinate R V k false true n j =
      doubleCoordinate R V.flip k true false j n := by
  exact doubleLift_coordinate R V k _ false true n j

@[reassoc (attr := simp)]
private theorem transposeX_10 (V : ℕᵒᵖ ⥤ ℕᵒᵖ ⥤ CochainComplex A ℤ)
    (k : ℤ) (n j : ℕ) :
    transposeX R V k ≫ doubleCoordinate R V k true false n j =
      doubleCoordinate R V.flip k false true j n := by
  exact doubleLift_coordinate R V k _ true false n j

@[reassoc (attr := simp)]
private theorem transposeX_11 (V : ℕᵒᵖ ⥤ ℕᵒᵖ ⥤ CochainComplex A ℤ)
    (k : ℤ) (n j : ℕ) :
    transposeX R V k ≫ doubleCoordinate R V k true true n j =
      -doubleCoordinate R V.flip k true true j n := by
  exact doubleLift_coordinate R V k _ true true n j

private theorem transposeX_square (V : ℕᵒᵖ ⥤ ℕᵒᵖ ⥤ CochainComplex A ℤ) (k : ℤ) :
    transposeX R V.flip k ≫ transposeX R V k = 𝟙 _ := by
  apply doubleCoordinate_ext R V k
  intro p q n j
  cases p <;> cases q <;> simp [Category.assoc] <;> rfl

omit [EssentiallySmall.{r} C] in
@[reassoc]
private theorem limit_map_coordinate
    {V W : ℕᵒᵖ ⥤ CochainComplex A ℤ} (f : V ⟶ W)
    (k : ℤ) (p : Bool) (n : ℕ) :
    ((limitComplex R).map f).f k ≫ coordinate R (koszulTowerComplex R W) k p ≫
      (Pi.π (fun n ↦ W.obj (op n)) n).f (degree k p) =
    coordinate R (koszulTowerComplex R V) k p ≫
      (Pi.π (fun n ↦ V.obj (op n)) n).f (degree k p) ≫
      (f.app (op n)).f (degree k p) := by
  change (roosF.map (koszulTowerComplexMap R f)).f k ≫ _ = _
  rw [coordinate_map_assoc]
  exact congrArg (fun z ↦ coordinate R (koszulTowerComplex R V) k p ≫ z)
    (congrArg (fun z ↦ z.f (degree k p))
      (Pi.map_π (fun n ↦ f.app (op n)) n))

@[reassoc]
private theorem doubleMap_coordinate
    {V W : ℕᵒᵖ ⥤ ℕᵒᵖ ⥤ CochainComplex A ℤ} (f : V ⟶ W)
    (k : ℤ) (p q : Bool) (n j : ℕ) :
    (doubleMap R f).f k ≫ doubleCoordinate R W k p q n j =
      doubleCoordinate R V k p q n j ≫
        ((f.app (op n)).app (op j)).f (degree (degree k p) q) := by
  have ho := limit_map_coordinate R (Functor.whiskerRight f (limitComplex R)) k p n
  have hi := limit_map_coordinate R (f.app (op n)) (degree k p) q j
  have h₁ := congrArg (fun z ↦ z ≫
    coordinate R (koszulTowerComplex R (W.obj (op n))) (degree k p) q ≫
    (Pi.π (fun j ↦ (W.obj (op n)).obj (op j)) j).f (degree (degree k p) q)) ho
  have h₂ := congrArg (fun z ↦
    coordinate R (koszulTowerComplex R (V ⋙ limitComplex R)) k p ≫
    (Pi.π (fun n ↦ (limitComplex R).obj (V.obj (op n))) n).f (degree k p) ≫ z) hi
  exact (by simpa only [doubleLimit, doubleMap, doubleCoordinate, Functor.comp_obj,
    Functor.whiskerRight_app, Category.assoc] using h₁.trans h₂)

private theorem transposeX_natural
    {V W : ℕᵒᵖ ⥤ ℕᵒᵖ ⥤ CochainComplex A ℤ} (f : V ⟶ W) (k : ℤ) :
    (doubleMap R ((flipFunctor _ _ _).map f)).f k ≫ transposeX R W k =
      transposeX R V k ≫ (doubleMap R f).f k := by
  apply doubleCoordinate_ext R W k
  intro p q n j
  cases p <;> cases q <;> simp [Category.assoc, doubleMap_coordinate] <;> rfl

private def doubleEval
    (V : ℕᵒᵖ ⥤ ℕᵒᵖ ⥤ CochainComplex A ℤ) (n j : ℕ) :
    doubleLimit R V ⟶ (V.obj (op n)).obj (op j) :=
  roosEval (koszulTowerComplex R (V ⋙ limitComplex R)) n ≫
    roosEval (koszulTowerComplex R (V.obj (op n))) j

private theorem doubleEval_f
    (V : ℕᵒᵖ ⥤ ℕᵒᵖ ⥤ CochainComplex A ℤ) (n j : ℕ) (k : ℤ) :
    (doubleEval R V n j).f k = doubleCoordinate R V k false false n j := by
  rfl

omit [EssentiallySmall.{r} C] in
private theorem doubleCoordinate_d00
    (V : ℕᵒᵖ ⥤ ℕᵒᵖ ⥤ CochainComplex A ℤ) (k l : ℤ) (n j : ℕ) :
    (doubleLimit R V).d k l ≫ doubleCoordinate R V l false false n j =
      doubleCoordinate R V k false false n j ≫ ((V.obj (op n)).obj (op j)).d k l := by
  simpa only [doubleEval_f] using (doubleEval R V n j).comm k l |>.symm

omit [EssentiallySmall.{r} C] in
omit [EssentiallySmall.{r} C] in
private abbrev c00 (V : ℕᵒᵖ ⥤ ℕᵒᵖ ⥤ CochainComplex A ℤ)
    (k : ℤ) (n j : ℕ) :
    (doubleLimit R V).X k ⟶ ((V.obj (op n)).obj (op j)).X k :=
  doubleCoordinate R V k false false n j

private abbrev c01 (V : ℕᵒᵖ ⥤ ℕᵒᵖ ⥤ CochainComplex A ℤ)
    (k i : ℤ) (hi : k - 1 = i) (n j : ℕ) :
    (doubleLimit R V).X k ⟶ ((V.obj (op n)).obj (op j)).X i :=
  RoosConeCalculus.v (koszulTowerComplex R (V ⋙ limitComplex R)) k ≫
    RoosConeCalculus.π (koszulTowerComplex R (V ⋙ limitComplex R)) k n ≫
    RoosConeCalculus.ucoord (koszulTowerComplex R (V.obj (op n))) k i hi ≫
    RoosConeCalculus.π (koszulTowerComplex R (V.obj (op n))) i j

omit [HasSheafify J AddCommGrpCat] [J.WEqualsLocallyBijective AddCommGrpCat.{r}] in
@[simp]
private theorem tower_d (V : ℕᵒᵖ ⥤ CochainComplex A ℤ) (k l : ℤ) (n : ℕ) :
    ((koszulTowerComplex R V).d k l).app (op n) = (V.obj (op n)).d k l := rfl

omit [HasSheafify J AddCommGrpCat] [J.WEqualsLocallyBijective AddCommGrpCat.{r}] in
@[simp]
private theorem tower_map (V : ℕᵒᵖ ⥤ CochainComplex A ℤ) (k : ℤ) (n : ℕ) :
    ((koszulTowerComplex R V).asFunctor.map (homOfLE (Nat.le_succ n)).op).f k =
      (V.map (homOfLE (Nat.le_succ n)).op).f k := rfl

@[simp]
private theorem limit_d (V : ℕᵒᵖ ⥤ CochainComplex A ℤ) (k l : ℤ) :
    ((limitComplex R).obj V).d k l =
      (roosF.obj (koszulTowerComplex R V)).d k l := rfl

private theorem c01_d
    (V : ℕᵒᵖ ⥤ ℕᵒᵖ ⥤ CochainComplex A ℤ) (k : ℤ) (n j : ℕ) :
    (doubleLimit R V).d k (k + 1) ≫ c01 R V (k + 1) k (by omega) n j =
      -(c01 R V k (k - 1) rfl n j ≫ ((V.obj (op n)).obj (op j)).d (k - 1) k) -
        c00 R V k n j +
        c00 R V k n (j + 1) ≫
          ((V.obj (op n)).map (homOfLE (Nat.le_succ j)).op).f k := by
  change (roosF.obj (koszulTowerComplex R (V ⋙ limitComplex R))).d k (k + 1) ≫
    c01 R V (k + 1) k (by omega) n j = _
  simp only [c01, Category.assoc, tower_d, tower_map, limit_d, Functor.comp_obj,
    v_d_assoc, RoosConeCalculus.π_d_assoc,
    RoosConeCalculus.differential_u_assoc, Preadditive.sub_comp, Preadditive.neg_comp,
    RoosConeCalculus.π_u, RoosConeCalculus.π_d, Preadditive.comp_sub,
    Preadditive.comp_neg]
  change -(c01 R V k (k - 1) rfl n j ≫
      ((V.obj (op n)).obj (op j)).d (k - 1) k) -
    (c00 R V k n j - c00 R V k n (j + 1) ≫
      ((V.obj (op n)).map (homOfLE (Nat.le_succ j)).op).f k) = _
  simp only [c01, Category.assoc]
  abel

omit [EssentiallySmall.{r} C] in
@[reassoc]
private theorem limit_map_v
    {V W : ℕᵒᵖ ⥤ CochainComplex A ℤ} (f : V ⟶ W) (k : ℤ) (j : ℕ) :
    ((limitComplex R).map f).f k ≫
      RoosConeCalculus.v (koszulTowerComplex R W) k ≫
      RoosConeCalculus.π (koszulTowerComplex R W) k j =
    RoosConeCalculus.v (koszulTowerComplex R V) k ≫
      RoosConeCalculus.π (koszulTowerComplex R V) k j ≫ (f.app (op j)).f k :=
  limit_map_coordinate R f k false j

@[reassoc]
private theorem limit_map_u
    {V W : ℕᵒᵖ ⥤ CochainComplex A ℤ} (f : V ⟶ W)
    (k i : ℤ) (hi : k - 1 = i) (j : ℕ) :
    ((limitComplex R).map f).f k ≫
      RoosConeCalculus.ucoord (koszulTowerComplex R W) k i hi ≫
      RoosConeCalculus.π (koszulTowerComplex R W) i j =
    RoosConeCalculus.ucoord (koszulTowerComplex R V) k i hi ≫
      RoosConeCalculus.π (koszulTowerComplex R V) i j ≫ (f.app (op j)).f i := by
  subst i
  exact limit_map_coordinate R f k true j

private abbrev c10 (V : ℕᵒᵖ ⥤ ℕᵒᵖ ⥤ CochainComplex A ℤ)
    (k i : ℤ) (hi : k - 1 = i) (n j : ℕ) :
    (doubleLimit R V).X k ⟶ ((V.obj (op n)).obj (op j)).X i :=
  RoosConeCalculus.ucoord (koszulTowerComplex R (V ⋙ limitComplex R)) k i hi ≫
    RoosConeCalculus.π (koszulTowerComplex R (V ⋙ limitComplex R)) i n ≫
    RoosConeCalculus.v (koszulTowerComplex R (V.obj (op n))) i ≫
    RoosConeCalculus.π (koszulTowerComplex R (V.obj (op n))) i j

private abbrev c11 (V : ℕᵒᵖ ⥤ ℕᵒᵖ ⥤ CochainComplex A ℤ)
    (k i t : ℤ) (hi : k - 1 = i) (ht : i - 1 = t) (n j : ℕ) :
    (doubleLimit R V).X k ⟶ ((V.obj (op n)).obj (op j)).X t :=
  RoosConeCalculus.ucoord (koszulTowerComplex R (V ⋙ limitComplex R)) k i hi ≫
    RoosConeCalculus.π (koszulTowerComplex R (V ⋙ limitComplex R)) i n ≫
    RoosConeCalculus.ucoord (koszulTowerComplex R (V.obj (op n))) i t ht ≫
    RoosConeCalculus.π (koszulTowerComplex R (V.obj (op n))) t j

private theorem c10_d
    (V : ℕᵒᵖ ⥤ ℕᵒᵖ ⥤ CochainComplex A ℤ) (k : ℤ) (n j : ℕ) :
    (doubleLimit R V).d k (k + 1) ≫ c10 R V (k + 1) k (by omega) n j =
      -(c10 R V k (k - 1) rfl n j ≫ ((V.obj (op n)).obj (op j)).d (k - 1) k) -
        c00 R V k n j + c00 R V k (n + 1) j ≫
          ((V.map (homOfLE (Nat.le_succ n)).op).app (op j)).f k := by
  change (roosF.obj (koszulTowerComplex R (V ⋙ limitComplex R))).d k (k + 1) ≫
    c10 R V (k + 1) k (by omega) n j = _
  simp only [c10, Category.assoc, tower_d, tower_map, limit_d, Functor.comp_obj,
    Functor.comp_map, RoosConeCalculus.differential_u_assoc,
    Preadditive.sub_comp, Preadditive.neg_comp, RoosConeCalculus.π_d_assoc,
    v_d_assoc, RoosConeCalculus.π_d, RoosConeCalculus.π_u_assoc,
    Preadditive.comp_sub, limit_map_v]
  change -(c10 R V k (k - 1) rfl n j ≫
      ((V.obj (op n)).obj (op j)).d (k - 1) k) -
    (c00 R V k n j - c00 R V k (n + 1) j ≫
      ((V.map (homOfLE (Nat.le_succ n)).op).app (op j)).f k) = _
  simp only [c10, Category.assoc]
  abel

private theorem c11_d
    (V : ℕᵒᵖ ⥤ ℕᵒᵖ ⥤ CochainComplex A ℤ) (k : ℤ) (n j : ℕ) :
    (doubleLimit R V).d k (k + 1) ≫ c11 R V (k + 1) k (k - 1) (by omega) rfl n j =
      c11 R V k (k - 1) (k - 1 - 1) rfl rfl n j ≫
          ((V.obj (op n)).obj (op j)).d (k - 1 - 1) (k - 1) +
        c10 R V k (k - 1) rfl n j -
        c10 R V k (k - 1) rfl n (j + 1) ≫
          ((V.obj (op n)).map (homOfLE (Nat.le_succ j)).op).f (k - 1) -
        c01 R V k (k - 1) rfl n j +
        c01 R V k (k - 1) rfl (n + 1) j ≫
          ((V.map (homOfLE (Nat.le_succ n)).op).app (op j)).f (k - 1) := by
  change (roosF.obj (koszulTowerComplex R (V ⋙ limitComplex R))).d k (k + 1) ≫
    c11 R V (k + 1) k (k - 1) (by omega) rfl n j = _
  simp only [c11, Category.assoc, tower_d, tower_map, limit_d, Functor.comp_obj,
    Functor.comp_map, RoosConeCalculus.differential_u_assoc,
    u_d_at_assoc R (koszulTowerComplex R (V.obj (op n)))
      (k - 1) (k - 1 - 1) k rfl (by omega),
    Preadditive.sub_comp, Preadditive.neg_comp, RoosConeCalculus.π_d_assoc,
    RoosConeCalculus.π_u_assoc, RoosConeCalculus.π_u, RoosConeCalculus.π_d,
    Preadditive.comp_sub, Preadditive.comp_neg, limit_map_u]
  change -(-(c11 R V k (k - 1) (k - 1 - 1) rfl rfl n j ≫
      ((V.obj (op n)).obj (op j)).d (k - 1 - 1) (k - 1)) -
    (c10 R V k (k - 1) rfl n j - c10 R V k (k - 1) rfl n (j + 1) ≫
      ((V.obj (op n)).map (homOfLE (Nat.le_succ j)).op).f (k - 1))) -
    (c01 R V k (k - 1) rfl n j - c01 R V k (k - 1) rfl (n + 1) j ≫
      ((V.map (homOfLE (Nat.le_succ n)).op).app (op j)).f (k - 1)) = _
  simp only [c01, c10, c11, Category.assoc]
  abel

@[reassoc]
private theorem c01_transport
    (V : ℕᵒᵖ ⥤ ℕᵒᵖ ⥤ CochainComplex A ℤ) (k i i' : ℤ)
    (hi : k - 1 = i) (hi' : k - 1 = i') (n j : ℕ) :
    c01 R V k i hi n j ≫
        (((V.obj (op n)).obj (op j)).XIsoOfEq (hi.symm.trans hi')).hom =
      c01 R V k i' hi' n j := by
  subst i
  subst i'
  simp only [HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom, Category.comp_id]

@[reassoc]
private theorem c10_transport
    (V : ℕᵒᵖ ⥤ ℕᵒᵖ ⥤ CochainComplex A ℤ) (k i i' : ℤ)
    (hi : k - 1 = i) (hi' : k - 1 = i') (n j : ℕ) :
    c10 R V k i hi n j ≫
        (((V.obj (op n)).obj (op j)).XIsoOfEq (hi.symm.trans hi')).hom =
      c10 R V k i' hi' n j := by
  subst i
  subst i'
  simp only [HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom, Category.comp_id]

@[reassoc]
private theorem c11_transport
    (V : ℕᵒᵖ ⥤ ℕᵒᵖ ⥤ CochainComplex A ℤ) (k i i' t t' : ℤ)
    (hi : k - 1 = i) (hi' : k - 1 = i')
    (ht : i - 1 = t) (ht' : i' - 1 = t') (n j : ℕ) :
    c11 R V k i t hi ht n j ≫
        (((V.obj (op n)).obj (op j)).XIsoOfEq (show t = t' by omega)).hom =
      c11 R V k i' t' hi' ht' n j := by
  subst i
  subst i'
  subst t
  subst t'
  simp only [HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom, Category.comp_id]

@[reassoc (attr := simp)]
private theorem transpose_c00
    (V : ℕᵒᵖ ⥤ ℕᵒᵖ ⥤ CochainComplex A ℤ) (k : ℤ) (n j : ℕ) :
    transposeX R V k ≫ c00 R V k n j = c00 R V.flip k j n :=
  transposeX_00 R V k n j

@[reassoc (attr := simp)]
private theorem transpose_c01
    (V : ℕᵒᵖ ⥤ ℕᵒᵖ ⥤ CochainComplex A ℤ)
    (k i : ℤ) (hi : k - 1 = i) (n j : ℕ) :
    transposeX R V k ≫ c01 R V k i hi n j = c10 R V.flip k i hi j n := by
  subst i
  exact transposeX_01 R V k n j

@[reassoc (attr := simp)]
private theorem transpose_c10
    (V : ℕᵒᵖ ⥤ ℕᵒᵖ ⥤ CochainComplex A ℤ)
    (k i : ℤ) (hi : k - 1 = i) (n j : ℕ) :
    transposeX R V k ≫ c10 R V k i hi n j = c01 R V.flip k i hi j n := by
  subst i
  exact transposeX_10 R V k n j

@[reassoc (attr := simp)]
private theorem transpose_c11
    (V : ℕᵒᵖ ⥤ ℕᵒᵖ ⥤ CochainComplex A ℤ)
    (k i t : ℤ) (hi : k - 1 = i) (ht : i - 1 = t) (n j : ℕ) :
    transposeX R V k ≫ c11 R V k i t hi ht n j =
      -c11 R V.flip k i t hi ht j n := by
  subst i
  subst t
  exact transposeX_11 R V k n j

private theorem transpose_chain01
    (V : ℕᵒᵖ ⥤ ℕᵒᵖ ⥤ CochainComplex A ℤ) (k : ℤ) (n j : ℕ) :
    transposeX R V k ≫ (doubleLimit R V).d k (k + 1) ≫
        c01 R V (k + 1) k (by omega) n j =
      (doubleLimit R V.flip).d k (k + 1) ≫ transposeX R V (k + 1) ≫
        c01 R V (k + 1) k (by omega) n j := by
  rw [c01_d, transpose_c01, c10_d]
  simp only [Preadditive.comp_add, Preadditive.comp_sub, Preadditive.comp_neg,
    Category.assoc, transpose_c01_assoc, transpose_c00, transpose_c00_assoc]
  rfl

private theorem transpose_chain10
    (V : ℕᵒᵖ ⥤ ℕᵒᵖ ⥤ CochainComplex A ℤ) (k : ℤ) (n j : ℕ) :
    transposeX R V k ≫ (doubleLimit R V).d k (k + 1) ≫
        c10 R V (k + 1) k (by omega) n j =
      (doubleLimit R V.flip).d k (k + 1) ≫ transposeX R V (k + 1) ≫
        c10 R V (k + 1) k (by omega) n j := by
  rw [c10_d, transpose_c10, c01_d]
  simp only [Preadditive.comp_add, Preadditive.comp_sub, Preadditive.comp_neg,
    Category.assoc, transpose_c10_assoc, transpose_c00, transpose_c00_assoc]
  rfl

private theorem transpose_chain11
    (V : ℕᵒᵖ ⥤ ℕᵒᵖ ⥤ CochainComplex A ℤ) (k : ℤ) (n j : ℕ) :
    transposeX R V k ≫ (doubleLimit R V).d k (k + 1) ≫
        c11 R V (k + 1) k (k - 1) (by omega) rfl n j =
      (doubleLimit R V.flip).d k (k + 1) ≫ transposeX R V (k + 1) ≫
        c11 R V (k + 1) k (k - 1) (by omega) rfl n j := by
  rw [c11_d, transpose_c11, Preadditive.comp_neg, c11_d]
  simp only [Preadditive.comp_add, Preadditive.comp_sub,
    Preadditive.neg_comp, Category.assoc, transpose_c11_assoc,
    transpose_c01, transpose_c01_assoc, transpose_c10, transpose_c10_assoc]
  simp only [c01, c10,
    Functor.flip_obj_obj, Functor.flip_obj_map, Functor.flip_map_app]
  abel

/-- Strict signed transposition of double Roos complexes, including naturality.

Proof source: Bhatt--Scholze, Lemma 3.4.13 and Stacks Tag 0941. Distribute
both biproduct coordinates and product projections, reindex `(n,j)` to `(j,n)`,
and multiply the `(true,true)` component by `-1` (this is `transposeX`). In the
coordinates `x_{pq}` of `doubleLimit V` (outer index `n`, inner `j`) the
differential is `x₀₀' = d x₀₀`, `x₀₁' = -d x₀₁ - U_j x₀₀`,
`x₁₀' = -d x₁₀ - U_n x₀₀`, `x₁₁' = d x₁₁ + U_j x₁₀ - U_n x₀₁`, where `U = 1 - S`
are the Roos tower differences; the same formulas with `n,j` exchanged hold for
`V.flip`. Substituting `x₀₀ = y₀₀`, `x₀₁ = y₁₀`, `x₁₀ = y₀₁`, `x₁₁ = -y₁₁` turns
one system into the other, so the swap is a chain map. Applying it twice is the
identity (`transposeX_square`), and diagonal product maps prove naturality
(`transposeX_natural`). -/
theorem signed_double_roos_chain_iso :
    ∃ T : ∀ V : ℕᵒᵖ ⥤ ℕᵒᵖ ⥤ CochainComplex (ringedSiteModules.{r}
        (SheafOfModules.derivedChangeRingIndependentCoefficients J R)) ℤ,
        doubleLimit R V.flip ≅ doubleLimit R V,
      (∀ V (k : ℤ) (n j : ℕ),
        (T V).hom.f k ≫ doubleCoordinate R V k false false n j =
          doubleCoordinate R V.flip k false false j n ∧
        (T V).hom.f k ≫ doubleCoordinate R V k true false n j =
          doubleCoordinate R V.flip k false true j n ∧
        (T V).hom.f k ≫ doubleCoordinate R V k false true n j =
          doubleCoordinate R V.flip k true false j n ∧
        (T V).hom.f k ≫ doubleCoordinate R V k true true n j =
          -doubleCoordinate R V.flip k true true j n) ∧
      (∀ {V W} (f : V ⟶ W),
        doubleMap R ((flipFunctor _ _ _).map f) ≫ (T W).hom =
          (T V).hom ≫ doubleMap R f) := by
  let h : ∀ V, doubleLimit R V.flip ⟶ doubleLimit R V := fun V ↦
    { f := transposeX R V
      comm' := by
        intro k l hkl
        have hkl' : k + 1 = l := by simpa [ComplexShape.up_Rel] using hkl
        subst l
        apply doubleCoordinate_ext R V (k + 1)
        intro p q n j
        cases p <;> cases q
        · rw [Category.assoc, doubleCoordinate_d00, transposeX_00_assoc]
          simpa only [Category.assoc, transposeX_00, Functor.flip_obj_obj] using
            (doubleCoordinate_d00 R V.flip k (k + 1) j n).symm
        · change (transposeX R V k ≫ (doubleLimit R V).d k (k + 1)) ≫
              c01 R V (k + 1) (k + 1 - 1) rfl n j =
            ((doubleLimit R V.flip).d k (k + 1) ≫ transposeX R V (k + 1)) ≫
              c01 R V (k + 1) (k + 1 - 1) rfl n j
          apply (cancel_mono ((((V.obj (op n)).obj (op j)).XIsoOfEq
            (show k + 1 - 1 = k by omega)).hom)).1
          simpa only [Category.assoc,
            c01_transport R V (k + 1) (k + 1 - 1) k rfl (by omega) n j] using
            transpose_chain01 R V k n j
        · change (transposeX R V k ≫ (doubleLimit R V).d k (k + 1)) ≫
              c10 R V (k + 1) (k + 1 - 1) rfl n j =
            ((doubleLimit R V.flip).d k (k + 1) ≫ transposeX R V (k + 1)) ≫
              c10 R V (k + 1) (k + 1 - 1) rfl n j
          apply (cancel_mono ((((V.obj (op n)).obj (op j)).XIsoOfEq
            (show k + 1 - 1 = k by omega)).hom)).1
          simpa only [Category.assoc,
            c10_transport R V (k + 1) (k + 1 - 1) k rfl (by omega) n j] using
            transpose_chain10 R V k n j
        · change (transposeX R V k ≫ (doubleLimit R V).d k (k + 1)) ≫
              c11 R V (k + 1) (k + 1 - 1) (k + 1 - 1 - 1) rfl rfl n j =
            ((doubleLimit R V.flip).d k (k + 1) ≫ transposeX R V (k + 1)) ≫
              c11 R V (k + 1) (k + 1 - 1) (k + 1 - 1 - 1) rfl rfl n j
          apply (cancel_mono ((((V.obj (op n)).obj (op j)).XIsoOfEq
            (show k + 1 - 1 - 1 = k - 1 by omega)).hom)).1
          simpa only [Category.assoc,
            c11_transport R V (k + 1) (k + 1 - 1) k (k + 1 - 1 - 1) (k - 1)
              rfl (by omega) rfl rfl n j] using transpose_chain11 R V k n j }
  let T : ∀ V, doubleLimit R V.flip ≅ doubleLimit R V := fun V ↦
    HomologicalComplex.Hom.isoOfComponents (fun k ↦
      { hom := transposeX R V k
        inv := transposeX R V.flip k
        hom_inv_id := by
          simpa only [Functor.flip_flip] using transposeX_square R V.flip k
        inv_hom_id := by
          exact transposeX_square R V k })
      (by exact fun k l hkl ↦ (h V).comm k l)
  refine ⟨T, ?_, ?_⟩
  · intro V k n j
    dsimp [T]
    exact ⟨transposeX_00 R V k n j, transposeX_10 R V k n j,
      transposeX_01 R V k n j, transposeX_11 R V k n j⟩
  · intro V W f
    dsimp [T]
    apply HomologicalComplex.Hom.ext
    funext k
    exact transposeX_natural R f k

end CategoryTheory.RingedPowerTorsion
