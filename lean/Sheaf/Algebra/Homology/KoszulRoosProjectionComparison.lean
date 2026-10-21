/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q128
-/
module

public import Sheaf.Algebra.Homology.PrincipalKoszulQuotientTowers
public import Sheaf.Algebra.Category.Ring.Sheaf.PrincipalPowerQuotients
public import Sheaf.Algebra.Homology.RestrictedKFlatTensorIdentification
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import Sheaf.CategoryTheory.StrictRoosModel
public import Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import Sheaf.CategoryTheory.DerivedCategory.AdjointFunctors
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Algebra.Homology.KInjectiveProductsTermwise
import Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact
import Sheaf.CategoryTheory.StrictRoosComparison
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Sheaf.Paper.RingedScalarExtensionComplexAdjunction
import Sheaf.Paper.RingedTopoiTensorSections

/-! # Koszul tensor, finite tails, and normalized Roos projection adjoints

Source: blueprint main-20261015, sec-smooth-purity/sk-lem-sp-tower, proof paragraph 1;
Bhatt--Scholze, The pro-etale topology for schemes, Sections 3.1 and 3.5;
Stacks Project, Tags 0941, 06YY, 09T5 and 03CZ.
(blueprint: lem-sp-koszul-roos-projection-comparison)

Positive tower and power indices are encoded by predecessors: index m means m+1.
A tail parameter h means deletion of the first h levels, so h=0 is the paper's h=1.
The tensor is written scalar first, K_m tensor X, using the canonical symmetry of
sheaf tensor to identify it with the paper's X tensor K_m.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u v r w t z
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped ChangeOfRings

namespace CategoryTheory.KoszulRoos

variable {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
  {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [HasSheafify J AddCommGrpCat.{r}] [J.WEqualsLocallyBijective AddCommGrpCat.{r}]

/-- The existing category of ringed-site modules.
Source: Stacks 03CZ (blueprint: lem-sp-koszul-roos-projection-comparison). -/
abbrev Modules (R : Sheaf J CommRingCat.{r}) :=
  ringedSiteModules.{r} (SheafOfModules.derivedChangeRingIndependentCoefficients J R)

/-- A global ring section regarded as a section of its unit module.
Source: Stacks 03CZ (blueprint: lem-sp-koszul-roos-projection-comparison). -/
def unitSection (R : Sheaf J CommRingCat.{r})
    (s : (R.obj ⋙ forget CommRingCat.{r}).sections) :
    (SheafOfModules.unit
      (SheafOfModules.derivedChangeRingIndependentCoefficients J R)).sections :=
  ⟨s.val, s.property⟩

/-- The existing two-term Koszul complex, with power m+1.
Source: Stacks 06YY (blueprint: lem-sp-koszul-roos-projection-comparison). -/
abbrev K (R : Sheaf J CommRingCat.{r})
    (s : (R.obj ⋙ forget CommRingCat.{r}).sections) (m : ℕ) :=
  principalKoszul R (unitSection R s) m

/-- The existing quotient ring sheaf, with power m+1.
Source: Stacks 06YY (blueprint: lem-sp-koszul-roos-projection-comparison). -/
abbrev B (R : Sheaf J CommRingCat.{r})
    (s : (R.obj ⋙ forget CommRingCat.{r}).sections) [HasSheafify J CommRingCat.{r}]
    (m : ℕ) := principalPowerRingQuotient R s (m + 1)

/-- The existing quotient ring projection.
Source: Stacks 06YY (blueprint: lem-sp-koszul-roos-projection-comparison). -/
abbrev quotient (R : Sheaf J CommRingCat.{r})
    (s : (R.obj ⋙ forget CommRingCat.{r}).sections) [HasSheafify J CommRingCat.{r}]
    (m : ℕ) := principalPowerRingProjection R s (m + 1)

/-- Total tensor with the actual two-term Koszul complex, in scalar-first order.
Source: Stacks 012Z (blueprint: lem-sp-koszul-roos-projection-comparison). -/
def tensor (R : Sheaf J CommRingCat.{r})
    (s : (R.obj ⋙ forget CommRingCat.{r}).sections) (m : ℕ) :
    CochainComplex (Modules R) ℤ ⥤ CochainComplex (Modules R) ℤ :=
  (curriedTensor (Modules R)).map₂CochainComplex.obj (K R s m)

/-- Reassemble a strict tower of complexes using the existing tower construction.
Source: Stacks 0941 (blueprint: lem-sp-koszul-roos-projection-comparison). -/
def assemble (R : Sheaf J CommRingCat.{r}) :
    (ℕᵒᵖ ⥤ CochainComplex (Modules R) ℤ) ⥤ CochainComplex (ℕᵒᵖ ⥤ Modules R) ℤ where
  obj := koszulTowerComplex R
  map := koszulTowerComplexMap R
  map_id X := by ext i n; rfl
  map_comp f g := by ext i n; rfl

/-- A total-tensor summand, with its target explicitly given by the tensor functor.
Source: Stacks 012Z (blueprint: lem-sp-koszul-roos-projection-comparison). -/
def summand (R : Sheaf J CommRingCat.{r})
    (s : (R.obj ⋙ forget CommRingCat.{r}).sections) (m : ℕ)
    (P : CochainComplex (Modules R) ℤ) (a b q : ℤ) (hab : a + b = q) :
    (K R s m).X a ⊗ P.X b ⟶ ((tensor R s m).obj P).X q :=
  CochainComplex.ιMapBifunctor (K R s m) P (curriedTensor (Modules R)) a b q hab

/-- Apply a complex functor to each level of a strict tower.
Source: Stacks 0941 (blueprint: lem-sp-koszul-roos-projection-comparison). -/
def onTowers (R : Sheaf J CommRingCat.{r})
    (F : CochainComplex (Modules R) ℤ ⥤ CochainComplex (Modules R) ℤ) :
    CochainComplex (ℕᵒᵖ ⥤ Modules R) ℤ ⥤ CochainComplex (ℕᵒᵖ ⥤ Modules R) ℤ :=
  HomologicalComplex.complexOfFunctorsToFunctorToComplex ⋙
    (Functor.whiskeringRight _ _ _).obj F ⋙ assemble R

/-- Shift the nonnegative index by h; positive indices start at h+1.
Source: Stacks 0941 (blueprint: lem-sp-koszul-roos-projection-comparison). -/
def tailIndex (h : ℕ) : ℕ ⥤ ℕ :=
  (⟨fun n ↦ h + n, fun _ _ hnm ↦ Nat.add_le_add_left hnm h⟩ : ℕ →o ℕ).monotone.functor

/-- Delete a finite prefix of a strict tower complex.
Source: Stacks 0941 (blueprint: lem-sp-koszul-roos-projection-comparison). -/
def tail (R : Sheaf J CommRingCat.{r}) (h : ℕ) :=
  ((Functor.whiskeringLeft _ _ (Modules R)).obj (tailIndex h).op).mapHomologicalComplex
    (.up ℤ)

/-- Product coordinate deletion, applied in both copies of the Roos product.
Source: Stacks 0941 (blueprint: lem-sp-koszul-roos-projection-comparison). -/
def deletionProduct (R : Sheaf J CommRingCat.{r})
    (X : CochainComplex (ℕᵒᵖ ⥤ Modules R) ℤ) (h : ℕ) :
    roosP X ⟶ roosP ((tail R h).obj X) :=
  Pi.lift (fun n : ℕ ↦ Pi.π (fun i : ℕ ↦ X.asFunctor.obj (op i)) (h + n))

/-- The canonical tensor/product comparison, specified by every coordinate.
Source: Stacks 0941, 012Z (blueprint: lem-sp-koszul-roos-projection-comparison). -/
def tensorProduct (R : Sheaf J CommRingCat.{r})
    (s : (R.obj ⋙ forget CommRingCat.{r}).sections) (m : ℕ)
    (X : CochainComplex (ℕᵒᵖ ⥤ Modules R) ℤ) :
    (tensor R s m).obj (roosP X) ⟶ roosP ((onTowers R (tensor R s m)).obj X) :=
  Pi.lift (fun n : ℕ ↦ (tensor R s m).map
    (Pi.π (fun i : ℕ ↦ X.asFunctor.obj (op i)) n))

/-- Koszul coefficient transition, using the already defined strict power tower.
Source: Stacks 06YY (blueprint: lem-sp-koszul-roos-projection-comparison). -/
def koszulStep (R : Sheaf J CommRingCat.{r})
    (s : (R.obj ⋙ forget CommRingCat.{r}).sections) {k m : ℕ} (hkm : k ≤ m) :
    K R s m ⟶ K R s k :=
  (principalKoszulTower R (unitSection R s)).map (homOfLE hkm).op

/-- The induced natural transition of total tensor functors.
Source: Stacks 06YY (blueprint: lem-sp-koszul-roos-projection-comparison). -/
def tensorStep (R : Sheaf J CommRingCat.{r})
    (s : (R.obj ⋙ forget CommRingCat.{r}).sections) {k m : ℕ} (hkm : k ≤ m) :
    tensor R s m ⟶ tensor R s k :=
  (curriedTensor (Modules R)).map₂CochainComplex.map (koszulStep R s hkm)

/-- The actual constant tower complex.
Source: Stacks 0941 (blueprint: lem-sp-koszul-roos-projection-comparison). -/
def constant (R : Sheaf J CommRingCat.{r}) (N : CochainComplex (Modules R) ℤ) :=
  (assemble R).obj ((Functor.const ℕᵒᵖ).obj N)

variable (R : Sheaf J CommRingCat.{r})
  (s : (R.obj ⋙ forget CommRingCat.{r}).sections) [HasSheafify J CommRingCat.{r}]
  [∀ S : Sheaf J CommRingCat.{r}, HasDerivedCategory.{w} (Modules S)]
  [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ Modules R)]

/-- The recorded scalar extension model, with the actual principal quotient map.
Source: Stacks 06YY (blueprint: lem-sp-koszul-roos-projection-comparison). -/
abbrev ScalarModel (m : ℕ) :=
  SheafOfModules.DerivedChangeOfRingsCochainModel.{u, v, r, w, w} (quotient R s m)

/-- The recorded exact restriction functor for the principal quotient.
Source: Stacks 03CZ (blueprint: lem-sp-koszul-roos-projection-comparison). -/
abbrev restriction (m : ℕ) := SheafOfModules.restrictedTensorScalars (quotient R s m)

/-- Its termwise action on complexes.
Source: Stacks 03CZ (blueprint: lem-sp-koszul-roos-projection-comparison). -/
abbrev restrictComplex (m : ℕ) := (restriction R s m).mapHomologicalComplex (.up ℤ)

/-- The canonical pure section of a presented scalar extension.
Source: Stacks 03CZ (blueprint: lem-sp-koszul-roos-projection-comparison). -/
def pure (m : ℕ) (D : ScalarModel R s m) (M : Modules R) (U : Cᵒᵖ)
    (b : (B R s m).obj.obj U) (x : M.val.obj U) : (D.E.obj M).val.obj U :=
  (eqToHom (D.obj_eq M).symm).val.app U
    ((toSheafify J (SheafOfModules.changeOfRingsPresheaf (quotient R s m) M).presheaf).app U
      (b ⊗ₜ[R.obj.obj U, ((quotient R s m).hom.app U).hom] x))

/-- Roos coordinates with an arbitrary degree, using explicit equality transports.
Source: Stacks 0941 (blueprint: lem-sp-koszul-roos-projection-comparison). -/
def coordinates (X : CochainComplex (ℕᵒᵖ ⥤ Modules R) ℤ) (q : ℤ) :
    (roosF.obj X).X q ≅ (roosP X).X (q - 1) ⊞ (roosP X).X q :=
  (roosF.obj X).XIsoOfEq (by omega) ≪≫ roosχ X (q - 1) ≪≫
    biprod.mapIso (Iso.refl _) ((roosP X).XIsoOfEq (by omega))

/-- Act on towers by a natural transformation between complex functors.
Source: Stacks 0941 (blueprint: lem-sp-koszul-roos-projection-comparison). -/
def onTowersMap {F G : CochainComplex (Modules R) ℤ ⥤ CochainComplex (Modules R) ℤ}
    (tau : F ⟶ G) : onTowers R F ⟶ onTowers R G :=
  Functor.whiskerRight
    (Functor.whiskerLeft HomologicalComplex.complexOfFunctorsToFunctorToComplex
      ((Functor.whiskeringRight _ _ _).map tau)) (assemble R)


/-- Termwise action of a normalized ordinary coefficient transition.
Source: Stacks 06YY (blueprint: lem-sp-koszul-roos-projection-comparison). -/
def ordinaryTransition {k m : ℕ} (Dm : ScalarModel R s m) (Dk : ScalarModel R s k)
    (e : Dm.E ⋙ restriction R s m ⟶ Dk.E ⋙ restriction R s k) :
    Dm.E.mapHomologicalComplex (.up ℤ) ⋙ restrictComplex R s m ⟶
      Dk.E.mapHomologicalComplex (.up ℤ) ⋙ restrictComplex R s k :=
  e.mapHomologicalComplex (.up ℤ)

/-- Normalized comparison data. Every functor in this structure has its existing
universal property, and every chain comparison is pinned on total-tensor summands
and both Roos coordinates. No arbitrary cone completion is allowed.
Source: Stacks 0941, 06YY and 09T5; blueprint tower proof paragraph 1
(blueprint: lem-sp-koszul-roos-projection-comparison). -/
structure Models where
  /-- The total derived inverse-limit functor. -/
  RF : DerivedCategory (ℕᵒᵖ ⥤ Modules R) ⥤ DerivedCategory (Modules R)
  /-- Its ordinary-limit unit. -/
  eta : roosLimitFunctor ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ RF
  /-- Normalized strict Roos comparison to that functor. -/
  norm : roosF ⋙ DerivedCategory.Q ≅ DerivedCategory.Q ⋙ RF
  /-- Existing K-flat extension models, separately at every coefficient power. -/
  scalar : ∀ m : ℕ, ScalarModel R s m
  /-- The normalized ordinary scalar adjunction. -/
  ordinaryAdj : ∀ m : ℕ, (scalar m).E ⊣ restriction R s m
  /-- Derived scalar extension and exact scalar restriction are adjoint. -/
  derivedAdj : ∀ m : ℕ, (scalar m).T ⊣ (restriction R s m).mapDerivedCategory
  /-- The canonical chain augmentation to ordinary scalar extension, then restriction. -/
  aug : ∀ m : ℕ, tensor R s m ⟶
    (scalar m).E.mapHomologicalComplex (.up ℤ) ⋙ restrictComplex R s m
  /-- Natural two-term computation of restricted derived extension. -/
  A : ∀ m : ℕ, tensor R s m ⋙ DerivedCategory.Q ≅
    DerivedCategory.Q ⋙ (scalar m).T ⋙ (restriction R s m).mapDerivedCategory
  /-- The natural chain isomorphism interchanging Koszul tensor and the Roos cone. -/
  chi : ∀ m : ℕ, roosF ⋙ tensor R s m ≅ onTowers R (tensor R s m) ⋙ roosF
  /-- Finite-prefix deletion as a strict chain map. -/
  delete : ∀ (X : CochainComplex (ℕᵒᵖ ⥤ Modules R) ℤ) (h : ℕ),
    roosF.obj X ⟶ roosF.obj ((tail R h).obj X)

/-- Normalization and computation properties of the displayed comparison data.
Source: blueprint tower proof paragraph 1, Stacks 0941, 06YY and 09T5
(blueprint: lem-sp-koszul-roos-projection-comparison). -/
structure Normalization (M : Models R s) : Prop where
  /-- Exactness of countable products on the pro-etale site. -/
  exactProducts : HasExactLimitsOfShape (Discrete ℕ) (Modules R)
  /-- Localized termwise products are the actual derived products. -/
  products : ∀ X : CochainComplex (ℕᵒᵖ ⥤ Modules R) ℤ,
    Nonempty (IsLimit (DerivedCategory.Q.mapCone
      (limit.cone (Discrete.functor (fun n : ℕ ↦ X.asFunctor.obj (op n))))))
  /-- It is the right derived functor of the actual inverse limit. -/
  universal : M.RF.IsRightDerivedFunctor M.eta (HomologicalComplex.quasiIso _ (.up ℤ))
  /-- Normalization on ordinary inverse limits. -/
  norm_unit : ∀ X, DerivedCategory.Q.map (roosι X) ≫ M.norm.hom.app X = M.eta.app X
  /-- The ordinary unit is x mapping to 1 tensor x. -/
  ordinary_unit : ∀ (m : ℕ) (P : Modules R) (U : Cᵒᵖ) (x : P.val.obj U),
    ((M.ordinaryAdj m).unit.app P).val.app U x = pure R s m (M.scalar m) P U 1 x
  /-- Normalization of the derived adjoint on K-flat representatives. -/
  derived_adjunction : ∀ (m : ℕ) (P : CochainComplex (Modules R) ℤ)
    (_hP : CochainComplex.IsKFlatIndependentCoefficients (R := R) P)
    (N : CochainComplex (Modules (B R s m)) ℤ)
    (f : ((M.scalar m).E.mapHomologicalComplex (.up ℤ)).obj P ⟶ N),
    ((M.derivedAdj m).homEquiv _ _).symm
      (DerivedCategory.Q.map
          (((M.ordinaryAdj m).mapHomologicalComplex (.up ℤ)).homEquiv P N f) ≫
        (restriction R s m).mapDerivedCategoryFactors.inv.app N) =
      (M.scalar m).ε.app P ≫ DerivedCategory.Q.map f
  /-- Its degree-zero inclusion is exactly the ordinary tensor unit. -/
  aug_unit : ∀ (m : ℕ) (P : CochainComplex (Modules R) ℤ),
    koszulRepresentativeAugmentation R P (unitSection R s) m ≫ (M.aug m).app P =
      ((M.ordinaryAdj m).mapHomologicalComplex (.up ℤ)).unit.app P
  /-- Augmentation vanishes on all other Koszul-degree summands. -/
  aug_zero : ∀ (m : ℕ) (P : CochainComplex (Modules R) ℤ) (a b : ℤ), a ≠ 0 →
    summand R s m P a b (a + b) rfl ≫
      ((M.aug m).app P).f (a + b) = 0
  /-- Its normalization is the actual augmentation on every K-flat complex. -/
  A_kflat : ∀ (m : ℕ) (P : CochainComplex (Modules R) ℤ),
    CochainComplex.IsKFlatIndependentCoefficients (R := R) P →
    (M.A m).hom.app P ≫
        (restriction R s m).mapDerivedCategory.map ((M.scalar m).ε.app P) ≫
        (restriction R s m).mapDerivedCategoryFactors.hom.app
          (((M.scalar m).E.mapHomologicalComplex (.up ℤ)).obj P) =
      DerivedCategory.Q.map ((M.aug m).app P)
  /-- Finite total tensor commutes with the countable product. -/
  tensor_product : ∀ (m : ℕ) (X : CochainComplex (ℕᵒᵖ ⥤ Modules R) ℤ),
    IsIso (tensorProduct R s m X)
  /-- Its previous-degree Roos coordinate, including the Koszul interchange sign. -/
  chi_first : ∀ (m : ℕ) (X : CochainComplex (ℕᵒᵖ ⥤ Modules R) ℤ) (a b : ℤ),
    summand R s m (roosF.obj X) a b (a + b) rfl ≫ ((M.chi m).hom.app X).f (a + b) ≫
        (coordinates R ((onTowers R (tensor R s m)).obj X) (a + b)).hom ≫ biprod.fst =
      ((-1 : ℤˣ) ^ a) •
        ((K R s m).X a ◁ ((coordinates R X b).hom ≫ biprod.fst) ≫
          summand R s m (roosP X) a (b - 1) (a + b - 1) (by omega) ≫
          (tensorProduct R s m X).f (a + b - 1))
  /-- Its current-degree Roos coordinate is the literal tensor of product projections. -/
  chi_second : ∀ (m : ℕ) (X : CochainComplex (ℕᵒᵖ ⥤ Modules R) ℤ) (a b : ℤ),
    summand R s m (roosF.obj X) a b (a + b) rfl ≫ ((M.chi m).hom.app X).f (a + b) ≫
        (coordinates R ((onTowers R (tensor R s m)).obj X) (a + b)).hom ≫ biprod.snd =
      (K R s m).X a ◁ ((coordinates R X b).hom ≫ biprod.snd) ≫
        summand R s m (roosP X) a b (a + b) rfl ≫ (tensorProduct R s m X).f (a + b)
  /-- Both cone coordinates are coordinate deletion. -/
  delete_coordinates : ∀ (X : CochainComplex (ℕᵒᵖ ⥤ Modules R) ℤ) (h : ℕ) (q : ℤ),
    (M.delete X h).f (q + 1) ≫ (roosχ ((tail R h).obj X) q).hom =
      (roosχ X q).hom ≫
        biprod.map ((deletionProduct R X h).f q) ((deletionProduct R X h).f (q + 1))
  /-- Prefix deletion is a quasi-isomorphism, including the empty prefix. -/
  delete_quasiIso : ∀ (X : CochainComplex (ℕᵒᵖ ⥤ Modules R) ℤ) (h : ℕ),
    QuasiIso (M.delete X h)
  /-- It retains each remaining projection. -/
  delete_projection : ∀ (X : CochainComplex (ℕᵒᵖ ⥤ Modules R) ℤ) (h n : ℕ),
    M.delete X h ≫ roosEval ((tail R h).obj X) n = roosEval X (h + n)
  /-- It is natural for strict maps of towers. -/
  delete_natural : ∀ {X Y : CochainComplex (ℕᵒᵖ ⥤ Modules R) ℤ} (f : X ⟶ Y) (h : ℕ),
    roosF.map f ≫ M.delete Y h = M.delete X h ≫ roosF.map ((tail R h).map f)
  /-- Scalar restriction detects derived isomorphisms. -/
  reflects : ∀ m : ℕ, (restriction R s m).mapDerivedCategory.ReflectsIsomorphisms

namespace Models

/-- The actual derived-limit projection, fixed by the normalized Roos comparison.
Source: Stacks 0941 (blueprint: lem-sp-koszul-roos-projection-comparison). -/
def projection (M : Models R s) (X : CochainComplex (ℕᵒᵖ ⥤ Modules R) ℤ) (n : ℕ) :
    M.RF.obj (DerivedCategory.Q.obj X) ⟶ DerivedCategory.Q.obj (X.asFunctor.obj (op n)) :=
  M.norm.inv.app X ≫ DerivedCategory.Q.map (roosEval X n)


/-- The prescribed composite: inverse two-term comparison, tensor/cone interchange,
tail deletion, then normalized Roos realization. This is a real composite of the
specified maps, never a choice of a cone filler.
Source: blueprint tower proof paragraph 1, Stacks 0941 and 06YY
(blueprint: lem-sp-koszul-roos-projection-comparison). -/
def comparison (M : Models R s) (X : CochainComplex (ℕᵒᵖ ⥤ Modules R) ℤ) (m h : ℕ) :
    ((M.scalar m).T ⋙ (restriction R s m).mapDerivedCategory).obj
        (M.RF.obj (DerivedCategory.Q.obj X)) ⟶
      M.RF.obj (DerivedCategory.Q.obj ((tail R h).obj
        ((onTowers R (tensor R s m)).obj X))) :=
  ((M.scalar m).T ⋙ (restriction R s m).mapDerivedCategory).map (M.norm.inv.app X) ≫
    (M.A m).inv.app (roosF.obj X) ≫ DerivedCategory.Q.map ((M.chi m).hom.app X) ≫
    DerivedCategory.Q.map (M.delete ((onTowers R (tensor R s m)).obj X) h) ≫
    M.norm.hom.app ((tail R h).obj ((onTowers R (tensor R s m)).obj X))


/-- The strict map to the constant restricted target, obtained from the actual
Koszul augmentations and the supplied compatible B_m-linear chain maps.
Source: Stacks 0941 (blueprint: lem-sp-koszul-roos-projection-comparison). -/
def familyMap (M : Models R s) (X : CochainComplex (ℕᵒᵖ ⥤ Modules R) ℤ) (m : ℕ)
    (N : CochainComplex (Modules (B R s m)) ℤ)
    (f : ((tail R m).obj X).asFunctor ⋙
      (M.scalar m).E.mapHomologicalComplex (.up ℤ) ⟶ (Functor.const ℕᵒᵖ).obj N) :
    (tail R m).obj ((onTowers R (tensor R s m)).obj X) ⟶
      constant R ((restrictComplex R s m).obj N) :=
  (assemble R).map
    (Functor.whiskerLeft ((tail R m).obj X).asFunctor (M.aug m) ≫
      Functor.whiskerRight f (restrictComplex R s m))


end Models

/-- All compatibility clauses for the normalized data. The adjoint equation refers
to the actual composite of the definition `Models.comparison` and a strict map of
Roos complexes, so equality is not inferred from projections into a homotopy limit.
Source: blueprint tower proof paragraph 1; Stacks 0941, 06YY and 09T5
(blueprint: lem-sp-koszul-roos-projection-comparison). -/
structure Compatibility (M : Models R s) : Prop extends Normalization R s M where
  /-- The prescribed comparison is an isomorphism. -/
  isIso : ∀ (X : CochainComplex (ℕᵒᵖ ⥤ Modules R) ℤ) (m h : ℕ),
    IsIso (M.comparison R s X m h)
  /-- Every remaining projection is the derived tensor of the original projection. -/
  projection : ∀ (X : CochainComplex (ℕᵒᵖ ⥤ Modules R) ℤ) (m h n : ℕ),
    M.comparison R s X m h ≫
        M.projection R s ((tail R h).obj ((onTowers R (tensor R s m)).obj X)) n =
      ((M.scalar m).T ⋙ (restriction R s m).mapDerivedCategory).map
          (M.projection R s X (h + n)) ≫
        (M.A m).inv.app (X.asFunctor.obj (op (h + n)))
  /-- Constant tower evaluation is inverse to the diagonal after localization. -/
  constant_identification : ∀ N : CochainComplex (Modules R) ℤ,
    IsIso (DerivedCategory.Q.map (roosEval (constant R N) 0)) ∧
    ∃ diagonal : N ⟶ roosF.obj (constant R N),
      (∀ q : ℤ, diagonal.f (q + 1) ≫ (roosχ (constant R N) q).hom =
        biprod.lift 0 ((Pi.lift (fun _ : ℕ ↦ 𝟙 N)).f (q + 1))) ∧
      DerivedCategory.Q.map diagonal ≫
          DerivedCategory.Q.map (roosEval (constant R N) 0) = 𝟙 _ ∧
      DerivedCategory.Q.map (roosEval (constant R N) 0) ≫
          DerivedCategory.Q.map diagonal = 𝟙 _
  /-- The full augmentation/limit/constant-evaluation composite is the restriction
  of the normalized derived adjoint at the first retained level. -/
  adjoint : ∀ (X : CochainComplex (ℕᵒᵖ ⥤ Modules R) ℤ) (m : ℕ)
    (N : CochainComplex (Modules (B R s m)) ℤ)
    (f : ((tail R m).obj X).asFunctor ⋙
      (M.scalar m).E.mapHomologicalComplex (.up ℤ) ⟶ (Functor.const ℕᵒᵖ).obj N),
    M.comparison R s X m m ≫
        M.RF.map (DerivedCategory.Q.map (M.familyMap R s X m N f)) ≫
        M.norm.inv.app (constant R ((restrictComplex R s m).obj N)) ≫
        DerivedCategory.Q.map (roosEval (constant R ((restrictComplex R s m).obj N)) 0) =
      (restriction R s m).mapDerivedCategory.map
        (((M.derivedAdj m).homEquiv _ _).symm
          (M.projection R s X m ≫
            DerivedCategory.Q.map
              (((M.ordinaryAdj m).mapHomologicalComplex (.up ℤ)).homEquiv
                (X.asFunctor.obj (op m)) N (f.app (op 0))) ≫
            (restriction R s m).mapDerivedCategoryFactors.inv.app N)) ≫
        (restriction R s m).mapDerivedCategoryFactors.hom.app N
  /-- The specified Koszul transitions have components (t^(m-k),1).
  The equation uses the actual cone map, so it specifies both degrees. -/
  koszul_transition : ∀ (k m : ℕ) (hkm : k ≤ m),
    ∃ square :
      (CochainComplex.singleFunctor (Modules R) 0).map
          (endoPow (globalSectionMultiplication R (unitSection R s)) (m + 1)) ≫ 𝟙 _ =
        (CochainComplex.singleFunctor (Modules R) 0).map
            (endoPow (globalSectionMultiplication R (unitSection R s)) (m - k)) ≫
          (CochainComplex.singleFunctor (Modules R) 0).map
            (endoPow (globalSectionMultiplication R (unitSection R s)) (k + 1)),
      koszulStep R s hkm = CochainComplex.mappingCone.map _ _
        ((CochainComplex.singleFunctor (Modules R) 0).map
          (endoPow (globalSectionMultiplication R (unitSection R s)) (m - k)))
        (𝟙 _) square
  /-- The actual coefficient quotient transitions, their pure-tensor normalization,
  and the commuting augmentation, two-term, and derived-limit comparison squares.
  Different tails may be compared on any common tail, in particular their maximum. -/
  coefficients : ∀ (k m : ℕ) (hkm : k ≤ m),
    ∃ q : B R s m ⟶ B R s k,
      quotient R s m ≫ q = quotient R s k ∧
      ∃ e : (M.scalar m).E ⋙ restriction R s m ⟶
          (M.scalar k).E ⋙ restriction R s k,
        (∀ (P : Modules R) (U : Cᵒᵖ) (b : (B R s m).obj.obj U) (x : P.val.obj U),
          (e.app P).val.app U (pure R s m (M.scalar m) P U b x) =
            pure R s k (M.scalar k) P U ((q.hom.app U).hom b) x) ∧
        ∃ c : (M.scalar m).T ⋙ (restriction R s m).mapDerivedCategory ⟶
            (M.scalar k).T ⋙ (restriction R s k).mapDerivedCategory,
          (∀ (P : CochainComplex (Modules R) ℤ),
            CochainComplex.IsKFlatIndependentCoefficients (R := R) P →
            c.app (DerivedCategory.Q.obj P) ≫
                (restriction R s k).mapDerivedCategory.map ((M.scalar k).ε.app P) ≫
                (restriction R s k).mapDerivedCategoryFactors.hom.app
                  (((M.scalar k).E.mapHomologicalComplex (.up ℤ)).obj P) =
              (restriction R s m).mapDerivedCategory.map ((M.scalar m).ε.app P) ≫
                (restriction R s m).mapDerivedCategoryFactors.hom.app
                  (((M.scalar m).E.mapHomologicalComplex (.up ℤ)).obj P) ≫
                DerivedCategory.Q.map
                  ((ordinaryTransition R s (M.scalar m) (M.scalar k) e).app P)) ∧
          (∀ P : CochainComplex (Modules R) ℤ,
            (tensorStep R s hkm).app P ≫ (M.aug k).app P =
              (M.aug m).app P ≫ (ordinaryTransition R s (M.scalar m) (M.scalar k) e).app P) ∧
          (∀ P : CochainComplex (Modules R) ℤ,
            DerivedCategory.Q.map ((tensorStep R s hkm).app P) ≫ (M.A k).hom.app P =
              (M.A m).hom.app P ≫ c.app (DerivedCategory.Q.obj P)) ∧
          (∀ (X : CochainComplex (ℕᵒᵖ ⥤ Modules R) ℤ) (h : ℕ),
            c.app (M.RF.obj (DerivedCategory.Q.obj X)) ≫ M.comparison R s X k h =
              M.comparison R s X m h ≫ M.RF.map (DerivedCategory.Q.map
                ((tail R h).map ((onTowersMap R (tensorStep R s hkm)).app X))))
  /-- The comparison is natural in strict maps of towers. -/
  natural : ∀ {X Y : CochainComplex (ℕᵒᵖ ⥤ Modules R) ℤ} (f : X ⟶ Y) (m h : ℕ),
    ((M.scalar m).T ⋙ (restriction R s m).mapDerivedCategory).map
        (M.RF.map (DerivedCategory.Q.map f)) ≫ M.comparison R s Y m h =
      M.comparison R s X m h ≫ M.RF.map (DerivedCategory.Q.map
        ((tail R h).map ((onTowers R (tensor R s m)).map f)))
  /-- Uniform cohomological bounds gain at most one degree under derived limit. -/
  bounded : ∀ (X : CochainComplex (ℕᵒᵖ ⥤ Modules R) ℤ) (a b : ℤ),
    (∀ (n : ℕ) (q : ℤ), q < a ∨ b < q →
      IsZero ((DerivedCategory.homologyFunctor (Modules R) q).obj
        (DerivedCategory.Q.obj (X.asFunctor.obj (op n))))) →
    ∀ q : ℤ, q < a ∨ b + 1 < q →
      IsZero ((DerivedCategory.homologyFunctor (Modules R) q).obj
        (M.RF.obj (DerivedCategory.Q.obj X)))


/-- The full comparison assertion, including the available sheafification structure.
The existential sheafification proof is an implementation choice for the small site,
not an additional hypothesis on the scheme or coefficient ring.
Source: Stacks 0941 and the blueprint tower proof paragraph 1
(blueprint: lem-sp-koszul-roos-projection-comparison). -/
def Conclusion : Prop :=
  ∃ i : HasSheafify J CommRingCat.{r},
    letI := i
    ∃ M : Models R s, Compatibility R s M

/-- Koszul tensor and finite-tail comparison preserve the actual Roos projections,
strict augmentation adjoints, coefficient transitions, and uniform cohomological bounds.
The coefficient universe contains the small pro-etale site; its object and morphism
universes remain independent. The localization instances only select morphism sizes.

Source: blueprint main-20261015, sec-smooth-purity/sk-lem-sp-tower.proof.md,
paragraph 1; Bhatt--Scholze, Sections 3.1 and 3.5; Stacks 0941, 06YY and 09T5.
(blueprint: lem-sp-koszul-roos-projection-comparison)

Proof, following all thirteen DAG steps:

1. Work on the small pro-étale site in a module universe containing its objects. Countable
products of $R$-module sheaves are sectionwise and exact by
[lem-weil-proetale-countable-products-exact], for arbitrary $T$. Exactness implies $H^q(\prod
X_n)=\prod H^q(X_n)$: the product functor preserves the kernels and images defining cohomology.
Choose individual K-injective resolutions using [prop-pur-kinjective-resolutions-exist]. Their
product represents the derived product by [lem-pc-ringed-space-product-kinjective], and the map
from the product of the original complexes is a quasi-isomorphism by the preceding cohomology
equality. Thus termwise products represent derived products. The normalized natural comparison
[lem-weil-strict-roos-comparison] identifies the strict Roos fibre with the actual $H=R\!\lim
X_\bullet$, carries its coordinate maps to $p_n$, and identifies strict maps of Roos fibres with
derived-limit maps. We use this normalization throughout, also after reindexing a tail by
$\mathbf N_{\geq1}$. Dependencies: lem-weil-proetale-countable-products-exact,
prop-pur-kinjective-resolutions-exist, lem-pc-ringed-space-product-kinjective,
lem-weil-strict-roos-comparison.

2. Fix the following coordinates, using [def-weil-abstract-derived-category] and
[def-pc-tensor-complex-sheaves]. For a chain endomorphism $u:P\to P$, write $F_u^q=P^q\oplus
P^{q-1}$ with $d(x,y)=(dx,ux-dy)$. The map $(x,y)\mapsto(-y,x)$ identifies this with
$\operatorname{Cone}(u)[-1]$; projection is $(x,y)\mapsto x$. Put $D_m(C)=C\otimes_RK_m$. In
degree $q$ write its coordinates as $(a,b)\in C^q\oplus C^{q+1}$. The total differential is
$d(a,b)=(da+(-1)^{q+1}t^m b,db)$. Consequently $(a,b)\mapsto(a,(-1)^{q+1}b)$ is a chain
isomorphism $D_m(C)\cong\operatorname{Cone}(t^m:C\to C)$, carrying the inclusion of $C$ to the
cone inclusion and the augmentation to $a\mapsto a\otimes1$. These formulas fix all signs used
below. Dependencies: def-weil-abstract-derived-category, def-pc-tensor-complex-sheaves.

3. Multiplication by $t^m$ is injective, being a composite of $m$ injective maps, and $B_m$ is
its sheaf cokernel. Hence $0\to R\xrightarrow{t^m}R\to B_m\to0$ is exact. Apply
[lem-cbc-regular-quotient-cone-augmentation] with $r=t^m$ and $S=B_m$. Together with the
coordinate isomorphism in step 2 this gives a natural isomorphism
$A_{m,C}:QD_m(C)\xrightarrow{\sim}\operatorname{Res}(QC\otimes_R^LB_m)$. For a K-flat $P$,
$A_{m,P}$ is represented by the augmentation $P\otimes K_m\to\operatorname{Res}(P\otimes B_m)$,
and the inclusion $P\to D_m(P)$ becomes $p\mapsto p\otimes1$. The derived scalar extension is
computed on these resolutions by [lem-pur-derived-change-of-rings]. The same cited cone theorem
gives naturality for all derived morphisms and resolution independence. In particular $D_m$
preserves quasi-isomorphisms, since its localized cone functor exists on $D(R)$, or directly by
the cone cohomology sequence. Dependencies: lem-cbc-regular-quotient-cone-augmentation,
lem-pur-derived-change-of-rings.

4. Delete the coordinates $n<h$ in both copies of the product. This strictly commutes with
$1-s$, hence defines $F_{1-s}(\prod_{n\geq1}X_n)\to F_{1-s}(\prod_{n\geq h}X_n)$. It is
degreewise split surjective, and its kernel is $F_U(P_{<h})$, where $P_{<h}=\prod_{1\leq
n<h}X_n$, $U=1-s_{<h}$, and the shift on the finite prefix has zero last component. It is
nilpotent: $s_{<h}^{h-1}=0$ for $h>1$. Thus $U^{-1}=\sum_{j=0}^{h-2}s_{<h}^j$. On the kernel the
degree $-1$ map $(x,y)\mapsto(U^{-1}y,0)$ satisfies $dH+Hd=1$, since $U$ commutes with $d$. The
kernel is therefore acyclic. The long exact sequence
[lem-weil-pbc-complex-ses-homology-long-exact] proves the deletion map is a quasi-isomorphism.
For $h=1$ it is the identity and its kernel is zero. Every retained projection is unchanged
literally. Dependencies: def-weil-abstract-derived-category,
lem-weil-pbc-complex-ses-homology-long-exact.

5. Let $P=\prod_nX_n$. The canonical map $D_m(P)\to\prod_nD_m(X_n)$ is the chain isomorphism $(
(a_n)_n,(b_n)_n )\mapsto((a_n,b_n))_n$. Its inverse takes the two coordinate families. This is a
sheaf map: products are sectionwise and only two summands occur in every total degree. The
differential in step 2 is componentwise, so this permutation commutes with $d$. If
$s((a_n))=(v_na_{n+1})$ for the transition maps $v_n$, it also commutes with $s$ and therefore
with $1-s$. It commutes with every product projection, all strict tower maps, and deletion of
any prefix, as each of these acts on the same coordinates. Dependencies:
def-pc-tensor-complex-sheaves, lem-weil-proetale-countable-products-exact.

6. Tensor the fibre coordinates of step 2. For any $u:P\to P$, a degree $q$ element of
$D_m(F_u)$ has coordinates $(x,y,z,w)\in P^q\oplus P^{q-1}\oplus P^{q+1}\oplus P^q$. Send it to
$((x,z),(y,w))\in F_{D_m(u)}^q$. Both differentials, in the target ordering, are
$$((dx+(-1)^{q+1}t^m z,dz),(ux-dy+(-1)^{q+1}t^m w,uz-dw)).$$ Thus this permutation is a chain
isomorphism $D_m(F_u)\cong F_{D_m(u)}$. It commutes with the first-coordinate projections to
$D_m(P)$ and with maps commuting with $u$. Combining it for $u=1-s$ with step 5 gives a natural
chain isomorphism $D_m(\mathsf R(X))\cong\mathsf R(D_m(X))$ that retains every projection. No
infinite totalization is being interchanged with a product. Dependencies:
def-pc-tensor-complex-sheaves, def-weil-abstract-derived-category.

7. Represent $H$ by $Q\mathsf R(X)$ using step 1. Start with $A_{m,\mathsf R(X)}^{-1}$ from step
3, apply the chain isomorphism of step 6, delete the prefix by step 4 applied to the strict
tower $D_m(X_n)$, and use [lem-weil-strict-roos-comparison] on that tail. The composite is the
asserted isomorphism from $\operatorname{Res}(H\otimes_R^LB_m)$ to $R\!\lim_{n\geq h}D_m(X_n)$.
Its composite with projection to level $n$ is $D_m(p_n)$ after $A_m^{-1}$: this holds at chain
level in steps 4–6 and for the normalized derived-limit comparison in step 1. Naturality of
$A_m$ says exactly that this is the restriction of the derived tensor of $p_n$, followed by the
stated two-term comparison. Dependencies: lem-weil-strict-roos-comparison,
lem-cbc-regular-quotient-cone-augmentation.

8. For the constant tail $N$, put $P_N=\prod_{n\geq m}N$ and $u=1-s$. Define $v:P_N\to P_N$ by
$(vz)_m=0$ and $(vz)_n=-\sum_{j=m}^{n-1}z_j$ for $n>m$. These are finite sums, so define sheaf
maps and commute with $d$. One has $uv=1$ and $x=\operatorname{diag}(x_m)+vux$. Hence $P_N\cong
N\oplus P_N$ by $x\mapsto(x_m,ux)$, and $F_u\cong N\oplus F_{1_{P_N}}$ by
$(x,y)\mapsto(x_m,(ux,y))$. The second factor contracts by $(a,b)\mapsto(b,0)$. Therefore
$e:F_u\to N$, $(x,y)\mapsto x_m$, is inverse in the derived category to the diagonal $N\to F_u$,
$z\mapsto(\operatorname{diag}z,0)$. This fixes the diagonal identification required in the
statement. Dependencies: def-weil-abstract-derived-category.

9. Now put $h=m$. The augmentations $D_m(X_n)\to X_n\otimes B_m$ commute strictly with
transitions. The assumed compatibility of $f_n$ makes their composites
$g_n:D_m(X_n)\to\operatorname{Res}N$ a strict map to the constant tail. Under the normalized
comparison [lem-weil-strict-roos-comparison], their derived-limit map is exactly the
coordinatewise map of Roos fibres. Applying $e$ from step 8 selects its first product component
at $m$. Consequently the complete composite of the statement, on the model $D_m(\mathsf R(X))$,
is $$D_m(\mathsf
R(X))\xrightarrow{D_m(p_m)}D_m(X_m)\xrightarrow{\mathrm{aug}}X_m\otimes_RB_m
\xrightarrow{f_m}\operatorname{Res}N.$$
This is an equality of the indicated chain maps, not an inference that arbitrary morphisms into
a homotopy limit are determined by their projections. Dependencies:
lem-weil-strict-roos-comparison, def-pc-tensor-complex-sheaves.

10. Choose a K-flat resolution $q:P\to\mathsf R(X)$ by [lem-pc-kflat-resolution]. Ordinary
scalar extension and restriction on complexes have the specified adjunction
[def-weil-pbc-ringed-scalar-extension-complex-adjunction], with unit $p\mapsto p\otimes1$ by
[def-weil-pbc-ringed-tensor-section-calculus]. Derive it using
[lem-pc-derived-adjoint-functors], [lem-pur-derived-change-of-rings], and exact restriction
[lem-sf-exact-functor-derived-triangulated]: kernels and sheafified cokernels have unchanged
underlying abelian sheaves [def-weil-sheaf-of-modules-category]. On $P$, the map
$H\to\operatorname{Res}N$ in the statement is represented by $p\mapsto f_m(p_mq(p)\otimes1)$.
Its adjoint is represented on $P\otimes B_m$ by $p\otimes b\mapsto b f_m(p_mq(p)\otimes1)$.
After the augmentation $D_m(P)\to P\otimes B_m$ this sends $(a,b)$ to $f_m(p_mq(a)\otimes1)$,
exactly the map in step 9 precomposed with $D_m(q)$. Both $D_m(q)$ and this augmentation are
quasi-isomorphisms, by steps 2–3. The normalization of
[lem-cbc-regular-quotient-cone-augmentation] identifies this roof with $A_m^{-1}$. Thus the
equality is precisely the restriction of the derived adjoint asserted, including its unit
normalization. Dependencies: lem-pc-kflat-resolution,
def-weil-pbc-ringed-scalar-extension-complex-adjunction,
def-weil-pbc-ringed-tensor-section-calculus, lem-pc-derived-adjoint-functors,
lem-pur-derived-change-of-rings, lem-sf-exact-functor-derived-triangulated,
def-weil-sheaf-of-modules-category, lem-cbc-regular-quotient-cone-augmentation.

11. Restriction along $R\to B_m$ preserves and reflects vanishing of cohomology: it leaves the
underlying abelian sheaves unchanged and is exact, by [def-pc-sheaf-restrict-scalars] and the
kernel/cokernel description [def-weil-sheaf-of-modules-category]. It is triangulated by
[lem-sf-exact-functor-derived-triangulated]. If the restriction of a derived morphism $a:A\to B$
is invertible, its cone restricts to zero, so that cone is acyclic and hence zero in the derived
category. In the triangle $A\xrightarrow a B\to0\to A[1]$, exactness of
$\operatorname{Hom}(B,-)$ from [lem-weil-pbc-hom-into-triangle-exact] supplies $r$ with $ar=1$.
In the backward rotation $0[-1]\to A\xrightarrow a B\to0$, the same exactness with source $A$
gives $ra-1=0$ since $a(ra-1)=0$. Thus $a$ is invertible. This proves detection of isomorphisms
without asserting faithfulness or fullness of derived restriction. Dependencies:
def-pc-sheaf-restrict-scalars, def-weil-sheaf-of-modules-category,
lem-sf-exact-functor-derived-triangulated, lem-weil-pbc-hom-into-triangle-exact,
def-weil-abstract-derived-category.

12. For $k\leq m$, the map $K_m\to K_k$ has components $t^{m-k}$ in degree $-1$ and $1$ in
degree $0$. It is a chain map because $t^k t^{m-k}=t^m$, and it commutes with the augmentations
via $B_m\to B_k$. On $D_m(C)^q$ it sends $(a,b)$ to $(a,t^{m-k}b)$. On $P\otimes B_m$, for a
single K-flat resolution $P$, the corresponding map is $p\otimes\bar r\mapsto p\otimes\bar r$
modulo $t^k$. The augmentation square therefore commutes on both summands. By
[lem-pur-derived-change-of-rings] these are the coefficient quotient transitions; step 3
identifies their restrictions with the displayed $K$-maps. The permutations in steps 5–6 and
tail deletion act on independent coordinates and commute with these maps. Compare different
tails on the common tail $n\geq\max(h_m,h_k)$; the deletion maps compose literally. All
resulting derived comparison squares commute. For $j\leq k\leq m$ the degree $-1$ components
compose because $t^{k-j}t^{m-k}=t^{m-j}$; identity transitions have components $(1,1)$. If
compatible target families are also varied, the formulas of steps 9–10 give the corresponding
naturality square on the same resolution. Dependencies: def-pc-tensor-complex-sheaves,
lem-pur-derived-change-of-rings, lem-cbc-regular-quotient-cone-augmentation.

13. Finally suppose $H^q(X_n)=0$ for all $q\notin[a,b]$ and all $n$. Exact products give
$H^q(P)=\prod_nH^q(X_n)$ as in step 1, so $P=\prod X_n$ has the same cohomological bound. In the
Roos triangle $H\to P\xrightarrow{1-s}P\to H[1]$, use [lem-sf-derived-homology-long-exact]: the
segment $H^{q-1}(P)\to H^q(H)\to H^q(P)$ has both outside terms zero for $q<a$ or $q>b+1$. Thus
$H^q(H)=0$ there, proving the interval $[a,b+1]$. The product exactness statement used here
holds for every scheme, and none of the coordinate calculations imposed quasi-compactness on
$T$. Dependencies: lem-weil-proetale-countable-products-exact, lem-weil-strict-roos-comparison,
lem-sf-derived-homology-long-exact.
-/
theorem koszulRoosProjectionComparison (T : AlgebraicGeometry.Scheme.{t})
    [EssentiallySmall.{t + 1} T.ProEt]
    (R : Sheaf (AlgebraicGeometry.Scheme.ProEt.topology T) CommRingCat.{max z (t + 1)})
    (s : (R.obj ⋙ forget CommRingCat.{max z (t + 1)}).sections)
    [∀ S : Sheaf (AlgebraicGeometry.Scheme.ProEt.topology T) CommRingCat.{max z (t + 1)},
      HasDerivedCategory.{w} (Modules S)]
    [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ Modules R)]
    (_hs : Mono (globalSectionMultiplication R (unitSection R s))) :
    Conclusion R s := by
  sorry

end CategoryTheory.KoszulRoos
