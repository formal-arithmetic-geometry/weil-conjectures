/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group O3
-/
module

public import Sheaf.CategoryTheory.StrictRoosModel
public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import Mathlib.CategoryTheory.Functor.OfSequence
import Sheaf.CategoryTheory.StrictRoosHomotopyFunctor
import Sheaf.CategoryTheory.StrictRoosAdditiveComparison
import Sheaf.AlgebraicGeometry.ProEtaleProductsExact
import all Sheaf.CategoryTheory.StrictRoosDerivation
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import Sheaf.CategoryTheory.StrictRoosDerivedLimitComparison
import all Sheaf.CategoryTheory.StrictRoosModel
import all Mathlib.Algebra.Homology.Functor
import all Mathlib.CategoryTheory.Limits.HasLimits
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-! # Augmented scalar Roos comparison with resolution-normalized units
Source: blueprint main-20261015, sec-six-functors-basics, sk-lem-int-tensor,
det-lem-int-tensor-pullback.proof.md, first and final paragraphs; Stacks Tags 0941,
07KC and 070I (blueprint: lem-sfb-augmented-scalar-roos-resolution).
The cone, product, coordinates and augmentations are the existing strict Roos model.
The public predicates below merely collect the coordinate and normalization equations
of this node. In particular, the derived comparison is tied to the universal unit,
including computations using a separate constant-tower resolution.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u v uB vB w t r

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.AugmentedScalarRoos

section Formulas

variable {A : Type u} [Category.{v} A] [Abelian A] [HasCountableProducts A]

/-- The product of the components of a transition-compatible homotopy, using the
canonical degreewise product comparison. Source: Stacks 0941 and the signed homotopy
calculation in proof step 3 (blueprint: lem-sfb-augmented-scalar-roos-resolution). -/
def productHomotopy {X Y : CochainComplex (ℕᵒᵖ ⥤ A) ℤ} {f g : X ⟶ Y}
    (h : Homotopy f g) (p q : ℤ) : (roosP X).X p ⟶ (roosP Y).X q :=
  (PreservesProduct.iso (HomologicalComplex.eval A (.up ℤ) p)
      (fun n : ℕ ↦ X.asFunctor.obj (op n))).hom ≫
    Limits.Pi.map (fun n : ℕ ↦ (h.hom p q).app (op n)) ≫
      (PreservesProduct.iso (HomologicalComplex.eval A (.up ℤ) q)
        (fun n : ℕ ↦ Y.asFunctor.obj (op n))).inv

/-- The coordinate clauses over a single coefficient ring. Source: the explicit
signed cone, strict-map, homotopy and augmentation computations of proof steps 2--4
(blueprint: lem-sfb-augmented-scalar-roos-resolution). -/
def ChainFormulas : Prop :=
  (∀ (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (p : ℤ),
    (roosF.obj X).d (p + 1) (p + 1 + 1) ≫ (roosχ X (p + 1)).hom =
      (roosχ X p).hom ≫
        biprod.lift
          (biprod.fst ≫ (-((roosP X).d p (p + 1))) +
            biprod.snd ≫ (-((roosU X).f (p + 1))))
          (biprod.snd ≫ (roosP X).d (p + 1) (p + 1 + 1))) ∧
  (∀ {X Y : CochainComplex (ℕᵒᵖ ⥤ A) ℤ} (f : X ⟶ Y) (p : ℤ),
    (roosF.map f).f (p + 1) ≫ (roosχ Y p).hom =
      (roosχ X p).hom ≫ biprod.map ((roosPmap f).f p) ((roosPmap f).f (p + 1))) ∧
  (∀ {X Y : CochainComplex (ℕᵒᵖ ⥤ A) ℤ} (f : X ≅ Y) (p : ℤ),
    (roosF.mapIso f).inv.f (p + 1) ≫ (roosχ X p).hom =
      (roosχ Y p).hom ≫
        biprod.map ((roosPmap f.inv).f p) ((roosPmap f.inv).f (p + 1))) ∧
  (∀ {X Y : CochainComplex (ℕᵒᵖ ⥤ A) ℤ} {f g : X ⟶ Y} (h : Homotopy f g),
    ∃ H : Homotopy (roosF.map f) (roosF.map g), ∀ p : ℤ,
      H.hom (p + 1) (p - 1 + 1) ≫ (roosχ Y (p - 1)).hom =
        (roosχ X p).hom ≫
          biprod.map (-productHomotopy h p (p - 1)) (productHomotopy h (p + 1) (p - 1 + 1))) ∧
  (∀ {X Y : CochainComplex (ℕᵒᵖ ⥤ A) ℤ} {L M : CochainComplex A ℤ}
    (b : ∀ n : ℕ, L ⟶ X.asFunctor.obj (op n))
    (hb : ∀ n, b (n + 1) ≫ X.asFunctor.map (homOfLE (Nat.le_succ n)).op = b n)
    (b' : ∀ n : ℕ, M ⟶ Y.asFunctor.obj (op n))
    (hb' : ∀ n, b' (n + 1) ≫ Y.asFunctor.map (homOfLE (Nat.le_succ n)).op = b' n)
    (f : X ⟶ Y) (v : L ⟶ M),
    (∀ n, b n ≫ (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map f).app
      (op n) = v ≫ b' n) →
    roosAugment b hb ≫ roosF.map f = v ≫ roosAugment b' hb') ∧
  (∀ (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (L : CochainComplex A ℤ)
    (b : ∀ n : ℕ, L ⟶ X.asFunctor.obj (op n))
    (hb : ∀ n, b (n + 1) ≫ X.asFunctor.map (homOfLE (Nat.le_succ n)).op = b n)
    (p : ℤ),
    (roosAugment b hb).f (p + 1) ≫ (roosχ X p).hom =
      biprod.lift 0 ((Pi.lift b).f (p + 1)))

/-- The two-coordinate formula for scalar comparison, using only the canonical
biproduct comparison and the specified product comparison. Source: proof step 2
(blueprint: lem-sfb-augmented-scalar-roos-resolution). -/
def ConeCoordinates {B : Type uB} [Category.{vB} B] [Abelian B]
    [HasCountableProducts B] (F : A ⥤ B) [F.Additive]
    (T : CochainComplex (ℕᵒᵖ ⥤ A) ℤ ⥤ CochainComplex (ℕᵒᵖ ⥤ B) ℤ)
    (P : ∀ X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ,
      (F.mapHomologicalComplex (.up ℤ)).obj (roosP X) ≅ roosP (T.obj X))
    (c : ∀ X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ,
      (F.mapHomologicalComplex (.up ℤ)).obj (roosF.obj X) ≅ roosF.obj (T.obj X)) : Prop :=
  ∀ (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (p : ℤ),
    (c X).hom.f (p + 1) ≫ (roosχ (T.obj X) p).hom =
      F.map (roosχ X p).hom ≫
        Functor.biprodComparison F ((roosP X).X p) ((roosP X).X (p + 1)) ≫
          biprod.map ((P X).hom.f p) ((P X).hom.f (p + 1))

/-- The constant strict tower of a complex, using Mathlib's constant functor degreewise.
Source: the constant-tower unit in proof steps 6--7
(blueprint: lem-sfb-augmented-scalar-roos-resolution). -/
abbrev constantTower (L : CochainComplex A ℤ) : CochainComplex (ℕᵒᵖ ⥤ A) ℤ :=
  ((Functor.const ℕᵒᵖ).mapHomologicalComplex (.up ℤ)).obj L

variable [HasLimitsOfShape ℕᵒᵖ A]
  [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ A)]

/-- Normalization by every K-injective tower resolution, the actual universal
augmented map, and a separate constant-tower resolution commuting only up to homotopy.
The augmentation equation uses the universal unit at X after the ordinary limit lift;
by naturality this is exactly the constant-tower unit followed by derived limit of b.
Source: Stacks 0941 and 070I; proof steps 5--7
(blueprint: lem-sfb-augmented-scalar-roos-resolution). -/
def ResolutionNormalized
    (RF : DerivedCategory.{w} (ℕᵒᵖ ⥤ A) ⥤ DerivedCategory.{w} A)
    (η : roosLimitFunctor ⋙ DerivedCategory.Q.{w} ⟶ DerivedCategory.Q.{w} ⋙ RF)
    (ρ : roosF ⋙ DerivedCategory.Q.{w} ≅ DerivedCategory.Q.{w} ⋙ RF) : Prop :=
  (∀ (X I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (q : X ⟶ I)
    (_hq : QuasiIso q) (_hI : I.IsKInjective),
    QuasiIso (roosF.map q) ∧ QuasiIso (roosι I) ∧
    ∃ (ε : DerivedCategory.Q.{w}.obj (limit I.asFunctor) ≅
        DerivedCategory.Q.{w}.obj (roosF.obj I))
      (d : DerivedCategory.Q.{w}.obj (limit I.asFunctor) ≅
        RF.obj (DerivedCategory.Q.{w}.obj X)),
      ε.hom = DerivedCategory.Q.{w}.map (roosι I) ∧
      d.hom ≫ RF.map (DerivedCategory.Q.{w}.map q) = η.app I ∧
      ρ.hom.app X = DerivedCategory.Q.{w}.map (roosF.map q) ≫ ε.inv ≫ d.hom) ∧
  (∀ (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (L : CochainComplex A ℤ)
    (b : ∀ n : ℕ, L ⟶ X.asFunctor.obj (op n))
    (hb : ∀ n, b (n + 1) ≫ X.asFunctor.map (homOfLE (Nat.le_succ n)).op = b n),
    DerivedCategory.Q.{w}.map (roosAugment b hb) ≫ ρ.hom.app X =
      DerivedCategory.Q.{w}.map (roosAugmentLimit b hb) ≫ η.app X) ∧
  (∀ (X I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (L : CochainComplex A ℤ)
    (b : constantTower L ⟶ X)
    (γ : ∀ n : ℕ, L ⟶ X.asFunctor.obj (op n))
    (hγ : ∀ n, γ (n + 1) ≫ X.asFunctor.map (homOfLE (Nat.le_succ n)).op = γ n)
    (_hγb : ∀ n, γ n =
      (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map b).app (op n))
    (q : X ⟶ I) (_hq : QuasiIso q) (_hI : I.IsKInjective)
    (J : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (p : constantTower L ⟶ J)
    (_hp : QuasiIso p) (_hJ : J.IsKInjective) (a : J ⟶ I)
    (_h : Homotopy (p ≫ a) (b ≫ q))
    (d : DerivedCategory.Q.{w}.obj (limit I.asFunctor) ≅
      RF.obj (DerivedCategory.Q.{w}.obj X))
    (_hd : d.hom ≫ RF.map (DerivedCategory.Q.{w}.map q) = η.app I)
    (lam : L ⟶ limit J.asFunctor)
    (_hlam : ∀ n : ℕ, lam ≫ limit.π J.asFunctor (op n) =
      (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map p).app (op n)),
    DerivedCategory.Q.{w}.map lam ≫
        DerivedCategory.Q.{w}.map
          (lim.map (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map a)) ≫
        d.hom = DerivedCategory.Q.{w}.map (roosAugment γ hγ) ≫ ρ.hom.app X)

/-- Termwise application of an additive functor to strict tower complexes.
Source: the strict scalar functor of proof steps 1--2
(blueprint: lem-sfb-augmented-scalar-roos-resolution). -/
abbrev mapTower {B : Type uB} [Category.{vB} B] [Abelian B]
    (F : A ⥤ B) [F.Additive] :
    CochainComplex (ℕᵒᵖ ⥤ A) ℤ ⥤ CochainComplex (ℕᵒᵖ ⥤ B) ℤ :=
  ((Functor.whiskeringRight ℕᵒᵖ A B).obj F).mapHomologicalComplex (.up ℤ)

/-- The scalar, chain and derived equations of this node, on its actual coefficient
categories and actual restriction functor. This transparent predicate packages the
clauses to avoid repeatedly unfolding sheaf-category structures during elaboration.
Source: blueprint det-lem-int-tensor-pullback, first and final paragraphs; the nine
explicit steps of the node (blueprint: lem-sfb-augmented-scalar-roos-resolution). -/
def ScalarFormulas {B : Type uB} [Category.{vB} B] [Abelian B]
    [HasCountableProducts B] [HasLimitsOfShape ℕᵒᵖ B]
    [HasDerivedCategory.{w} B] [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ B)]
    (F : A ⥤ B) [F.Additive]
    (RF_R : DerivedCategory.{w} (ℕᵒᵖ ⥤ A) ⥤ DerivedCategory.{w} A)
    (ηR : roosLimitFunctor (A := A) ⋙ DerivedCategory.Q.{w} (C := A) ⟶
      DerivedCategory.Q.{w} (C := ℕᵒᵖ ⥤ A) ⋙ RF_R)
    (RF_C : DerivedCategory.{w} (ℕᵒᵖ ⥤ B) ⥤ DerivedCategory.{w} B)
    (ηC : roosLimitFunctor (A := B) ⋙ DerivedCategory.Q.{w} (C := B) ⟶
      DerivedCategory.Q.{w} (C := ℕᵒᵖ ⥤ B) ⋙ RF_C) : Prop :=
  PreservesFiniteLimits F ∧
  PreservesFiniteColimits F ∧
  PreservesFiniteBiproducts F ∧
  ChainFormulas (A := A) ∧ ChainFormulas (A := B) ∧
  ∃ (P : ∀ W : CochainComplex (ℕᵒᵖ ⥤ A) ℤ,
      (F.mapHomologicalComplex (.up ℤ)).obj (roosP W) ≅ roosP ((mapTower F).obj W))
    (c : ∀ W : CochainComplex (ℕᵒᵖ ⥤ A) ℤ,
      (F.mapHomologicalComplex (.up ℤ)).obj (roosF.obj W) ≅ roosF.obj ((mapTower F).obj W))
    (ρR : roosF (A := A) ⋙ DerivedCategory.Q.{w} (C := A) ≅
      DerivedCategory.Q.{w} (C := ℕᵒᵖ ⥤ A) ⋙ RF_R)
    (ρC : roosF (A := B) ⋙ DerivedCategory.Q.{w} (C := B) ≅
      DerivedCategory.Q.{w} (C := ℕᵒᵖ ⥤ B) ⋙ RF_C)
    (Dr : DerivedCategory.{w} A ⥤ DerivedCategory.{w} B)
    (φ : DerivedCategory.Q.{w} (C := A) ⋙ Dr ≅
      F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q.{w} (C := B))
    (β : ∀ W : CochainComplex (ℕᵒᵖ ⥤ A) ℤ, Dr.obj (RF_R.obj (DerivedCategory.Q.{w}.obj W)) ≅
      RF_C.obj (DerivedCategory.Q.{w}.obj ((mapTower F).obj W))),
    (∀ (W : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (n : ℕ),
      (P W).hom ≫ Pi.π
        (fun k : ℕ ↦ ((mapTower F).obj W).asFunctor.obj (op k)) n =
      (F.mapHomologicalComplex (.up ℤ)).map (Pi.π (fun k : ℕ ↦ W.asFunctor.obj (op k)) n)) ∧
    (∀ W : CochainComplex (ℕᵒᵖ ⥤ A) ℤ,
      (F.mapHomologicalComplex (.up ℤ)).map (roosU W) ≫ (P W).hom =
        (P W).hom ≫ roosU ((mapTower F).obj W)) ∧
    ConeCoordinates F (mapTower F) P c ∧
    (∀ {W V : CochainComplex (ℕᵒᵖ ⥤ A) ℤ} (f : W ⟶ V),
      (F.mapHomologicalComplex (.up ℤ)).map (roosF.map f) ≫ (c V).hom =
        (c W).hom ≫ roosF.map ((mapTower F).map f)) ∧
    ResolutionNormalized RF_R ηR ρR ∧ ResolutionNormalized RF_C ηC ρC ∧
    (∀ W : CochainComplex (ℕᵒᵖ ⥤ A) ℤ,
      (β W).hom = Dr.map (ρR.inv.app W) ≫ φ.hom.app (roosF.obj W) ≫
        DerivedCategory.Q.{w}.map (c W).hom ≫
          ρC.hom.app ((mapTower F).obj W)) ∧
    (∀ {W V : CochainComplex (ℕᵒᵖ ⥤ A) ℤ} (f : W ⟶ V),
      Dr.map (RF_R.map (DerivedCategory.Q.{w}.map f)) ≫ (β V).hom =
        (β W).hom ≫ RF_C.map (DerivedCategory.Q.{w}.map ((mapTower F).map f))) ∧
    (∀ (W : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (W' : CochainComplex (ℕᵒᵖ ⥤ B) ℤ)
      (L : CochainComplex A ℤ) (L' : CochainComplex B ℤ)
      (b : ∀ n : ℕ, L ⟶ W.asFunctor.obj (op n))
      (hb : ∀ n, b (n + 1) ≫ W.asFunctor.map (homOfLE (Nat.le_succ n)).op = b n)
      (b' : ∀ n : ℕ, L' ⟶ W'.asFunctor.obj (op n))
      (hb' : ∀ n, b' (n + 1) ≫ W'.asFunctor.map (homOfLE (Nat.le_succ n)).op = b' n)
      (f : (mapTower F).obj W ⟶ W') (v : (F.mapHomologicalComplex (.up ℤ)).obj L ⟶ L'),
      (∀ n : ℕ, (F.mapHomologicalComplex (.up ℤ)).map (b n) ≫
        (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map f).app (op n) =
          v ≫ b' n) →
      ((F.mapHomologicalComplex (.up ℤ)).map (roosAugment b hb) ≫ (c W).hom ≫ roosF.map f =
        v ≫ roosAugment b' hb') ∧
      (Dr.map (DerivedCategory.Q.{w}.map (roosAugment b hb) ≫ ρR.hom.app W) ≫
          (β W).hom ≫ RF_C.map (DerivedCategory.Q.{w}.map f) =
        φ.hom.app L ≫ DerivedCategory.Q.{w}.map v ≫
          DerivedCategory.Q.{w}.map (roosAugment b' hb') ≫ ρC.hom.app W'))

end Formulas

section Scalars

variable (Z : AlgebraicGeometry.Scheme.{t})

/-- The recorded category of modules on the small pro-etale site, without changing
its objects or morphisms. Source: the scalar-restriction setup of proof step 1
(blueprint: lem-sfb-augmented-scalar-roos-resolution). -/
abbrev Modules (R : Sheaf (AlgebraicGeometry.Scheme.ProEt.topology Z)
    RingCat.{max r (t + 1)}) := ringedSiteModules.{max r (t + 1)} R

end Scalars

end CategoryTheory.AugmentedScalarRoos

namespace CategoryTheory
open AugmentedScalarRoos

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

section Helpers

variable {A : Type u} [Category.{v} A] [Abelian A] [HasCountableProducts A]

private theorem augment_natural {X Y : CochainComplex (ℕᵒᵖ ⥤ A) ℤ}
    {L M : CochainComplex A ℤ}
    (b : ∀ n : ℕ, L ⟶ X.asFunctor.obj (op n))
    (hb : ∀ n, b (n + 1) ≫ X.asFunctor.map (homOfLE (Nat.le_succ n)).op = b n)
    (b' : ∀ n : ℕ, M ⟶ Y.asFunctor.obj (op n))
    (hb' : ∀ n, b' (n + 1) ≫ Y.asFunctor.map (homOfLE (Nat.le_succ n)).op = b' n)
    (f : X ⟶ Y) (v : L ⟶ M)
    (h : ∀ n, b n ≫ (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map f).app
      (op n) = v ≫ b' n) :
    roosAugment b hb ≫ roosF.map f = v ≫ roosAugment b' hb' := by
  ext k
  obtain ⟨p, rfl⟩ : ∃ p : ℤ, k = p + 1 := ⟨k - 1, by omega⟩
  apply (cancel_mono (roosχ Y p).hom).1
  simp only [HomologicalComplex.comp_f, Category.assoc, roosF_map_χ,
    roosAugment_χ, reassoc_of% roosAugment_χ]
  apply biprod.hom_ext
  · simp
  · simp only [Category.assoc, biprod.map_snd, biprod.lift_snd_assoc,
      biprod.lift_snd]
    rw [← HomologicalComplex.comp_f, ← HomologicalComplex.comp_f]
    congr 1
    apply Pi.hom_ext
    intro n
    simp [roosPmap, Category.assoc, h]

private theorem productHomotopy_π {X Y : CochainComplex (ℕᵒᵖ ⥤ A) ℤ}
    {f g : X ⟶ Y} (h : Homotopy f g) (p q : ℤ) (n : ℕ) :
    productHomotopy h p q ≫
        (Pi.π (fun k : ℕ ↦ Y.asFunctor.obj (op k)) n).f q =
      (Pi.π (fun k : ℕ ↦ X.asFunctor.obj (op k)) n).f p ≫
        (h.hom p q).app (op n) := by
  have hi : (PreservesProduct.iso (HomologicalComplex.eval A (.up ℤ) q)
        (fun k : ℕ ↦ Y.asFunctor.obj (op k))).inv ≫
      (Pi.π (fun k : ℕ ↦ Y.asFunctor.obj (op k)) n).f q =
      Pi.π (fun k : ℕ ↦ (Y.X q).obj (op k)) n := by
    apply (cancel_epi (PreservesProduct.iso (HomologicalComplex.eval A (.up ℤ) q)
      (fun k : ℕ ↦ Y.asFunctor.obj (op k))).hom).1
    rw [Iso.hom_inv_id_assoc]
    simp only [PreservesProduct.iso_hom]
    exact (piComparison_comp_π (HomologicalComplex.eval A (.up ℤ) q)
      (fun k : ℕ ↦ Y.asFunctor.obj (op k)) n).symm
  dsimp only [productHomotopy]
  rw [Category.assoc, Category.assoc, hi, Pi.map_π]
  exact piComparison_comp_π_assoc _ _ _ _

private theorem chain_formulas : ChainFormulas (A := A) := by
  refine ⟨?_, roosF_map_χ, ?_, ?_, augment_natural, (fun X L b hb p ↦ roosAugment_χ b hb p)⟩
  · intro X p
    simpa only [roos_cone_coords, roosχ, roosF, Functor.comp_obj, roosConeFunctor,
      Preadditive.comp_neg, sub_eq_add_neg] using roos_cone_d (roosP X) (roosU X) p
  · intro X Y f p
    exact roosF_map_χ f.inv p
  · intro X Y f g h
    obtain ⟨H, hH⟩ := (roosF_homotopy_functor.{u, v, 0} (A := A)).2.1 X Y f g h
    refine ⟨H, ?_⟩
    intro p
    apply biprod.hom_ext
    · apply (isLimitOfHasProductOfPreservesLimit
        (HomologicalComplex.eval A (.up ℤ) (p - 1))
        (fun n : ℕ ↦ Y.asFunctor.obj (op n))).hom_ext
      rintro ⟨n⟩
      simp only [Fan.mk_π_app, HomologicalComplex.eval_map, Category.assoc,
        biprod.map_fst_assoc, Preadditive.comp_neg, Preadditive.neg_comp,
        productHomotopy_π]
      convert! (hH (p - 1) n).1 using 1 <;>
        (congr! (transparency := .default) <;> omega)
    · apply (isLimitOfHasProductOfPreservesLimit
        (HomologicalComplex.eval A (.up ℤ) (p - 1 + 1))
        (fun n : ℕ ↦ Y.asFunctor.obj (op n))).hom_ext
      rintro ⟨n⟩
      simp only [Fan.mk_π_app, HomologicalComplex.eval_map, Category.assoc,
        biprod.map_snd_assoc, productHomotopy_π]
      convert! (hH (p - 1) n).2 using 1 <;>
        (congr! (transparency := .default) <;> omega)

variable [HasLimitsOfShape ℕᵒᵖ A]
  [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ A)]

private theorem normalized_of_unit
    (RF : DerivedCategory.{w} (ℕᵒᵖ ⥤ A) ⥤ DerivedCategory.{w} A)
    (η : roosLimitFunctor ⋙ DerivedCategory.Q.{w} ⟶ DerivedCategory.Q.{w} ⋙ RF)
    (ρ : roosF ⋙ DerivedCategory.Q.{w} ≅ DerivedCategory.Q.{w} ⋙ RF)
    (hunit : Functor.whiskerRight (roosInclusion (A := A)) DerivedCategory.Q.{w} ≫
      ρ.hom = η)
    (hι : ∀ I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ, I.IsKInjective → QuasiIso (roosι I)) :
    ResolutionNormalized RF η ρ := by
  have hunit_app (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) := NatTrans.congr_app hunit X
  dsimp only [NatTrans.comp_app, Functor.whiskerRight_app, roosInclusion] at hunit_app
  have haug (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (L : CochainComplex A ℤ)
      (b : ∀ n : ℕ, L ⟶ X.asFunctor.obj (op n))
      (hb : ∀ n, b (n + 1) ≫ X.asFunctor.map (homOfLE (Nat.le_succ n)).op = b n) :
      DerivedCategory.Q.map (roosAugment b hb) ≫ ρ.hom.app X =
        DerivedCategory.Q.map (roosAugmentLimit b hb) ≫ η.app X := by
    rw [roosAugment_eq, Functor.map_comp, Category.assoc, hunit_app]
  refine ⟨?_, haug, ?_⟩
  · intro X I q hq hI
    have hn := ρ.hom.naturality q
    dsimp only [Functor.comp_map] at hn
    have hFq : IsIso (DerivedCategory.Q.map (roosF.map q)) := by
      have heq : DerivedCategory.Q.map (roosF.map q) =
          ρ.hom.app X ≫ RF.map (DerivedCategory.Q.map q) ≫ ρ.inv.app I := by
        rw [← Category.assoc, ← hn]
        simp
      rw [heq]
      infer_instance
    have := hι I hI
    have hη : IsIso (η.app I) := by rw [← hunit_app]; infer_instance
    let ε := asIso (DerivedCategory.Q.{w}.map (roosι I))
    let d := asIso (η.app I) ≪≫ (asIso (RF.map (DerivedCategory.Q.map q))).symm
    refine ⟨(DerivedCategory.isIso_Q_map_iff_quasiIso _ _).mp hFq,
      hι I hI, ε, d, rfl, ?_, ?_⟩
    · simp [d]
    · apply (cancel_mono (RF.map (DerivedCategory.Q.map q))).1
      rw [← hn]
      simp only [d, Iso.trans_hom, Iso.symm_hom, asIso_hom, asIso_inv,
        Category.assoc, IsIso.inv_hom_id, Category.comp_id]
      rw [← hunit_app I]
      simp [ε]
  · intro X I L b γ hγ hγb q hq hI J p hp hJ a h d hd lam hlam
    let γ0 : ∀ n : ℕ, L ⟶ (constantTower L).asFunctor.obj (op n) := fun _ ↦ 𝟙 L
    have hγ0 : ∀ n, γ0 (n + 1) ≫
        (constantTower L).asFunctor.map (homOfLE (Nat.le_succ n)).op = γ0 n := by
      intro n
      apply HomologicalComplex.Hom.ext
      funext k
      simp [γ0, constantTower, HomologicalComplex.asFunctor]
    let j := roosAugment γ0 hγ0
    have hb : j ≫ roosF.map b = roosAugment γ hγ := by
      simpa only [Category.id_comp] using
        augment_natural γ0 hγ0 γ hγ b (𝟙 L) (fun n ↦ by
          simpa [γ0] using (hγb n).symm)
    let γp : ∀ n : ℕ, L ⟶ J.asFunctor.obj (op n) := fun n ↦
      (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map p).app (op n)
    have hγp : ∀ n, γp (n + 1) ≫
        J.asFunctor.map (homOfLE (Nat.le_succ n)).op = γp n := by
      intro n
      have hh := (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map p).naturality
        (homOfLE (Nat.le_succ n)).op
      apply HomologicalComplex.Hom.ext
      funext k
      simpa [γp, constantTower, HomologicalComplex.asFunctor] using
        congrArg (fun z ↦ z.f k) hh.symm
    have hp' : j ≫ roosF.map p = lam ≫ roosι J := by
      have he := augment_natural γ0 hγ0 γp hγp p (𝟙 L) (fun n ↦ by simp [γ0, γp])
      simp only [Category.id_comp] at he
      rw [he, roosAugment_eq]
      congr 1
      apply limit.hom_ext
      intro n
      exact (roosAugmentLimit_π γp hγp n.unop).trans (hlam n.unop).symm
    obtain ⟨H, _⟩ := (roosF_homotopy_functor.{u, v, 0} (A := A)).2.1 _ _ _ _ h
    have heq : DerivedCategory.Q.{w}.map
        (lam ≫ lim.map (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map a) ≫
          roosι I) = DerivedCategory.Q.map (roosAugment γ hγ ≫ roosF.map q) := by
      erw [roosι_natural, ← Category.assoc, ← hp', Category.assoc,
        ← roosF.map_comp]
      rw [Functor.map_comp, DerivedCategory.Q_map_eq_of_homotopy _ H,
        roosF.map_comp, ← Functor.map_comp, ← Category.assoc, hb]
    apply (cancel_mono (RF.map (DerivedCategory.Q.map q))).1
    rw [Category.assoc, Category.assoc, hd]
    rw [← hunit_app I, ← Category.assoc, ← Category.assoc, ← Functor.map_comp,
      ← Functor.map_comp, Category.assoc, heq, Functor.map_comp, Category.assoc]
    have hn := ρ.hom.naturality q
    dsimp only [Functor.comp_map] at hn
    rw [hn]
    simp only [Category.assoc]

end Helpers

section ScalarHelpers

variable {A : Type u} [Category.{v} A] [Abelian A] [HasCountableProducts A]
  {B : Type uB} [Category.{vB} B] [Abelian B] [HasCountableProducts B]

private theorem roos_hom_ext {X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ}
    {L : CochainComplex A ℤ} {f g : L ⟶ roosF.obj X}
    (h : ∀ p : ℤ, f.f (p + 1) ≫ (roosχ X p).hom =
      g.f (p + 1) ≫ (roosχ X p).hom) : f = g := by
  ext k
  obtain ⟨p, rfl⟩ : ∃ p : ℤ, k = p + 1 := ⟨k - 1, by omega⟩
  exact (cancel_mono (roosχ X p).hom).1 (h p)

private theorem cone_comparison (F : A ⥤ B) [F.Additive]
    [PreservesLimitsOfShape (Discrete ℕ) F] :
    ∃ c : ∀ X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ,
        (F.mapHomologicalComplex (.up ℤ)).obj (roosF.obj X) ≅
          roosF.obj ((mapTower F).obj X),
      ConeCoordinates F (mapTower F)
        (fun X ↦ PreservesProduct.iso (F.mapHomologicalComplex (.up ℤ))
          (fun n : ℕ ↦ X.asFunctor.obj (op n))) c ∧
      (∀ {X Y : CochainComplex (ℕᵒᵖ ⥤ A) ℤ} (f : X ⟶ Y),
        (F.mapHomologicalComplex (.up ℤ)).map (roosF.map f) ≫ (c Y).hom =
          (c X).hom ≫ roosF.map ((mapTower F).map f)) := by
  obtain ⟨c, hc, hn, _⟩ := strictRoosAdditiveComparison F (fun _ ↦ inferInstance)
  refine ⟨c, hc, ?_⟩
  intro X Y f
  obtain ⟨μ, ν, hμ, hν, heq⟩ := hn X Y f
  have hμ' : μ = roosF.map f :=
    roos_hom_ext (fun p ↦ (hμ p).trans (roosF_map_χ f p).symm)
  have hν' : ν = roosF.map ((mapTower F).map f) :=
    roos_hom_ext (fun p ↦ (hν p).trans (roosF_map_χ ((mapTower F).map f) p).symm)
  simpa only [hμ', hν'] using heq

private theorem scalar_augment (F : A ⥤ B) [F.Additive]
    [PreservesLimitsOfShape (Discrete ℕ) F]
    (c : ∀ X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ,
        (F.mapHomologicalComplex (.up ℤ)).obj (roosF.obj X) ≅
          roosF.obj ((mapTower F).obj X))
    (hc : ConeCoordinates F (mapTower F)
      (fun X ↦ PreservesProduct.iso (F.mapHomologicalComplex (.up ℤ))
        (fun n : ℕ ↦ X.asFunctor.obj (op n))) c)
    (W : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (W' : CochainComplex (ℕᵒᵖ ⥤ B) ℤ)
    (L : CochainComplex A ℤ) (L' : CochainComplex B ℤ)
    (b : ∀ n : ℕ, L ⟶ W.asFunctor.obj (op n))
    (hb : ∀ n, b (n + 1) ≫ W.asFunctor.map (homOfLE (Nat.le_succ n)).op = b n)
    (b' : ∀ n : ℕ, L' ⟶ W'.asFunctor.obj (op n))
    (hb' : ∀ n, b' (n + 1) ≫ W'.asFunctor.map (homOfLE (Nat.le_succ n)).op = b' n)
    (f : (mapTower F).obj W ⟶ W')
    (v : (F.mapHomologicalComplex (.up ℤ)).obj L ⟶ L')
    (h : ∀ n : ℕ, (F.mapHomologicalComplex (.up ℤ)).map (b n) ≫
        (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map f).app (op n) =
      v ≫ b' n) :
    (F.mapHomologicalComplex (.up ℤ)).map (roosAugment b hb) ≫
        (c W).hom ≫ roosF.map f = v ≫ roosAugment b' hb' := by
  with_unfolding_all
    apply roos_hom_ext
    intro p
    simp only [HomologicalComplex.comp_f, Category.assoc, roosF_map_χ,
      reassoc_of% hc, roosAugment_χ, Functor.mapHomologicalComplex_map_f]
    rw [← F.map_comp_assoc, roosAugment_χ]
    apply biprod.hom_ext
    · simp only [Category.assoc]
      erw [biprod.map_fst, biprod.map_fst_assoc, Functor.biprodComparison_fst_assoc,
        ← F.map_comp_assoc, biprod.lift_fst]
      simp
    · simp only [Category.assoc]
      erw [biprod.map_snd, biprod.map_snd_assoc, Functor.biprodComparison_snd_assoc,
        ← F.map_comp_assoc, biprod.lift_snd]
      have hprod : (F.mapHomologicalComplex (.up ℤ)).map (Pi.lift b) ≫
          piComparison (F.mapHomologicalComplex (.up ℤ))
            (fun n : ℕ ↦ W.asFunctor.obj (op n)) ≫ roosPmap f = v ≫ Pi.lift b' := by
        apply Pi.hom_ext
        intro n
        dsimp only [roosPmap]
        simp only [Category.assoc]
        erw [Pi.map_π, piComparison_comp_π_assoc,
          ← Functor.map_comp_assoc, Pi.lift_π, Pi.lift_π]
        exact h n
      simpa only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
        PreservesProduct.iso_hom, biprod.lift_snd] using congrArg (fun z ↦ z.f (p + 1)) hprod

end ScalarHelpers

private theorem normalized_exists
    {D : Type u} [Category.{v} D] (J : GrothendieckTopology D)
    [HasSheafify J AddCommGrpCat.{max u v r}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max u v r}]
    (R : Sheaf J RingCat.{max u v r})
    (hcomm : ∀ (U : Dᵒᵖ) (a b : R.obj.obj U), a * b = b * a)
    [HasDerivedCategory.{w} (ringedSiteModules.{max u v r} R)]
    [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ ringedSiteModules.{max u v r} R)]
    [HasExactLimitsOfShape (Discrete ℕ) (ringedSiteModules.{max u v r} R)]
    (RF : DerivedCategory.{w} (ℕᵒᵖ ⥤ ringedSiteModules.{max u v r} R) ⥤
      DerivedCategory.{w} (ringedSiteModules.{max u v r} R))
    (η : roosLimitFunctor ⋙ DerivedCategory.Q.{w} ⟶ DerivedCategory.Q.{w} ⋙ RF)
    (hRF : RF.IsRightDerivedFunctor η
      (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ ringedSiteModules.{max u v r} R) (.up ℤ))) :
    ∃ ρ : roosF ⋙ DerivedCategory.Q.{w} ≅ DerivedCategory.Q.{w} ⋙ RF,
      ResolutionNormalized RF η ρ := by
  obtain ⟨CF, κ, hCF, _⟩ := strictRoosDerivation.{u, v, r, w} J R hcomm
  let := hCF
  let := hRF
  let W := HomologicalComplex.quasiIso
    (ℕᵒᵖ ⥤ ringedSiteModules.{max u v r} R) (.up ℤ)
  let e : CF ≅ RF := CF.rightDerivedUnique RF (roosDerivedUnit κ) η W
  let ρ : roosF ⋙ DerivedCategory.Q.{w} ≅ DerivedCategory.Q.{w} ⋙ RF :=
    κ ≪≫ Functor.isoWhiskerLeft DerivedCategory.Q e
  have hunit (X : CochainComplex (ℕᵒᵖ ⥤ ringedSiteModules.{max u v r} R) ℤ) :
      DerivedCategory.Q.map (roosι X) ≫ ρ.hom.app X = η.app X := by
    have h := CF.rightDerivedNatTrans_app RF (roosDerivedUnit κ) η W (𝟙 _) X
    simpa [ρ, e, Functor.rightDerivedUnique, Functor.rightDerivedNatIso,
      roosDerivedUnit, roosInclusion, roosLimitFunctor,
      Functor.rightDerivedNatTrans, Category.assoc] using h
  have hunit_nat : Functor.whiskerRight (roosInclusion (A := ringedSiteModules R))
      DerivedCategory.Q.{w} ≫ ρ.hom = η := by
    ext X
    exact hunit X
  refine ⟨ρ, normalized_of_unit RF η ρ hunit_nat ?_⟩
  intro I hI
  obtain ⟨_, j, _, _, hj, _, _, hjqi, _⟩ :=
    strictRoosDerivedLimitComparison.{w, u, v, r} J R hcomm I I (𝟙 I)
  have hj' : j = roosι I := by
    apply HomologicalComplex.Hom.ext
    funext k
    obtain ⟨p, rfl⟩ : ∃ p : ℤ, k = p + 1 := ⟨k - 1, by omega⟩
    apply (cancel_mono (roosχ I p).hom).1
    exact (hj p).trans (roosι_χ I p).symm
  simpa only [hj'] using hjqi

private theorem scalar_properties
    {D : Type u} [Category.{v} D] {J : GrothendieckTopology D}
    [HasSheafify J AddCommGrpCat.{r}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
    {C R : Sheaf J RingCat.{r}} (i : C ⟶ R) :
    PreservesLimitsOfSize.{r, r} (SheafOfModules.restrictScalars.{r} i) ∧
      PreservesColimitsOfSize.{r, r} (SheafOfModules.restrictScalars.{r} i) := by
  have hlim (S : Sheaf J RingCat.{r}) :
      PreservesLimitsOfSize.{r, r} (SheafOfModules.toSheaf.{r} S) := by
    constructor
    intro K _
    exact ((moduleSheaves_colimits_forgetful S).2.2.2.2.2 K).1
  have hcolim (S : Sheaf J RingCat.{r}) :
      PreservesColimitsOfSize.{r, r} (SheafOfModules.toSheaf.{r} S) := by
    constructor
    intro K _
    exact ((moduleSheaves_colimits_forgetful S).2.2.2.2.2 K).2.1
  let := hlim C
  let := hlim R
  let := hcolim C
  let := hcolim R
  let : ReflectsLimitsOfSize.{r, r} (SheafOfModules.toSheaf.{r} C) :=
    reflectsLimits_of_reflectsIsomorphisms
  let : ReflectsColimitsOfSize.{r, r} (SheafOfModules.toSheaf.{r} C) :=
    reflectsColimits_of_reflectsIsomorphisms
  let : PreservesLimitsOfSize.{r, r}
      (SheafOfModules.restrictScalars i ⋙ SheafOfModules.toSheaf.{r} C) :=
    inferInstanceAs (PreservesLimitsOfSize.{r, r} (SheafOfModules.toSheaf.{r} R))
  let : PreservesColimitsOfSize.{r, r}
      (SheafOfModules.restrictScalars i ⋙ SheafOfModules.toSheaf.{r} C) :=
    inferInstanceAs (PreservesColimitsOfSize.{r, r} (SheafOfModules.toSheaf.{r} R))
  exact ⟨preservesLimits_of_reflects_of_preserves _ (SheafOfModules.toSheaf.{r} C),
    preservesColimits_of_reflects_of_preserves _ (SheafOfModules.toSheaf.{r} C)⟩

private theorem scalar_formulas
    {A : Type u} [Category.{v} A] [Abelian A] [HasCountableProducts A]
    [HasLimitsOfShape ℕᵒᵖ A]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ A)]
    {B : Type uB} [Category.{vB} B] [Abelian B] [HasCountableProducts B]
    [HasLimitsOfShape ℕᵒᵖ B]
    [HasDerivedCategory.{w} B] [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ B)]
    (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesLimitsOfShape (Discrete ℕ) F]
    (RF_R : DerivedCategory.{w} (ℕᵒᵖ ⥤ A) ⥤ DerivedCategory.{w} A)
    (ηR : roosLimitFunctor ⋙ DerivedCategory.Q.{w} ⟶ DerivedCategory.Q.{w} ⋙ RF_R)
    (RF_C : DerivedCategory.{w} (ℕᵒᵖ ⥤ B) ⥤ DerivedCategory.{w} B)
    (ηC : roosLimitFunctor ⋙ DerivedCategory.Q.{w} ⟶ DerivedCategory.Q.{w} ⋙ RF_C)
    (ρR : roosF ⋙ DerivedCategory.Q.{w} ≅ DerivedCategory.Q.{w} ⋙ RF_R)
    (hnR : ResolutionNormalized RF_R ηR ρR)
    (ρC : roosF ⋙ DerivedCategory.Q.{w} ≅ DerivedCategory.Q.{w} ⋙ RF_C)
    (hnC : ResolutionNormalized RF_C ηC ρC) :
    ScalarFormulas F RF_R ηR RF_C ηC := by
  obtain ⟨c, hc, hcn⟩ := cone_comparison F
  let P (W : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :=
    PreservesProduct.iso (F.mapHomologicalComplex (.up ℤ))
      (fun n : ℕ ↦ W.asFunctor.obj (op n))
  let Dr := F.mapDerivedCategory
  let φ := F.mapDerivedCategoryFactors
  let β (W : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :=
    Dr.mapIso ((ρR.symm).app W) ≪≫ φ.app (roosF.obj W) ≪≫
      DerivedCategory.Q.mapIso (c W) ≪≫ ρC.app ((mapTower F).obj W)
  refine ⟨inferInstance, inferInstance, inferInstance, chain_formulas, chain_formulas,
    P, c, ρR, ρC, Dr, φ, β, ?_, ?_, hc, hcn, hnR, hnC, ?_, ?_, ?_⟩
  · intro W n
    exact piComparison_comp_π _ _ n
  · intro W
    let G := F.mapHomologicalComplex (.up ℤ)
    change G.map (towerTransitionEndomorphism _) ≫
      piComparison G (fun n : ℕ ↦ W.asFunctor.obj (op n)) =
      piComparison G (fun n : ℕ ↦ W.asFunctor.obj (op n)) ≫
      towerTransitionEndomorphism (K := fun n : ℕ ↦ G.obj (W.asFunctor.obj (op n)))
        (fun n ↦ G.map (W.asFunctor.map (homOfLE (Nat.le_succ n)).op))
    apply Pi.hom_ext
    intro n
    simp only [towerTransitionEndomorphism, towerProductShift, Functor.map_sub,
      Functor.map_id, Preadditive.sub_comp, Preadditive.comp_sub, Category.assoc,
      piComparison_comp_π, Pi.lift_π, Category.id_comp]
    rw [← G.map_comp, Pi.lift_π]
    rw [← Category.assoc, piComparison_comp_π, ← G.map_comp]
  · intro W
    rfl
  · intro W V f
    have hR := ρR.inv.naturality f
    have hC := ρC.hom.naturality ((mapTower F).map f)
    have hφ := φ.hom.naturality (roosF.map f)
    dsimp only [Functor.comp_map] at hR hC hφ
    change Dr.map (RF_R.map (DerivedCategory.Q.map f)) ≫
      (Dr.map (ρR.inv.app V) ≫ φ.hom.app (roosF.obj V) ≫
        DerivedCategory.Q.map (c V).hom ≫ ρC.hom.app ((mapTower F).obj V)) = _
    rw [← Dr.map_comp_assoc, hR, Dr.map_comp, Category.assoc, reassoc_of% hφ]
    rw [← DerivedCategory.Q.map_comp_assoc, hcn f, DerivedCategory.Q.map_comp]
    simp only [Category.assoc]
    rw [hC]
    change _ = (Dr.map (ρR.inv.app W) ≫ φ.hom.app (roosF.obj W) ≫
      DerivedCategory.Q.map (c W).hom ≫ ρC.hom.app ((mapTower F).obj W)) ≫ _
    simp only [Category.assoc]
  · intro W W' L L' b hb b' hb' f v h
    have ha := scalar_augment F c hc W W' L L' b hb b' hb' f v h
    refine ⟨ha, ?_⟩
    have hφ := φ.hom.naturality (roosAugment b hb)
    have hC := ρC.hom.naturality f
    dsimp only [Functor.comp_map] at hφ hC
    change Dr.map (DerivedCategory.Q.map (roosAugment b hb) ≫ ρR.hom.app W) ≫
        (Dr.map (ρR.inv.app W) ≫ φ.hom.app (roosF.obj W) ≫
          DerivedCategory.Q.map (c W).hom ≫ ρC.hom.app ((mapTower F).obj W)) ≫
        RF_C.map (DerivedCategory.Q.map f) = _
    simp only [Dr.map_comp, Category.assoc]
    rw [← Dr.map_comp_assoc (ρR.hom.app W) (ρR.inv.app W),
      Iso.hom_inv_id_app, Dr.map_id, Category.id_comp]
    rw [reassoc_of% hφ]
    rw [← hC]
    rw [← DerivedCategory.Q.map_comp_assoc, ← DerivedCategory.Q.map_comp_assoc,
      Category.assoc, ha, DerivedCategory.Q.map_comp]
    simp only [Category.assoc]


/-- Scalar restriction commutes with the actual signed Roos cones and canonical
augmented derived-limit maps, naturally on strict maps and normalized on every
K-injective tower resolution. The coefficient universe contains the site; its object
and morphism universes remain independent. No boundedness, flatness, completeness,
or preservation of K-injectives by restriction is assumed.
Source: blueprint main-20261015, det-lem-int-tensor-pullback.proof.md, first and final
paragraphs; Stacks 0941, 07KC and 070I
(blueprint: lem-sfb-augmented-scalar-roos-resolution).
Proof plan:
1. Restriction keeps underlying abelian sheaves and maps, hence kernels and sheafified
   cokernels. It is exact. Products are sectionwise and exact over either coefficient
   sheaf by lem-weil-proetale-countable-products-exact. The product comparison has
   the same tuple projections; finite biproducts have the same coordinates.
2. Use def-weil-tower-transition-endomorphism to check dF=Fd and D²=0 for
   D(y,x)=(-dy-Fx,dx). Strict maps commute with F, so products act diagonally on cones.
   The inverse diagonal uses the inverse strict map. The same calculation gives c.
3. A tower homotopy h has compatible components. Its product H commutes with F;
   substitution gives D'(-H,H)+(-H,H)D=diag(f-g,f-g).
4. A compatible augmentation b satisfies F b^Pi=0, hence (0,b^Pi) is a chain map.
   Both augmentation composites have zero first coordinate and equal second tuples.
5. Apply lem-weil-strict-roos-comparison over both rings. For every K-injective
   resolution, lem-sf-strict-roos-derived-limit-comparison supplies both quasi-isos.
   With universal unit η set d=(RF(Qq)) inverse composed with η_I. Naturality gives
   ρ_X=Q Roos(q) (Q j_I) inverse d, with no termwise injectivity requirement.
6. Roos(q) α=j_I lim(q)b. Localize and use naturality of η. The resulting map is
   η_X Q(lim b), equivalently RF(Qb) times the actual constant-tower unit.
7. For a separate resolution p of the constant tower and a comparison a with
   ap homotopic to qb, the compatible homotopy restricts to ordinary inverse limits.
   Localization identifies the two composites, giving the separate-resolution clause.
8. By lem-weil-pbc-exact-functor-derived-factorization restriction descends to D(r)
   with localization comparison φ. Conjugate Q(c) by φ and the two fixed ρ's to
   obtain β. Strict chain naturality gives its naturality by cancellation.
9. Apply the chain augmentation equality and naturality of ρ. This proves that β
   respects the actual canonical augmented maps, also with a subsequent strict map.
   All calculations are degreewise; exact products suffice without boundedness. -/
theorem augmentedScalarRoosResolution
    (Z : AlgebraicGeometry.Scheme.{t})
    (C R : Sheaf (AlgebraicGeometry.Scheme.ProEt.topology Z) RingCat.{max r (t + 1)})
    (_hC : ∀ (U : Z.ProEtᵒᵖ) (a b : C.obj.obj U), a * b = b * a)
    (_hR : ∀ (U : Z.ProEtᵒᵖ) (a b : R.obj.obj U), a * b = b * a)
    (i : C ⟶ R)
    [HasSheafify (AlgebraicGeometry.Scheme.ProEt.topology Z)
      AddCommGrpCat.{max r (t + 1)}]
    [(AlgebraicGeometry.Scheme.ProEt.topology Z).WEqualsLocallyBijective
      AddCommGrpCat.{max r (t + 1)}]
    [HasDerivedCategory.{w} (Modules Z R)]
    [HasDerivedCategory.{w} (Modules Z C)]
    [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ Modules Z R)]
    [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ Modules Z C)]
    (RF_R : DerivedCategory.{w} (ℕᵒᵖ ⥤ Modules Z R) ⥤
      DerivedCategory.{w} (Modules Z R))
    (ηR : roosLimitFunctor (A := Modules Z R) ⋙
      DerivedCategory.Q.{w} (C := Modules Z R) ⟶
        DerivedCategory.Q.{w} (C := ℕᵒᵖ ⥤ Modules Z R) ⋙ RF_R)
    (_hRF_R : RF_R.IsRightDerivedFunctor ηR
      (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ Modules Z R) (.up ℤ)))
    (RF_C : DerivedCategory.{w} (ℕᵒᵖ ⥤ Modules Z C) ⥤
      DerivedCategory.{w} (Modules Z C))
    (ηC : roosLimitFunctor (A := Modules Z C) ⋙
      DerivedCategory.Q.{w} (C := Modules Z C) ⟶
        DerivedCategory.Q.{w} (C := ℕᵒᵖ ⥤ Modules Z C) ⋙ RF_C)
    (_hRF_C : RF_C.IsRightDerivedFunctor ηC
      (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ Modules Z C) (.up ℤ))) :
    ScalarFormulas (A := Modules Z R) (B := Modules Z C)
      (SheafOfModules.restrictScalars.{max r (t + 1)} i) RF_R ηR RF_C ηC := by
  let F := SheafOfModules.restrictScalars.{max r (t + 1)} i
  obtain ⟨hlim, hcolim⟩ := scalar_properties i
  let : PreservesLimitsOfSize.{max r (t + 1), max r (t + 1)} F := hlim
  let : PreservesColimitsOfSize.{max r (t + 1), max r (t + 1)} F := hcolim
  let : HasExactLimitsOfShape (Discrete ℕ) (Modules Z R) :=
    AlgebraicGeometry.Scheme.ProEt.products_exact Z R ℕ
  let : HasExactLimitsOfShape (Discrete ℕ) (Modules Z C) :=
    AlgebraicGeometry.Scheme.ProEt.products_exact Z C ℕ
  obtain ⟨ρR, hnR⟩ := normalized_exists (AlgebraicGeometry.Scheme.ProEt.topology Z)
    R _hR RF_R ηR _hRF_R
  obtain ⟨ρC, hnC⟩ := normalized_exists (AlgebraicGeometry.Scheme.ProEt.topology Z)
    C _hC RF_C ηC _hRF_C
  let : PreservesFiniteLimits F := inferInstance
  let : PreservesFiniteColimits F := inferInstance
  let : PreservesLimitsOfSize.{0, 0} F := preservesLimitsOfSize_shrink F
  let : PreservesLimitsOfShape (Discrete ℕ) F := inferInstance
  exact scalar_formulas F RF_R ηR RF_C ηC ρR hnR ρC hnC

end CategoryTheory
