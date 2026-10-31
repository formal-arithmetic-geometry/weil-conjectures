/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AffineLinePurityComparison
public import WeilConjectures.AlgebraicGeometry.FiniteProductCompactification
public import WeilConjectures.AlgebraicGeometry.FiniteTorAmplitudeSites
public import WeilConjectures.Mathlib.AlgebraicGeometry.AffineSpace
public import WeilConjectures.AlgebraicGeometry.AffineSpacePurityComparison
public import Mathlib.GroupTheory.Perm.Option

import WeilConjectures.AlgebraicGeometry.FiniteEtaleTwistLine
import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateTwist
import WeilConjectures.AlgebraicGeometry.Sites.Kummer
import Mathlib.Algebra.Module.ZMod
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.CategoryTheory.Sites.Monoidal
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import WeilConjectures.AlgebraicGeometry.EtaleConstantRingModuleEquivalence
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.ConstructibleSheaf.Defs
import WeilConjectures.EtaleCohomology.TateTwist.Sheaf
import WeilConjectures.ConstructibleSheaf.Pullback
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1KummerSupplement
import WeilConjectures.ConstructibleSheaf.Monoidal
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.LocallyTrivialInverse
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ProjectionFormula

/-! # Integration of products of even Tate lines

Source: the current blueprint, sec-smooth-purity/sk-prop-sp-composition,
prop-pur-affine-space-composition-law.proof, Steps 3--4.
(blueprint: def-pur-even-line-product-maps).

The index r denotes r+1 factors throughout. Products are the actual finite
compact-support product word. The Tate object is the pullback of the tensor
positiveTensorPower of A(1)[2]; this is the twist-additivity presentation of A(r+1)[2(r+1)].
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048

universe u v w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.EvenLineProduct
open AffineLinePurity AffineSpacePurity

attribute [local irreducible] Etale.ordinaryFiniteSingleFunctor
  AffineSpacePurity.shiftedLine Scheme.finiteEtaleTateLine

section Tensor
variable {B : Type v} [Category.{w} B] [MonoidalCategory B]

/-- Positive, left-associated tensor powers; r means r+1 factors.
Source: the displayed kappa recursion (blueprint: def-pur-even-line-product-maps).
-/
def positiveTensorPower (M : B) : ℕ → B
  | 0 => M
  | r + 1 => positiveTensorPower M r ⊗ M

/-- Canonical reassociation of two positive tensor powers, using only associators.
Source: all binary parenthesizations in the node
(blueprint: def-pur-even-line-product-maps). -/
def appendPower (M : B) (a : ℕ) : (b : ℕ) →
    positiveTensorPower M a ⊗ positiveTensorPower M b ≅ positiveTensorPower M (a + b + 1)
  | 0 => Iso.refl _
  | b + 1 => (α_ (positiveTensorPower M a) (positiveTensorPower M b) M).symm ≪≫
      whiskerRightIso (appendPower M a b) M

/-- The corresponding tensor power of a map to the unit, with the unit constraints.
Source: t_Y tensor (r+1) (blueprint: def-pur-even-line-product-maps). -/
def powerTrace {M : B} (t : M ⟶ 𝟙_ B) : (r : ℕ) → positiveTensorPower M r ⟶ 𝟙_ B
  | 0 => t
  | r + 1 => tensorHom (powerTrace t r) t ≫ (λ_ (𝟙_ B)).hom

/-- A nonempty planar binary parenthesization.
Source: every parenthesization clause
(blueprint: def-pur-even-line-product-maps). -/
inductive ProductTree
  | leaf : ProductTree
  | join : ProductTree → ProductTree → ProductTree

/-- Number of factors minus one. Source: nonempty products in the node
(blueprint: def-pur-even-line-product-maps). -/
def ProductTree.index : ProductTree → ℕ
  | .leaf => 0
  | .join l r => l.index + r.index + 1

/-- Parenthesized tensor object. Source: binary products in the node
(blueprint: def-pur-even-line-product-maps). -/
def ProductTree.tensor (M : B) : ProductTree → B
  | .leaf => M
  | .join l r => l.tensor M ⊗ r.tensor M

/-- Canonical associator normalization of a binary tree.
Source: reassociation clause (blueprint: def-pur-even-line-product-maps). -/
def ProductTree.normalize (M : B) : (t : ProductTree) → t.tensor M ≅ positiveTensorPower M t.index
  | .leaf => Iso.refl _
  | .join l r => (whiskerRightIso (l.normalize M) (r.tensor M) ≪≫
      whiskerLeftIso (positiveTensorPower M l.index) (r.normalize M)) ≪≫
        appendPower M l.index r.index






/-- Swap the last two factors by the signed derived braiding and associators.
Source: adjacent swaps in proof Step 4
(blueprint: def-pur-even-line-product-maps). -/
def lastAdjacent (swap : (M N : B) → M ⊗ N ≅ N ⊗ M) (M : B) : (r : ℕ) →
    positiveTensorPower M (r + 1) ≅ positiveTensorPower M (r + 1)
  | 0 => swap M M
  | r + 1 => (α_ (positiveTensorPower M r) M M) ≪≫
      whiskerLeftIso (positiveTensorPower M r) (swap M M) ≪≫
        (α_ (positiveTensorPower M r) M M).symm

/-- Swap factor i with the last factor, expressed using adjacent signed swaps.
Source: finite permutations in proof Step 4
(blueprint: def-pur-even-line-product-maps). -/
def lastSwap (swap : (M N : B) → M ⊗ N ≅ N ⊗ M) (M : B) :
    (r : ℕ) → (i : Fin (r + 1)) →
    positiveTensorPower M r ≅ positiveTensorPower M r
  | 0, _ => Iso.refl _
  | r + 1, i =>
    match finSuccEquivLast i with
    | none => Iso.refl _
    | some j => whiskerRightIso (lastSwap swap M r j) M ≪≫
        lastAdjacent swap M r ≪≫ (whiskerRightIso (lastSwap swap M r j) M).symm

/-- The signed tensor permutation, obtained by the canonical last-factor decomposition.
This uses the same coordinate convention as the scheme map below.
Source: P_sigma in the node (blueprint: def-pur-even-line-product-maps). -/
def permutation (swap : (M N : B) → M ⊗ N ≅ N ⊗ M) (M : B) :
    (r : ℕ) → (σ : Equiv.Perm (Fin (r + 1))) →
    positiveTensorPower M r ≅ positiveTensorPower M r
  | 0, _ => Iso.refl _
  | r + 1, σ =>
    let d := Equiv.Perm.decomposeOption
      ((Equiv.permCongr (finSuccEquivLast : Fin (r + 2) ≃ Option (Fin (r + 1)))) σ)
    whiskerRightIso (permutation swap M r d.2) M ≪≫
      lastSwap swap M (r + 1) (finSuccEquivLast.symm d.1)
end Tensor

/-- The published signed symmetry in the fixed-scalar derived category.
Source: canonical K-flat derived tensor symmetry
(blueprint: def-pur-even-line-product-maps). -/
def signedSymmetry (P : WeilConjectures.PurityFiniteSetting.{u}) (Y : Scheme.{u})
    (M N : D P Y) : M ⊗ N ≅ N ⊗ M :=
  ((VectorIntegrationSite.symmetry (ModuleCat.{u + 1} (Ring P)) Y).app M).app N

/-- The actual affine coordinate space with r+1 coordinates.
Source: X_m in the node (blueprint: def-pur-even-line-product-maps). -/
abbrev space (Y : Scheme.{u}) (r : ℕ) := iteratedAffineLine Y (r + 1)

/-- Its projection. Source: p_m (blueprint: def-pur-even-line-product-maps). -/
abbrev proj (Y : Scheme.{u}) (r : ℕ) := iteratedAffineLineProj Y (r + 1)

/-- Compactifiability already provided by the recorded affine-space construction.
Source: finite-type affine projection
(blueprint: def-pur-even-line-product-maps). -/
instance projectionCompactifiable (Y : Scheme.{u}) (r : ℕ) :
    HasCompactification (proj Y r) := (projection_geometry Y (r + 1)).2

/-- Use the normalized line compactification at r=0 and the published choice otherwise.
Source: actual finite compact support (blueprint: def-pur-even-line-product-maps).
-/
def compactification (Y : Scheme.{u}) : (r : ℕ) → Compactification (proj Y r)
  | 0 => (affineTraceLineCompactification Y).copy (Category.comp_id _)
  | r + 1 => HasCompactification.compactification (proj Y (r + 1))

/-- The concrete shriek functor, without a six-functor datum.
Source: Rp_m! in the node (blueprint: def-pur-even-line-product-maps). -/
def support (P : WeilConjectures.PurityFiniteSetting.{u}) (Y : Scheme.{u}) (r : ℕ) :=
  rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} (Ring P))
    (compactification Y r)

/-- Twist-additivity presentation of A(r+1)[2(r+1)], pulled back from Y.
Source: T_m in the node (blueprint: def-pur-even-line-product-maps). -/
def tate (P : WeilConjectures.PurityFiniteSetting.{u}) (Y : Scheme.{u}) (r : ℕ) :
    D P (space Y r) :=
  (inverseImage (Ring P) (proj Y r)).obj (positiveTensorPower (shiftedLine P Y) r)

/-- V_m, on the full fixed-coefficient pro-etale derived category.
Source: V_m in the node (blueprint: def-pur-even-line-product-maps). -/
def integral (P : WeilConjectures.PurityFiniteSetting.{u}) (Y : Scheme.{u}) (r : ℕ) : D P Y :=
  (support P Y r).obj (tate P Y r)

/-- First coordinate block of an affine product.
Source: binary relative product (blueprint: def-pur-even-line-product-maps). -/
def first (Y : Scheme.{u}) (a b : ℕ) : space Y (a + b + 1) ⟶ space Y a :=
  (proj Y (a + b + 1)).toIteratedAffineLine (fun i =>
    iteratedAffineLine.coord Y (a + b + 1 + 1)
      (Fin.cast (Nat.succ_add a (b + 1)) (Fin.castAdd (b + 1) i)))

/-- Second coordinate block of an affine product.
Source: binary relative product (blueprint: def-pur-even-line-product-maps). -/
def second (Y : Scheme.{u}) (a b : ℕ) : space Y (a + b + 1) ⟶ space Y b :=
  (proj Y (a + b + 1)).toIteratedAffineLine (fun i =>
    iteratedAffineLine.coord Y (a + b + 1 + 1)
      (Fin.cast (Nat.succ_add a (b + 1)) (Fin.natAdd (a + 1) i)))

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem affine_hom_ext {T Y : Scheme.{u}} (n : ℕ)
    {f g : T ⟶ iteratedAffineLine Y n}
    (hp : f ≫ iteratedAffineLineProj Y n = g ≫ iteratedAffineLineProj Y n)
    (hc : ∀ i, f.appTop (iteratedAffineLine.coord Y n i) =
      g.appTop (iteratedAffineLine.coord Y n i)) : f = g := by
  induction n with
  | zero =>
    change f ≫ 𝟙 Y = g ≫ 𝟙 Y at hp
    exact (Category.comp_id f).symm.trans (hp.trans (Category.comp_id g))
  | succ n ih =>
    apply AffineSpace.hom_ext
    · apply ih
      · change f ≫ _ ≫ _ = g ≫ _ ≫ _ at hp
        exact (Category.assoc _ _ _).trans (hp.trans (Category.assoc _ _ _).symm)
      · intro i
        change f.appTop ((𝔸(PUnit.{u + 1}; iteratedAffineLine Y n) ↘
          iteratedAffineLine Y n).appTop (iteratedAffineLine.coord Y n i)) = _
        exact hc i.succ
    · intro i
      cases i
      exact hc 0

/-- The block projections commute with the structure maps and form a Cartesian square.
Source: concrete product geometry in proof Step 1
(blueprint: def-pur-even-line-product-maps).
Proof: the affine-space universal property identifies a map to X_(a+b+2) with its
first a+1 and last b+1 coordinate vectors and a common map to Y. This is exactly
the pullback universal property. The two projection equations follow by forgetting
the vectors in toIteratedAffineLine_proj. -/
theorem block_geometry (Y : Scheme.{u}) (a b : ℕ) :
    first Y a b ≫ proj Y a = proj Y (a + b + 1) ∧
    second Y a b ≫ proj Y b = proj Y (a + b + 1) ∧
    IsPullback (first Y a b) (second Y a b) (proj Y a) (proj Y b) := by
  have h₁ : first Y a b ≫ proj Y a = proj Y (a + b + 1) :=
    Scheme.Hom.toIteratedAffineLine_proj _ _
  have h₂ : second Y a b ≫ proj Y b = proj Y (a + b + 1) :=
    Scheme.Hom.toIteratedAffineLine_proj _ _
  refine ⟨h₁, h₂, IsPullback.mk' (h₁.trans h₂.symm) ?_ ?_⟩
  · intro T f g hf hg
    apply affine_hom_ext (a + b + 1 + 1)
    · change f ≫ proj Y (a + b + 1) = g ≫ proj Y (a + b + 1)
      rw [← h₁, ← Category.assoc, ← Category.assoc, hf]
    · intro i
      obtain ⟨j, rfl⟩ := (finCongr (Nat.succ_add a (b + 1))).surjective i
      refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) j
      · have h := congrArg (fun z : T ⟶ space Y a ↦
          z.appTop (iteratedAffineLine.coord Y (a + 1) j)) hf
        simpa only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, first,
          Scheme.Hom.toIteratedAffineLine_appTop_coord, finCongr_apply] using h
      · have h := congrArg (fun z : T ⟶ space Y b ↦
          z.appTop (iteratedAffineLine.coord Y (b + 1) j)) hg
        simpa only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, second,
          Scheme.Hom.toIteratedAffineLine_appTop_coord, finCongr_apply] using h
  · intro T f g hfg
    let t : Fin (a + b + 1 + 1) → Γ(T, ⊤) := fun i ↦
      Fin.addCases (fun j ↦ f.appTop (iteratedAffineLine.coord Y (a + 1) j))
        (fun j ↦ g.appTop (iteratedAffineLine.coord Y (b + 1) j))
        (Fin.cast (Nat.succ_add a (b + 1)).symm i)
    let l : T ⟶ space Y (a + b + 1) := (f ≫ proj Y a).toIteratedAffineLine t
    refine ⟨l, ?_, ?_⟩
    · apply affine_hom_ext (a + 1)
      · rw [Category.assoc, h₁]
        exact Scheme.Hom.toIteratedAffineLine_proj _ _
      · intro i
        simp only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, first,
          Scheme.Hom.toIteratedAffineLine_appTop_coord, l, t, Fin.cast_cast,
          Fin.cast_refl, id_eq, Fin.addCases_left]
    · apply affine_hom_ext (b + 1)
      · rw [Category.assoc, h₂, ← hfg]
        exact Scheme.Hom.toIteratedAffineLine_proj _ _
      · intro i
        simp only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, second,
          Scheme.Hom.toIteratedAffineLine_appTop_coord, l, t, Fin.cast_cast,
          Fin.cast_refl, id_eq, Fin.addCases_right]

/-- Actual coordinate-block product geometry, with the standard proper/open ambient product.
Source: finite product compactification in proof Steps 1--2
(blueprint: def-pur-even-line-product-maps). -/
def geometry (Y : Scheme.{u}) (a b : ℕ) : FiniteProductGeometry (proj Y a) (proj Y b) :=
  { finiteProductGeometry (compactification Y a) (compactification Y b) with
    P := space Y (a + b + 1)
    p := first Y a b
    q := second Y a b
    sqP := (block_geometry Y a b).2.2 }

/-- Pullback along a map over Y, normalized using the actual derived compositor.
Source: pullback and twist additivity in Steps 1 and 3
(blueprint: def-pur-even-line-product-maps). -/
def overPullback (A : Type (u + 1)) [CommRing A] {X Z Y : Scheme.{u}}
    (f : X ⟶ Z) (p : Z ⟶ Y) (q : X ⟶ Y) (h : f ≫ p = q) (M : C A Y) :
    (inverseImage A f).obj ((inverseImage A p).obj M) ≅ (inverseImage A q).obj M :=
  ((inverseImageComp A f p).app M).symm ≪≫
    eqToIso (congrArg (fun z => (inverseImage A z).obj M) h)

/-- Canonical coefficient identification for the product: pullback/tensor comparison,
twist positiveTensorPower reassociation, and no scalar orientation choice.
Source: external power T_(a+b) in Step 1
(blueprint: def-pur-even-line-product-maps). -/
def externalIso (P : WeilConjectures.PurityFiniteSetting.{u}) (Y : Scheme.{u}) (a b : ℕ) :
    finiteProductExternal (geometry Y a b) (ModuleCat.{u + 1} (Ring P))
      (tate P Y a) (tate P Y b) ≅ tate P Y (a + b + 1) :=
  tensorIso (Ring P) _
    (overPullback (Ring P) (first Y a b) (proj Y a) (proj Y (a + b + 1))
      (block_geometry Y a b).1 (positiveTensorPower (shiftedLine P Y) a))
    (overPullback (Ring P) (second Y a b) (proj Y b) (proj Y (a + b + 1))
      (block_geometry Y a b).2.1 (positiveTensorPower (shiftedLine P Y) b)) ≪≫
  (inverseImageTensorIso (Ring P) (proj Y (a + b + 1))
    (positiveTensorPower (shiftedLine P Y) a) (positiveTensorPower (shiftedLine P Y) b)).symm ≪≫
  (inverseImage (Ring P) (proj Y (a + b + 1))).mapIso
    (appendPower (shiftedLine P Y) a b)

private theorem etale_ctf (A : Type (u + 1)) [CommRing A] [Finite A]
    (T : Scheme.{u}) (K : C A T)
    (hK : DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} A) T K) :
    ∃ L, Etale.DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} A) T L ∧
      Nonempty (((comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategory).obj L ≅ K) := by
  obtain ⟨L, hL, ⟨e⟩⟩ := hK.1
  obtain ⟨a, b, ht⟩ := hK.2
  exact ⟨L, ⟨hL, a, b, DerivedCategory.torAmplitudeIn_of_mapDerivedCategory A
    ((DerivedCategory.torAmplitudeIn _ T a b).prop_of_iso e.symm ht)⟩, ⟨e⟩⟩

private theorem tensor_ctf (A : Type (u + 1)) [CommRing A] [Finite A]
    (T : Scheme.{u}) (K M : C A T)
    (hK : DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} A) T K)
    (hM : DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} A) T M) :
    DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} A) T (K ⊗ M) := by
  obtain ⟨L, hL, ⟨e⟩⟩ := etale_ctf A T K hK
  obtain ⟨N, hN, ⟨e'⟩⟩ := etale_ctf A T M hM
  let q := (derivedTensorObjCompMapDerivedCategoryComparisonUpperStarIso
    (ModuleCat.{u + 1} A) L).app N ≪≫ tensorIso A T e e'
  exact (DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} A) T).prop_of_iso q
    (DerivedCategory.constructibleFiniteTor_mapDerivedCategory A
      (Etale.constructibleFiniteTor_tensor A T hL hN))

private theorem pull_ctf (A : Type (u + 1)) [CommRing A] [Finite A]
    {T Z : Scheme.{u}} (f : T ⟶ Z) (K : C A Z)
    (hK : DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} A) Z K) :
    DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} A) T
      ((inverseImage A f).obj K) := by
  obtain ⟨L, hL, ⟨e⟩⟩ := etale_ctf A Z K hK
  let q := ((Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso
      (comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} A) f).symm ≪≫
      Functor.mapDerivedCategoryCompIso _ _).app L ≪≫
    (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) f).symm.app _ ≪≫
    (inverseImage A f).mapIso e
  exact (DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} A) T).prop_of_iso q
    (DerivedCategory.constructibleFiniteTor_mapDerivedCategory A
      (Etale.constructibleFiniteTor_mapDerivedCategory_upperStar A f hL))

private theorem ordinaryLine_ctf (A : Type (u + 1)) [CommRing A] [Finite A]
    (T : Scheme.{u}) (N : ℕ) (hA : (N : A) = 0) (hN : 0 < N)
    (hunit : IsUnit (N : Γ(T, ⊤))) :
    Etale.DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} A) T
      ((Etale.ordinaryFiniteDegreeZero A T
        (Scheme.finiteEtaleTateLine T N A hA))⟦(2 : ℤ)⟧) := by
  unfold Etale.ordinaryFiniteDegreeZero
  let F := Scheme.finiteEtaleTateLine T N A hA
  obtain ⟨⟨cover, hc⟩, hlc, hflat, _⟩ := Scheme.finite_etale_torsion_twist_line
    T N hN (fun t ↦ by
      simpa only [map_natCast] using hunit.map (T.presheaf.germ ⊤ t (by trivial)).hom)
    A hA 1
  have hloc : Scheme.IsLocallyConstantSheaf F := hlc
  let e (i : cover.I₀) : (Etale.upperStar (ModuleCat.{u + 1} A) (cover.f i)).obj F ≅
      𝟙_ (Sheaf (cover.X i).smallEtaleTopology (ModuleCat.{u + 1} A)) :=
    let U := cover.etalePrecoverageToEtale i
    let E := Scheme.Etale.overSheafEquiv U (ModuleCat.{u + 1} A)
    (Scheme.overSheafEquivFunctorObjOverIso (ModuleCat.{u + 1} A) U F).symm ≪≫
      E.functor.mapIso (hc i).some ≪≫
      ((Scheme.Etale.overEquiv U).constantSheafSheafCongrIso
        (T.smallEtaleTopology.over U) U.left.smallEtaleTopology (ModuleCat.{u + 1} A)
        Over.mkIdTerminal).app (ModuleCat.of A A) ≪≫
      (Functor.Monoidal.εIso
        (constantSheaf U.left.smallEtaleTopology (ModuleCat.{u + 1} A))).symm
  have : Scheme.JointlySurjective Scheme.etalePrecoverage.{u} :=
    inferInstanceAs (Scheme.JointlySurjective (Scheme.precoverage @AlgebraicGeometry.Etale))
  let invF := Etale.tensorInverseOfUpperStarIso (ModuleCat.{u + 1} A)
    cover.f cover.iUnion_range F e
  have hfinite : Scheme.IsFiniteSheaf F := Scheme.IsFiniteSheaf.of_tensorIso invF.rightIso
  have : Scheme.IsConstructibleSheaf F :=
    Scheme.IsFiniteLocallyConstantSheaf.isConstructibleSheaf
      { toIsLocallyConstantSheaf := hloc, toIsFiniteSheaf := hfinite }
  have hf : ObjectProperty.flat F :=
    (ObjectProperty.flat_iff_preservesFiniteLimits F).2 hflat
  have hbc := Etale.DerivedCategory.boundedConstructible_singleFunctor_obj F 0
  have ht := Etale.torAmplitudeIn_shift (ModuleCat.{u + 1} A)
    (_root_.DerivedCategory.torAmplitudeIn_singleFunctor_obj_of_flat hf) (2 : ℤ)
  exact ⟨(Etale.DerivedCategory.boundedConstructible _ T).le_shift (2 : ℤ) _ hbc,
    (0 : ℤ) - 2, (0 : ℤ) - 2, ht⟩

/-- Compare the constructed ordinary line before specializing the coefficient ring. -/
private theorem comparedLine_ctf (A : Type (u + 1)) [CommRing A] [Finite A]
    (T : Scheme.{u}) (N : ℕ) (hA : (N : A) = 0) (hN : 0 < N)
    (hunit : IsUnit (N : Γ(T, ⊤))) :
    DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} A) T
      ((VectorIntegrationSite.comparison A T).obj
        ((Etale.ordinaryFiniteDegreeZero A T
          (Scheme.finiteEtaleTateLine T N A hA))⟦(2 : ℤ)⟧)) := by
  exact DerivedCategory.constructibleFiniteTor_mapDerivedCategory A
    (ordinaryLine_ctf A T N hA hN hunit)

private theorem shiftedLine_ctf (P : WeilConjectures.PurityFiniteSetting.{u})
    (T : Scheme.{u}) (aT : T ⟶ Spec (.of P.field.k)) :
    DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} (Ring P)) T
      (shiftedLine P T) := by
  simpa only [shiftedLine, Etale.ordinaryFiniteLine] using
    comparedLine_ctf (Ring P) T (P.coefficients.l ^ (P.level + 1))
      (annihilates P) (pow_pos (Fact.out : P.coefficients.l.Prime).pos _)
      (exponentUnit P T aT)

private theorem power_ctf (A : Type (u + 1)) [CommRing A] [Finite A]
    (Y : Scheme.{u}) (M : C A Y)
    (hM : DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} A) Y M) (r : ℕ) :
    DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} A) Y
      (positiveTensorPower M r) := by
  induction r with
  | zero => exact hM
  | succ r ih => exact tensor_ctf A Y _ _ ih hM

private theorem tate_ctf (P : WeilConjectures.PurityFiniteSetting.{u})
    (Y : Scheme.{u}) (aY : Y ⟶ Spec (.of P.field.k)) (r : ℕ) :
    DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} (Ring P)) (space Y r)
      (tate P Y r) :=
  pull_ctf (Ring P) (proj Y r) _ (power_ctf (Ring P) Y _ (shiftedLine_ctf P Y aY) r)

/-- The finite flat Tate external power has bounded etale origin at every positive level.
Source: proof Step 1, shifted locally constant flat line and finite-Tor comparison
(blueprint: def-pur-even-line-product-maps).
Proof: the finite Kummer sheaf is a locally constant free rank-one A-module since ell
is invertible on Y. Its finite tensor powers are flat locally constant, in degree
-2(a+b+2). Exact pullback preserves this property. The displayed externalIso identifies
the external product with that pullback. Its ordinary etale realization is bounded,
and the canonical site comparison gives the required origin witness. -/
theorem external_origin (P : WeilConjectures.PurityFiniteSetting.{u}) (Y : Scheme.{u})
    (aY : Y ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    [IsSeparated aY] (a b : ℕ) :
    DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} (Ring P)) (space Y (a + b + 1))
      (finiteProductExternal (geometry Y a b) (ModuleCat.{u + 1} (Ring P))
        (tate P Y a) (tate P Y b)) := by
  exact (DerivedCategory.plusEtaleOrigin _ _).prop_of_iso (externalIso P Y a b).symm
    (tate_ctf P Y aY (a + b + 1)).plusEtaleOrigin

/-- The actual forward compact-support product, in affine coordinate-block coordinates.
The target compactification is only copied across its structure-map equality: its open
and proper maps, hence its shriek functor, are unchanged. This is the specified Xi word.
Source: kappa_(a,b) inverse in the node
(blueprint: def-pur-even-line-product-maps). -/
@[irreducible]
def forward (P : WeilConjectures.PurityFiniteSetting.{u}) (Y : Scheme.{u})
    (aY : Y ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    [IsSeparated aY] (a b : ℕ) :
    integral P Y a ⊗ integral P Y b ⟶ integral P Y (a + b + 1) :=
  let ch := (compactification Y (a + b + 1)).copy (block_geometry Y a b).2.1
  letI : HasCompactification (second Y a b ≫ proj Y b) := ch.hasCompactification
  finiteProductChosenForward (geometry Y a b) (Ring P)
    (compactification Y a) (compactification Y b) ch (tate P Y a) (tate P Y b)
    (external_origin P Y aY a b) ≫
      (support P Y (a + b + 1)).map (externalIso P Y a b).hom


/-- The normalized affine-line integration, transported only by the canonical Tate
pullback, line coefficient, and constant-unit identifications.
Source: t_Y in the node (blueprint: def-pur-even-line-product-maps). -/
@[irreducible]
def trace (P : WeilConjectures.PurityFiniteSetting.{u}) (Y : Scheme.{u})
    (aY : Y ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    [IsSeparated aY] : integral P Y 0 ⟶ 𝟙_ (D P Y) :=
  letI : IsNoetherian Y := tower_noetherian P Y aY 0
  (support P Y 0).map
    ((shiftedLinePullback P (proj Y 0) aY).hom ≫ (lineCoefficientIso P Y aY).inv) ≫
  integration P.coefficients.l P.extension (P.level - 1) Y P.level (annihilates P)
    (((isUnit_pow_iff (Nat.succ_ne_zero P.level)).mp
      (by simpa only [Nat.cast_pow] using exponentUnit P Y aY))) ≫
  (coefficientUnitIso (ModuleCat.{u + 1} (Ring P)) Y).hom

/-- The specified inverse binary product, requiring precisely its actual invertibility.
Source: kappa_(m,1) (blueprint: def-pur-even-line-product-maps). -/
def binaryInverse (P : WeilConjectures.PurityFiniteSetting.{u}) (Y : Scheme.{u})
    (aY : Y ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    [IsSeparated aY] (a b : ℕ) (h : IsIso (forward P Y aY a b)) :
    integral P Y (a + b + 1) ≅ integral P Y a ⊗ integral P Y b :=
  letI := h
  (asIso (forward P Y aY a b)).symm

/-- The displayed kappa recursion, with kappa_1 literally the identity.
Source: kappa_m in the node (blueprint: def-pur-even-line-product-maps). -/
def kappa (P : WeilConjectures.PurityFiniteSetting.{u}) (Y : Scheme.{u})
    (aY : Y ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    [IsSeparated aY] (h : ∀ a : ℕ, IsIso (forward P Y aY a 0)) :
    (r : ℕ) → integral P Y r ≅ positiveTensorPower (integral P Y 0) r
  | 0 => Iso.refl _
  | r + 1 => binaryInverse P Y aY r 0 (h r) ≪≫
      whiskerRightIso (kappa P Y aY h r) (integral P Y 0)

/-- Forward iteration with any binary parenthesization. No invertibility of other
binary products is assumed. Source: every parenthesization clause
(blueprint: def-pur-even-line-product-maps). -/
def treeForward (P : WeilConjectures.PurityFiniteSetting.{u}) (Y : Scheme.{u})
    (aY : Y ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    [IsSeparated aY] : (t : ProductTree) →
      t.tensor (integral P Y 0) ⟶ integral P Y t.index
  | .leaf => 𝟙 _
  | .join l r => tensorHom (treeForward P Y aY l) (treeForward P Y aY r) ≫
      forward P Y aY l.index r.index

/-- Polynomial coordinate permutation, not an arbitrary automorphism over Y.
Source: s_sigma in the node (blueprint: def-pur-even-line-product-maps). -/
def coordinate (Y : Scheme.{u}) (r : ℕ) (σ : Equiv.Perm (Fin (r + 1))) :
    space Y r ⟶ space Y r :=
  (proj Y r).toIteratedAffineLine (fun i => iteratedAffineLine.coord Y (r + 1) (σ i))

/-- The actual coordinate map is an automorphism and its square over 1_Y is Cartesian.
Source: coordinate permutations in proof Step 3
(blueprint: def-pur-even-line-product-maps).
Proof: the map for sigma inverse is a two-sided inverse by the universal coordinate
property. Forgetting coordinates gives coordinate times p=p. An isomorphism over the
identity is a Cartesian square, with its evident inverse universal lift. -/
theorem coordinate_geometry (Y : Scheme.{u}) (r : ℕ)
    (σ : Equiv.Perm (Fin (r + 1))) :
    IsIso (coordinate Y r σ) ∧ coordinate Y r σ ≫ proj Y r = proj Y r ∧
      IsPullback (coordinate Y r σ) (proj Y r) (proj Y r) (𝟙 Y) := by
  have hp (τ : Equiv.Perm (Fin (r + 1))) :
      coordinate Y r τ ≫ proj Y r = proj Y r :=
    Scheme.Hom.toIteratedAffineLine_proj _ _
  have hc (τ υ : Equiv.Perm (Fin (r + 1))) (h : ∀ i, τ (υ i) = i) :
      coordinate Y r τ ≫ coordinate Y r υ = 𝟙 _ := by
    apply affine_hom_ext (r + 1)
    · simp only [Category.assoc, hp, Category.id_comp]
    · intro i
      simp only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
        coordinate, Scheme.Hom.toIteratedAffineLine_appTop_coord, h,
        Scheme.Hom.id_appTop, CommRingCat.id_apply]
  let e : space Y r ≅ space Y r :=
    ⟨coordinate Y r σ, coordinate Y r σ.symm,
      hc σ σ.symm σ.apply_symm_apply, hc σ.symm σ σ.symm_apply_apply⟩
  have : IsIso (coordinate Y r σ) := e.isIso_hom
  exact ⟨inferInstance, hp σ, IsPullback.of_horiz_isIso ⟨by simp only [hp,
    Category.comp_id]⟩⟩

/-- Canonical twist-additivity identification under coordinate pullback.
Source: the coefficient identification defining S_sigma
(blueprint: def-pur-even-line-product-maps). -/
def coordinateTate (P : WeilConjectures.PurityFiniteSetting.{u}) (Y : Scheme.{u})
    (r : ℕ) (σ : Equiv.Perm (Fin (r + 1))) :
    (inverseImage (Ring P) (coordinate Y r σ)).obj (tate P Y r) ≅ tate P Y r :=
  overPullback (Ring P) (coordinate Y r σ) (proj Y r) (proj Y r)
    (coordinate_geometry Y r σ).2.1 (positiveTensorPower (shiftedLine P Y) r)

/-- Origin of a finite Tate power and of its coefficient-first tensor with a ctf input,
including after a coordinate pullback.
Source: proof Steps 1 and 6 (blueprint: def-pur-even-line-product-maps).
Proof: the Tate power is a shifted locally constant flat line of rank one. Ctf objects
have bounded etale-origin representatives, and exact inverse image and tensoring with
this shifted flat line preserve boundedness. Pullback by the coordinate isomorphism
preserves the same representative. The site comparison supplies each asserted witness.
-/
theorem coordinate_origins (P : WeilConjectures.PurityFiniteSetting.{u}) (Y : Scheme.{u})
    (aY : Y ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    [IsSeparated aY] (r : ℕ) (σ : Equiv.Perm (Fin (r + 1))) :
    DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} (Ring P)) (space Y r)
      ((inverseImage (Ring P) (coordinate Y r σ)).obj (tate P Y r)) ∧
    ∀ K : D P Y, DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} (Ring P)) Y K →
      DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} (Ring P)) (space Y r)
        ((inverseImage (Ring P) (coordinate Y r σ)).obj
          ((inverseImage (Ring P) (proj Y r)).obj K ⊗ tate P Y r)) := by
  constructor
  · exact (pull_ctf (Ring P) (coordinate Y r σ) _
      (tate_ctf P Y aY r)).plusEtaleOrigin
  · intro K hK
    exact (pull_ctf (Ring P) (coordinate Y r σ) _
      (tensor_ctf (Ring P) (space Y r) _ _
        (pull_ctf (Ring P) (proj Y r) K hK) (tate_ctf P Y aY r))).plusEtaleOrigin

/-- Actual scheme-induced action on compact support: inverse identity pullback,
exchange for the isomorphism square, canonical compactification comparison, then
coefficient pullback. The origin witness restricts only the existing comparison.
Source: S_sigma in the node (blueprint: def-pur-even-line-product-maps). -/
@[irreducible]
def actionOn (P : WeilConjectures.PurityFiniteSetting.{u}) (Y : Scheme.{u})
    (r : ℕ) (σ : Equiv.Perm (Fin (r + 1))) (M : D P (space Y r))
    (e : (inverseImage (Ring P) (coordinate Y r σ)).obj M ≅ M)
    (hM : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} (Ring P)) (space Y r)
      ((inverseImage (Ring P) (coordinate Y r σ)).obj M)) :
    (support P Y r).obj M ⟶ (support P Y r).obj M :=
  (inverseImageId (Ring P) Y).inv.app _ ≫
  (rightDerivedLowerShriekOfCompactificationBaseChangeMap (ModuleCat.{u + 1} (Ring P))
    (coordinate_geometry Y r σ).2.2 (compactification Y r)).app M ≫
  (finiteForwardCompactificationComparison (Ring P)
    ((compactification Y r).ofIsPullback (coordinate_geometry Y r σ).2.2)
    (compactification Y r)).hom.app ⟨_, hM⟩ ≫
  (support P Y r).map e.hom

/-- The action on V_m induced by the actual coordinate permutation.
Source: S_sigma (blueprint: def-pur-even-line-product-maps). -/
def coordinateAction (P : WeilConjectures.PurityFiniteSetting.{u}) (Y : Scheme.{u})
    (aY : Y ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    [IsSeparated aY] (r : ℕ) (σ : Equiv.Perm (Fin (r + 1))) :
    integral P Y r ⟶ integral P Y r :=
  actionOn P Y r σ (tate P Y r) (coordinateTate P Y r σ)
    (coordinate_origins P Y aY r σ).1

/-- The coordinate action with K remaining first. No symmetry crosses K.
Source: S_(sigma,K) in proof Step 6
(blueprint: def-pur-even-line-product-maps). -/
def coefficientAction (P : WeilConjectures.PurityFiniteSetting.{u}) (Y : Scheme.{u})
    (aY : Y ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    [IsSeparated aY] (r : ℕ) (σ : Equiv.Perm (Fin (r + 1)))
    (K : D P Y) (hK : DerivedCategory.constructibleFiniteTor
      (ModuleCat.{u + 1} (Ring P)) Y K) :
    (support P Y r).obj ((inverseImage (Ring P) (proj Y r)).obj K ⊗ tate P Y r) ⟶
    (support P Y r).obj ((inverseImage (Ring P) (proj Y r)).obj K ⊗ tate P Y r) :=
  actionOn P Y r σ _
    (inverseImageTensorIso (Ring P) (coordinate Y r σ) _ _ ≪≫
      tensorIso (Ring P) _
        (overPullback (Ring P) (coordinate Y r σ) (proj Y r) (proj Y r)
          (coordinate_geometry Y r σ).2.1 K) (coordinateTate P Y r σ))
    ((coordinate_origins P Y aY r σ).2 K hK)

attribute [local irreducible] projectionMapOfCompactification

private theorem reorderedProjection_isIso
    (A : Type (u + 1)) [CommRing A] [Finite A] {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) (F : C A X) (K : C A Y)
    (h : IsIso (((projectionMapOfCompactification (ModuleCat.{u + 1} A) c).app F).app K)) :
    IsIso (VectorIntegrationSite.projection (ModuleCat.{u + 1} A) c F K) := by
  unfold VectorIntegrationSite.projection
  exact IsIso.comp_isIso' inferInstance (IsIso.comp_isIso' h inferInstance)

/-- Invertibility of the actual coefficient-first projection component.
Source: proof Step 6 (blueprint: def-pur-even-line-product-maps).
Proof: the Tate power is bounded constructible, K has finite Tor amplitude, and p_m
is separated of finite type between Noetherian schemes with finite constant A.
Apply the finite compact-support projection formula to the canonical etale-origin
representatives, and conjugate by the two signed symmetries to keep K first. -/
theorem projection_isIso (P : WeilConjectures.PurityFiniteSetting.{u}) (Y : Scheme.{u})
    (aY : Y ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    [IsSeparated aY] (r : ℕ) (K : D P Y)
    (hK : DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} (Ring P)) Y K) :
    IsIso (VectorIntegrationSite.projection (ModuleCat.{u + 1} (Ring P))
      (compactification Y r) (tate P Y r) K) := by
  have hPF := hasProjectionFormulaOfCompactification_of_constructibleFiniteTor
    (Ring P) (compactification Y r) (tate_ctf P Y aY r) hK
  exact reorderedProjection_isIso (Ring P) (compactification Y r) _ K hPF

/-- The counit with coefficient K first: inverse actual projection, 1_K tensor J,
then the standard right unit constraint.
Source: final displayed map in the node
(blueprint: def-pur-even-line-product-maps). -/
def coefficientTrace (P : WeilConjectures.PurityFiniteSetting.{u}) (Y : Scheme.{u})
    (aY : Y ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    [IsSeparated aY] (r : ℕ) (K : D P Y)
    (hK : DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} (Ring P)) Y K)
    (J : integral P Y r ⟶ 𝟙_ (D P Y)) :
    (support P Y r).obj ((inverseImage (Ring P) (proj Y r)).obj K ⊗ tate P Y r) ⟶ K :=
  letI := projection_isIso P Y aY r K hK
  inv (VectorIntegrationSite.projection (ModuleCat.{u + 1} (Ring P))
    (compactification Y r) (tate P Y r) K) ≫ tensorHom (𝟙 K) J ≫ (ρ_ K).hom

end AlgebraicGeometry.ProEtale.EvenLineProduct
