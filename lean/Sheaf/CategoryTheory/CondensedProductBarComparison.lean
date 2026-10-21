/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NX
-/
module

public import Sheaf.CategoryTheory.CondensedProductActionInflation
public import Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
public import Sheaf.CategoryTheory.DerivedCategory.CompositionAdjunctionNormalization
public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
public import Mathlib.CategoryTheory.Preadditive.FunctorCategory
public import WeilConjectures.Mathlib.Algebra.Homology.TotalComplex
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExactPullback
public import Mathlib.Algebra.Homology.Functor
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import WeilConjectures.CategoryTheory.DoubleComplexTotal
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import Mathlib.CategoryTheory.Abelian.Injective.Resolution
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Sheaf.CategoryTheory.SheafTensor
import Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence
import WeilConjectures.Algebra.Homology.FirstQuadrantTotalComparison
import WeilConjectures.Mathlib.CategoryTheory.Preadditive.Injective.Preserves
import Sheaf.CategoryTheory.DerivedInjectiveResolutionNaturality
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ExtensionByZeroFlat
import WeilConjectures.Algebra.Homology.LiftToInjectiveUniqueUpToHomotopy

/-! # The normalized product-to-successive condensed internal bar comparison

Source: blueprint direct-image stability, paragraph (3), formal augmented-bar input
(blueprint: lem-sfb-condensed-product-bar-comparison).

Internal Hom from a free represented module is specified by its sections on products
of profinite test objects. Applying this functor to an equivariant injective resolution,
rather than to the original module, gives the derived internal Hom terms.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicTopology

namespace Profinite.CondensedAction

section ActionInstances

variable (R : Profinite.CondensedRing.{u}) [IsCommMonObj R.X]
variable (P : Type u) [TopologicalSpace P] [Group P] [IsTopologicalGroup P]
  [CompactSpace P] [T2Space P] [TotallyDisconnectedSpace P]

/-- The abelian structure has exactly the existing sectionwise addition of action maps.
All other fields are propositions furnished by `product_action_inflation` with both
factors P. Source: blueprint paragraph (3)
(blueprint: lem-sfb-condensed-product-bar-comparison). -/
noncomputable instance productBarActionAbelian : Abelian (ActionModule R P) where
  toPreadditive := actionPreadditive
  toIsNormalMonoCategory := by
    obtain ⟨a, _, _, ha, _⟩ := product_action_inflation R P P
    exact ha ▸ a.toIsNormalMonoCategory
  toIsNormalEpiCategory := by
    obtain ⟨a, _, _, ha, _⟩ := product_action_inflation R P P
    exact ha ▸ a.toIsNormalEpiCategory
  has_finite_products := by
    obtain ⟨a, _, _, _, _⟩ := product_action_inflation R P P
    exact a.has_finite_products
  has_kernels := by
    obtain ⟨a, _, _, ha, _⟩ := product_action_inflation R P P
    exact ha ▸ a.has_kernels
  has_cokernels := by
    obtain ⟨a, _, _, ha, _⟩ := product_action_inflation R P P
    exact ha ▸ a.has_cokernels


/-- The corresponding property is supplied by the recorded inflation theorem.
Source: blueprint paragraph (3)
(blueprint: lem-sfb-condensed-product-bar-comparison). -/
instance productBarActionGrothendieck : IsGrothendieckAbelian.{u + 1} (ActionModule R P) := by
  obtain ⟨a, _, _, hs⟩ := product_action_inflation R P P
  have ha : a = productBarActionAbelian R P := by
    have h := hs.1
    cases a
    cases h
    rfl
  exact ha ▸ hs.2.2.2.2.1

/-- The corresponding property is supplied by the recorded inflation theorem.
Source: blueprint paragraph (3)
(blueprint: lem-sfb-condensed-product-bar-comparison). -/
instance productBarTrivialAdditive : (trivial (R := R) (P := P)).Additive := by
  obtain ⟨a, _, _, hs⟩ := product_action_inflation R P P
  exact hs.2.2.2.2.2.2.2.1

/-- The corresponding property is supplied by the recorded inflation theorem.
Source: blueprint paragraph (3)
(blueprint: lem-sfb-condensed-product-bar-comparison). -/
instance productBarTrivialFiniteLimits : PreservesFiniteLimits (trivial (R := R) (P := P)) := by
  obtain ⟨a, _, _, hs⟩ := product_action_inflation R P P
  exact hs.2.2.2.2.2.2.2.2.1

/-- The corresponding property is supplied by the recorded inflation theorem.
Source: blueprint paragraph (3)
(blueprint: lem-sfb-condensed-product-bar-comparison). -/
instance productBarTrivialFiniteColimits : PreservesFiniteColimits (trivial (R := R) (P := P)) := by
  obtain ⟨a, _, _, hs⟩ := product_action_inflation R P P
  exact hs.2.2.2.2.2.2.2.2.2.1

/-- Ordinary internal modules have the Grothendieck property in the recorded theorem.
Source: blueprint paragraph (3)
(blueprint: lem-sfb-condensed-product-bar-comparison). -/
instance productBarModulesGrothendieck : IsGrothendieckAbelian.{u + 1} (Modules R) := by
  obtain ⟨_, _, _, hs⟩ := product_action_inflation R PUnit.{u + 1} PUnit.{u + 1}
  exact hs.2.2.2.1

variable (G H : Type u) [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
  [TopologicalSpace H] [Group H] [IsTopologicalGroup H]
  [CompactSpace H] [T2Space H] [TotallyDisconnectedSpace H]

/-- Exact additive projection inflation is supplied by the recorded theorem.
Source: blueprint paragraph (3)
(blueprint: lem-sfb-condensed-product-bar-comparison). -/
instance productBarInflateAdditive :
    (inflate (R := R) (ContinuousMonoidHom.fst G H)).Additive := by
  obtain ⟨_, _, _, hs⟩ := product_action_inflation R G H
  exact hs.2.2.2.2.2.2.2.2.2.2.2.2.2.1

/-- Exact additive projection inflation is supplied by the recorded theorem.
Source: blueprint paragraph (3)
(blueprint: lem-sfb-condensed-product-bar-comparison). -/
instance productBarInflateFiniteLimits :
    PreservesFiniteLimits (inflate (R := R) (ContinuousMonoidHom.fst G H)) := by
  obtain ⟨_, _, _, hs⟩ := product_action_inflation R G H
  exact hs.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

/-- Exact additive projection inflation is supplied by the recorded theorem.
Source: blueprint paragraph (3)
(blueprint: lem-sfb-condensed-product-bar-comparison). -/
instance productBarInflateFiniteColimits :
    PreservesFiniteColimits (inflate (R := R) (ContinuousMonoidHom.fst G H)) := by
  obtain ⟨_, _, _, hs⟩ := product_action_inflation R G H
  exact hs.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1


end ActionInstances

variable (R : Profinite.CondensedRing.{u}) [IsCommMonObj R.X]
variable (G H : Type u) [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
  [TopologicalSpace H] [Group H] [IsTopologicalGroup H]
  [CompactSpace H] [T2Space H] [TotallyDisconnectedSpace H]

/-- Profinite parameters representing the free-module internal Hom sections.
Source: blueprint paragraph (3) (blueprint: lem-sfb-condensed-product-bar-comparison). -/
def productBarParameters (S : Profinite.{u}) (a b : ℕ) : Profinite.{u} :=
  Profinite.of (S × ((Fin a → G) × (Fin b → H)))

/-- The inhomogeneous nerve face: omit an endpoint or multiply adjacent coordinates.
Source: blueprint paragraph (3) (blueprint: lem-sfb-condensed-product-bar-comparison). -/
def productBarFace {P : Type u} [TopologicalSpace P] [Group P] [IsTopologicalGroup P]
    (n : ℕ) (i : Fin (n + 2)) : C((Fin (n + 1) → P), (Fin n → P)) :=
  ContinuousMap.pi fun j ↦
    if j.val + 1 < i.val then ContinuousMap.eval (X := fun _ : Fin (n + 1) ↦ P) j.castSucc
    else if j.val + 1 = i.val then
      ContinuousMap.eval (X := fun _ : Fin (n + 1) ↦ P) j.castSucc *
        ContinuousMap.eval (X := fun _ : Fin (n + 1) ↦ P) j.succ
    else ContinuousMap.eval (X := fun _ : Fin (n + 1) ↦ P) j.succ

/-- Insert the unit, the inhomogeneous nerve degeneracy.
Source: blueprint paragraph (3) (blueprint: lem-sfb-condensed-product-bar-comparison). -/
def productBarDegeneracy {P : Type u} [TopologicalSpace P] [Group P]
    (n : ℕ) (i : Fin (n + 1)) : C((Fin n → P), (Fin (n + 1) → P)) :=
  ContinuousMap.pi fun j ↦
    if h : j.val < i.val then ContinuousMap.eval (X := fun _ : Fin n ↦ P) ⟨j.val, by omega⟩
    else if h' : j.val = i.val then ContinuousMap.const _ 1
    else ContinuousMap.eval (X := fun _ : Fin n ↦ P) ⟨j.val - 1, by omega⟩

/-- Change the test object and the two parameter tuples simultaneously.
Source: blueprint paragraph (3) (blueprint: lem-sfb-condensed-product-bar-comparison). -/
def productBarParameterMap {S T : Profinite.{u}} (f : T ⟶ S)
    {a b c d : ℕ} (g : C((Fin c → G), (Fin a → G)))
    (h : C((Fin d → H), (Fin b → H))) :
    productBarParameters G H T c d ⟶ productBarParameters G H S a b :=
  ConcreteCategory.ofHom
    ((f.hom.hom.comp ContinuousMap.fst).prodMk
      ((g.comp (ContinuousMap.fst.comp ContinuousMap.snd)).prodMk
        (h.comp (ContinuousMap.snd.comp ContinuousMap.snd))))

/-- Project a parameter test object back to the original test object.
Source: blueprint paragraph (3) (blueprint: lem-sfb-condensed-product-bar-comparison). -/
def productBarProjection (S : Profinite.{u}) (a b : ℕ) :
    productBarParameters G H S a b ⟶ S :=
  ConcreteCategory.ofHom ContinuousMap.fst

/-- The action entering the first G face, as a section of the product condensed group.
Source: blueprint paragraph (3) (blueprint: lem-sfb-condensed-product-bar-comparison). -/
def productBarFirstG (S : Profinite.{u}) (a b : ℕ) :
    C(productBarParameters G H S (a + 1) b, G × H) :=
  ((ContinuousMap.eval 0).comp (ContinuousMap.fst.comp ContinuousMap.snd)).prodMk
    (ContinuousMap.const _ 1)

/-- The action entering the first H face, retaining the commuting G action.
Source: blueprint paragraph (3) (blueprint: lem-sfb-condensed-product-bar-comparison). -/
def productBarFirstH (S : Profinite.{u}) (a b : ℕ) :
    C(productBarParameters G H S a (b + 1), G × H) :=
  (ContinuousMap.const _ 1).prodMk
    ((ContinuousMap.eval 0).comp (ContinuousMap.snd.comp ContinuousMap.snd))

/-- Read a bicosimplicial module in bidegree (a,b).
Source: blueprint paragraph (3) (blueprint: lem-sfb-condensed-product-bar-comparison). -/
abbrev productBarEvaluation (a b : ℕ) :
    (SimplexCategory ⥤ SimplexCategory ⥤ Modules R) ⥤ Modules R :=
  (evaluation _ _).obj (SimplexCategory.mk a) ⋙
    (evaluation _ _).obj (SimplexCategory.mk b)

/-- A simultaneous internal-Hom bar, specified on every profinite test object.
The section formula is Hom(A[S × G^a × H^b],M), not continuous functions into
M evaluated at a point. The scalar, restriction and operator formulas fix the object
and all its maps. Source: blueprint paragraph (3)
(blueprint: lem-sfb-condensed-product-bar-comparison). -/
structure ProductBar where
  /-- Internal Hom from free represented modules, before resolving the second variable. -/
  cochains : ActionModule R (G × H) ⥤ (SimplexCategory ⥤ SimplexCategory ⥤ Modules R)
  /-- Postcomposition is additive. -/
  additive : cochains.Additive
  /-- The represented-free-module internal-Hom section identification. -/
  sections : ∀ (M : ActionModule R (G × H)) (a b : ℕ) (S : Profinite.{u}),
    sectionModule R ((productBarEvaluation R a b).obj (cochains.obj M)) S ≃+
      sectionModule R M.module (productBarParameters G H S a b)
  /-- Linearity uses restriction of scalars along the test-object projection. -/
  scalar : ∀ (M : ActionModule R (G × H)) (a b : ℕ) (S : Profinite.{u})
    (r : (InternalAbelianSheafModule.sectionRings
      (coherentTopology Profinite.{u}) R.X).obj (op S))
    (x : sectionModule R ((productBarEvaluation R a b).obj (cochains.obj M)) S),
    sections M a b S (r • x) =
      ((InternalAbelianSheafModule.sectionRings
        (coherentTopology Profinite.{u}) R.X).map
          (productBarProjection G H S a b).op r) • sections M a b S x
  /-- Restriction is pullback along the map on the test-object coordinate. -/
  restriction : ∀ (M : ActionModule R (G × H)) (a b : ℕ) (S T : Profinite.{u})
    (f : T ⟶ S)
    (x : sectionModule R ((productBarEvaluation R a b).obj (cochains.obj M)) S),
    sections M a b T
      ((((productBarEvaluation R a b).obj (cochains.obj M)).X.obj.map f.op).hom x) =
      (M.module.X.obj.map (productBarParameterMap G H f
        (ContinuousMap.id _) (ContinuousMap.id _)).op).hom (sections M a b S x)
  /-- Maps are postcomposition in the second variable of internal Hom. -/
  map_sections : ∀ (M N : ActionModule R (G × H)) (f : M ⟶ N)
    (a b : ℕ) (S : Profinite.{u})
    (x : sectionModule R ((productBarEvaluation R a b).obj (cochains.obj M)) S),
    sections N a b S
      (((((productBarEvaluation R a b).map (cochains.map f)).hom.hom.app (op S)).hom) x) =
      ((f.val.hom.hom.app (op (productBarParameters G H S a b))).hom)
        (sections M a b S x)
  /-- G cofaces, with the first coface acting on the target. -/
  faceG : ∀ (M : ActionModule R (G × H)) (a b : ℕ) (i : Fin (a + 2))
    (S : Profinite.{u})
    (x : sectionModule R ((productBarEvaluation R a b).obj (cochains.obj M)) S),
    sections M (a + 1) b S
      (((((cochains.obj M).map (SimplexCategory.δ i)).app
        (SimplexCategory.mk b)).hom.hom.app (op S)).hom x) =
      if i.val = 0 then
        M.act (productBarParameters G H S (a + 1) b) (productBarFirstG G H S a b)
          ((M.module.X.obj.map (productBarParameterMap G H (𝟙 S)
            (productBarFace a i) (ContinuousMap.id _)).op).hom (sections M a b S x))
      else (M.module.X.obj.map (productBarParameterMap G H (𝟙 S)
        (productBarFace a i) (ContinuousMap.id _)).op).hom (sections M a b S x)
  /-- H cofaces, with the first coface acting by the second factor. -/
  faceH : ∀ (M : ActionModule R (G × H)) (a b : ℕ) (i : Fin (b + 2))
    (S : Profinite.{u})
    (x : sectionModule R ((productBarEvaluation R a b).obj (cochains.obj M)) S),
    sections M a (b + 1) S
      (((((cochains.obj M).obj (SimplexCategory.mk a)).map
        (SimplexCategory.δ i)).hom.hom.app (op S)).hom x) =
      if i.val = 0 then
        M.act (productBarParameters G H S a (b + 1)) (productBarFirstH G H S a b)
          ((M.module.X.obj.map (productBarParameterMap G H (𝟙 S)
            (ContinuousMap.id _) (productBarFace b i)).op).hom (sections M a b S x))
      else (M.module.X.obj.map (productBarParameterMap G H (𝟙 S)
        (ContinuousMap.id _) (productBarFace b i)).op).hom (sections M a b S x)
  /-- G degeneracies insert the identity in the parameter tuple. -/
  degeneracyG : ∀ (M : ActionModule R (G × H)) (a b : ℕ) (i : Fin (a + 1))
    (S : Profinite.{u})
    (x : sectionModule R ((productBarEvaluation R (a + 1) b).obj (cochains.obj M)) S),
    sections M a b S
      (((((cochains.obj M).map (SimplexCategory.σ i)).app
        (SimplexCategory.mk b)).hom.hom.app (op S)).hom x) =
      (M.module.X.obj.map (productBarParameterMap G H (𝟙 S)
        (productBarDegeneracy a i) (ContinuousMap.id _)).op).hom
          (sections M (a + 1) b S x)
  /-- H degeneracies insert the identity in the second tuple. -/
  degeneracyH : ∀ (M : ActionModule R (G × H)) (a b : ℕ) (i : Fin (b + 1))
    (S : Profinite.{u})
    (x : sectionModule R ((productBarEvaluation R a (b + 1)).obj (cochains.obj M)) S),
    sections M a b S
      (((((cochains.obj M).obj (SimplexCategory.mk a)).map
        (SimplexCategory.σ i)).hom.hom.app (op S)).hom x) =
      (M.module.X.obj.map (productBarParameterMap G H (𝟙 S)
        (ContinuousMap.id _) (productBarDegeneracy b i)).op).hom
          (sections M a (b + 1) S x)
  /-- The degree-zero coaugmentation before taking invariants. -/
  augmentation : forgetAction ⟶ cochains ⋙ productBarEvaluation R 0 0
  /-- Its sections are pullback along the unique empty parameter tuples. -/
  augmentation_sections : ∀ (M : ActionModule R (G × H)) (S : Profinite.{u})
    (x : sectionModule R M.module S),
    sections M 0 0 S (((augmentation.app M).hom.hom.app (op S)).hom x) =
      (M.module.X.obj.map (productBarProjection G H S 0 0).op).hom x

attribute [instance] ProductBar.additive Invariants.additive ProductInvariants.additive

variable {R G H}

/-- The simultaneous resolution model, using the same resolution for every parameter.
Source: blueprint paragraph (3) (blueprint: lem-sfb-condensed-product-bar-comparison). -/
def ProductBar.onComplex (B : ProductBar R G H)
    (I : CochainComplex (ActionModule R (G × H)) ℕ) :
    (SimplexCategory ⥤ SimplexCategory ⥤ CochainComplex (Modules R) ℕ) :=
  ((B.cochains.mapHomologicalComplex (.up ℕ)).obj I).asFunctor ⋙
    HomologicalComplex.complexOfFunctorsToFunctorToComplex

/-- Diagonal double complex: cosimplicial degree first, resolution degree second.
Coordinate reordering identifies its nth column with the product-group bar.
Source: blueprint paragraph (3) (blueprint: lem-sfb-condensed-product-bar-comparison). -/
def ProductBar.diagonalDouble (B : ProductBar R G H)
    (I : CochainComplex (ActionModule R (G × H)) ℕ) :
    HomologicalComplex₂ (Modules R) (.up ℕ) (.up ℕ) :=
  (alternatingCofaceMapComplex _).obj
    (Functor.diag SimplexCategory ⋙ Functor.uncurry.obj (B.onComplex I))

/-- Iterated double complex: H and resolution totalized before the G direction.
The resulting differential is dG + (-1)^a dH + (-1)^(a+b) dres.
Source: blueprint paragraph (3) (blueprint: lem-sfb-condensed-product-bar-comparison). -/
def ProductBar.iteratedDouble (B : ProductBar R G H)
    (I : CochainComplex (ActionModule R (G × H)) ℕ) :
    HomologicalComplex₂ (Modules R) (.up ℕ) (.up ℕ) :=
  (alternatingCofaceMapComplex _).obj
    (B.onComplex I ⋙ alternatingCofaceMapComplex _ ⋙
      HomologicalComplex₂.totalFunctor (Modules R) (.up ℕ) (.up ℕ) (.up ℕ))

/-- The finite-diagonal total of the diagonal bar model.
Source: blueprint paragraph (3) (blueprint: lem-sfb-condensed-product-bar-comparison). -/
def ProductBar.diagonalTotal (B : ProductBar R G H)
    (I : CochainComplex (ActionModule R (G × H)) ℕ) : CochainComplex (Modules R) ℕ :=
  (B.diagonalDouble I).total (.up ℕ)

/-- The H-first iterated finite-diagonal total.
Source: blueprint paragraph (3) (blueprint: lem-sfb-condensed-product-bar-comparison). -/
def ProductBar.iteratedTotal (B : ProductBar R G H)
    (I : CochainComplex (ActionModule R (G × H)) ℕ) : CochainComplex (Modules R) ℕ :=
  (B.iteratedDouble I).total (.up ℕ)

/-- A map of compatible resolution models, by postcomposition in every term.
Source: blueprint paragraph (3) (blueprint: lem-sfb-condensed-product-bar-comparison). -/
def ProductBar.onComplexMap (B : ProductBar R G H)
    {I J : CochainComplex (ActionModule R (G × H)) ℕ} (f : I ⟶ J) :
    B.onComplex I ⟶ B.onComplex J :=
  Functor.whiskerRight (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map
    ((B.cochains.mapHomologicalComplex (.up ℕ)).map f))
      HomologicalComplex.complexOfFunctorsToFunctorToComplex

/-- The induced map on diagonal totals, for any lift of a module map to resolutions.
Source: blueprint paragraph (3) (blueprint: lem-sfb-condensed-product-bar-comparison). -/
def ProductBar.diagonalMap (B : ProductBar R G H)
    {I J : CochainComplex (ActionModule R (G × H)) ℕ} (f : I ⟶ J) :
    B.diagonalTotal I ⟶ B.diagonalTotal J :=
  HomologicalComplex₂.total.map
    ((alternatingCofaceMapComplex _).map
      (Functor.whiskerLeft (Functor.diag SimplexCategory) (Functor.uncurry.map (B.onComplexMap f))))
        (.up ℕ)

/-- The induced map on H-first iterated totals.
Source: blueprint paragraph (3) (blueprint: lem-sfb-condensed-product-bar-comparison). -/
def ProductBar.iteratedMap (B : ProductBar R G H)
    {I J : CochainComplex (ActionModule R (G × H)) ℕ} (f : I ⟶ J) :
    B.iteratedTotal I ⟶ B.iteratedTotal J :=
  HomologicalComplex₂.total.map
    ((alternatingCofaceMapComplex _).map
      (Functor.whiskerRight (B.onComplexMap f) (alternatingCofaceMapComplex _ ⋙
        HomologicalComplex₂.totalFunctor (Modules R) (.up ℕ) (.up ℕ) (.up ℕ)))) (.up ℕ)

/-- The diagonal total's summand in cosimplicial degree zero.
Source: blueprint paragraph (3) (blueprint: lem-sfb-condensed-product-bar-comparison). -/
def ProductBar.diagonalZero (B : ProductBar R G H)
    (I : CochainComplex (ActionModule R (G × H)) ℕ) (q : ℕ) :
    (productBarEvaluation R 0 0).obj (B.cochains.obj (I.X q)) ⟶
      (B.diagonalTotal I).X q :=
  (B.diagonalDouble I).ιTotal (.up ℕ) 0 q q (Nat.zero_add q)

/-- The iterated total's summand in both cosimplicial degrees zero.
Source: blueprint paragraph (3) (blueprint: lem-sfb-condensed-product-bar-comparison). -/
def ProductBar.iteratedZero (B : ProductBar R G H)
    (I : CochainComplex (ActionModule R (G × H)) ℕ) (q : ℕ) :
    (productBarEvaluation R 0 0).obj (B.cochains.obj (I.X q)) ⟶
      (B.iteratedTotal I).X q :=
  HomologicalComplex₂.ιTotal
    ((alternatingCofaceMapComplex _).obj ((B.onComplex I).obj (SimplexCategory.mk 0)))
      (.up ℕ) 0 q q (Nat.zero_add q) ≫
    (B.iteratedDouble I).ιTotal (.up ℕ) 0 q q (Nat.zero_add q)


/-- The two actual invariant augmentations into the compatible bar totals. Their components
are prescribed, so no arbitrary comparison map is an input.
Source: blueprint paragraph (3) (blueprint: lem-sfb-condensed-product-bar-comparison). -/
structure ProductBarAugmentations (B : ProductBar R G H)
    (dG : Invariants R G) (dHG : ProductInvariants R G H)
    (dGH : Invariants R (G × H))
    (I : CochainComplex (ActionModule R (G × H)) ℕ) where
  /-- Direct invariant augmentation. -/
  diagonal : (dGH.functor.mapHomologicalComplex (.up ℕ)).obj I ⟶ B.diagonalTotal I
  /-- Successive H then G invariant augmentation. -/
  iterated : ((dHG.functor ⋙ dG.functor).mapHomologicalComplex (.up ℕ)).obj I ⟶
    B.iteratedTotal I
  /-- Direct augmentation is supported in diagonal cosimplicial degree zero. -/
  diagonal_f : ∀ q : ℕ, diagonal.f q =
    dGH.inclusion.app (I.X q) ≫ B.augmentation.app (I.X q) ≫ B.diagonalZero I q
  /-- Successive augmentation is supported in bidegree (0,0). -/
  iterated_f : ∀ q : ℕ, iterated.f q =
    dG.inclusion.app (dHG.functor.obj (I.X q)) ≫ dHG.inclusion.app (I.X q) ≫
      B.augmentation.app (I.X q) ≫ B.iteratedZero I q

variable [HasDerivedCategory.{u + 2} (Modules R)]
  [HasDerivedCategory.{u + 2} (ActionModule R G)]
  [HasDerivedCategory.{u + 2} (ActionModule R (G × H))]

/-- Localization after extension by zero from nonnegative to integer degrees.
Source: blueprint paragraph (3) (blueprint: lem-sfb-condensed-product-bar-comparison). -/
abbrev productBarQ {C : Type (u + 2)} [Category.{u + 1} C] [Abelian C]
    [HasDerivedCategory.{u + 2} C] : CochainComplex C ℕ ⥤ DerivedCategory C :=
  ComplexShape.embeddingUpNat.extendFunctor C ⋙ DerivedCategory.Q

/-- The composite right-derived unit on an ordinary compatible complex.
Source: blueprint paragraph (3) (blueprint: lem-sfb-condensed-product-bar-comparison). -/
def productBarIteratedUnit (dG : Invariants R G) (dHG : ProductInvariants R G H)
    (I : CochainComplex (ActionModule R (G × H)) ℕ) :
    DerivedCategory.Q.obj ((dG.functor.mapHomologicalComplex (.up ℤ)).obj
      ((dHG.functor.mapHomologicalComplex (.up ℤ)).obj
        (I.extend ComplexShape.embeddingUpNat))) ⟶
    (dHG.functor.rightDerivedFunctor ⋙ dG.functor.rightDerivedFunctor).obj
      (productBarQ.obj I) :=
  dG.functor.rightDerivedFunctorUnitQ
    ((dHG.functor.mapHomologicalComplex (.up ℤ)).obj
      (I.extend ComplexShape.embeddingUpNat)) ≫
    dG.functor.rightDerivedFunctor.map
      (dHG.functor.rightDerivedFunctorUnitQ (I.extend ComplexShape.embeddingUpNat))

/-- The canonical ordinary comparison from direct to successive invariants, termwise.
Source: blueprint paragraph (3), specified inflation adjunctions
(blueprint: lem-sfb-condensed-product-bar-comparison). -/
def productBarInvariantMap (dG : Invariants R G) (dHG : ProductInvariants R G H)
    (dGH : Invariants R (G × H))
    (h : trivial (R := R) (P := G × H) =
      trivial (R := R) (P := G) ⋙ inflate (R := R) (ContinuousMonoidHom.fst G H))
    (I : CochainComplex (ActionModule R (G × H)) ℕ) :
    (dGH.functor.mapHomologicalComplex (.up ℕ)).obj I ⟶
      ((dHG.functor ⋙ dG.functor).mapHomologicalComplex (.up ℕ)).obj I :=
  (NatTrans.mapHomologicalComplex
    (conjugateIsoEquiv dGH.adjunction (dG.adjunction.comp dHG.adjunction)
      (eqToIso h.symm)).hom (.up ℕ)).app I

/-- The two augmentations are quasi-isomorphisms on an injective resolution.
This structure contains no unspecified maps: their components are prescribed in the parent.
Source: blueprint paragraph (3) (blueprint: lem-sfb-condensed-product-bar-comparison). -/
structure ProductBarQuasiAugmentations (B : ProductBar R G H)
    (dG : Invariants R G) (dHG : ProductInvariants R G H)
    (dGH : Invariants R (G × H))
    (I : CochainComplex (ActionModule R (G × H)) ℕ)
    extends ProductBarAugmentations B dG dHG dGH I where
  /-- The diagonal invariant augmentation is a quasi-isomorphism. -/
  diagonal_quasiIso : QuasiIso diagonal
  /-- The successive invariant augmentation is a quasi-isomorphism. -/
  iterated_quasiIso : QuasiIso iterated

attribute [instance] ProductBarQuasiAugmentations.diagonal_quasiIso
  ProductBarQuasiAugmentations.iterated_quasiIso

/-- The augmented product-nerve comparison, H first and G second, is uniquely determined
in the derived category by its value on the invariant augmentation. This formula uses
both actual augmentations and the ordinary adjunction comparison between their sources.
Source: blueprint paragraph (3) (blueprint: lem-sfb-condensed-product-bar-comparison). -/
def ProductBarQuasiAugmentations.comparison {B : ProductBar R G H}
    {dG : Invariants R G} {dHG : ProductInvariants R G H}
    {dGH : Invariants R (G × H)}
    {I : CochainComplex (ActionModule R (G × H)) ℕ}
    (j : ProductBarQuasiAugmentations B dG dHG dGH I)
    (h : trivial (R := R) (P := G × H) =
      trivial (R := R) (P := G) ⋙ inflate (R := R) (ContinuousMonoidHom.fst G H)) :
    productBarQ.obj (B.diagonalTotal I) ⟶ productBarQ.obj (B.iteratedTotal I) :=
  (asIso (DerivedCategory.Q.map
    (HomologicalComplex.extendMap j.diagonal ComplexShape.embeddingUpNat))).inv ≫
    productBarQ.map (productBarInvariantMap dG dHG dGH h I) ≫ productBarQ.map j.iterated

/-- The resolution identifies N[0] with its chosen injective complex in the ordinary
unbounded derived category. Source: blueprint paragraph (3)
(blueprint: lem-sfb-condensed-product-bar-comparison). -/
def productBarResolutionIso (N : ActionModule R (G × H)) (I : InjectiveResolution N) :
    productBarQ.obj ((CochainComplex.single₀ _).obj N) ≅ productBarQ.obj I.cocomplex :=
  asIso (DerivedCategory.Q.map
    (HomologicalComplex.extendMap I.ι ComplexShape.embeddingUpNat))

/-- The specified right-derived comparison, the conjugate of the derived inflation
identification under the specified adjunctions. Source: blueprint paragraph (3)
(blueprint: lem-sfb-condensed-product-bar-comparison). -/
def productBarDerivedComparison (dG : Invariants R G) (dHG : ProductInvariants R G H)
    (dGH : Invariants R (G × H))
    (h : trivial (R := R) (P := G × H) =
      trivial (R := R) (P := G) ⋙ inflate (R := R) (ContinuousMonoidHom.fst G H)) :
    dGH.functor.rightDerivedFunctor ≅
      dHG.functor.rightDerivedFunctor ⋙ dG.functor.rightDerivedFunctor :=
  conjugateIsoEquiv dGH.adjunction.mapDerivedCategoryRightDerivedAdjunction
    (dG.adjunction.mapDerivedCategoryRightDerivedAdjunction.comp
      dHG.adjunction.mapDerivedCategoryRightDerivedAdjunction)
    (Adjunction.derivedCompositionLeftIso
      (trivial (R := R) (P := G))
      (inflate (R := R) (ContinuousMonoidHom.fst G H))
      (trivial (R := R) (P := G × H)) (eqToIso h))

/-- Normalized derived identifications of the two totalizations on a chosen resolution.
The two unit equations specify the actual K-injective derived comparisons, preventing an
arbitrary isomorphism from changing the normalization. Source: blueprint paragraph (3)
(blueprint: lem-sfb-condensed-product-bar-comparison). -/
structure ProductBarResolutionComparison (B : ProductBar R G H)
    (dG : Invariants R G) (dHG : ProductInvariants R G H)
    (dGH : Invariants R (G × H))
    (h : trivial (R := R) (P := G × H) =
      trivial (R := R) (P := G) ⋙ inflate (R := R) (ContinuousMonoidHom.fst G H))
    (N : ActionModule R (G × H)) (I : InjectiveResolution N) where
  /-- The augmentations, with their prescribed components and quasi-isomorphisms. -/
  augmentations : ProductBarQuasiAugmentations B dG dHG dGH I.cocomplex
  /-- The diagonal derived identification on N in degree zero. -/
  diagonalIso : dGH.functor.rightDerivedFunctor.obj
      (productBarQ.obj ((CochainComplex.single₀ _).obj N)) ≅
    productBarQ.obj (B.diagonalTotal I.cocomplex)
  /-- The successive derived identification, retaining G invariants after H invariants. -/
  iteratedIso : (dHG.functor.rightDerivedFunctor ⋙ dG.functor.rightDerivedFunctor).obj
      (productBarQ.obj ((CochainComplex.single₀ _).obj N)) ≅
    productBarQ.obj (B.iteratedTotal I.cocomplex)
  /-- The direct identification is normalized by the invariant inclusion and derived unit. -/
  diagonal_normalization :
    dGH.functor.rightDerivedFunctorUnitQ (I.cocomplex.extend ComplexShape.embeddingUpNat) ≫
      (dGH.functor.rightDerivedFunctor.mapIso (productBarResolutionIso N I)).inv ≫
        diagonalIso.hom =
      DerivedCategory.Q.map
        (HomologicalComplex.mapExtendIso I.cocomplex ComplexShape.embeddingUpNat
          dGH.functor).hom ≫ productBarQ.map augmentations.diagonal
  /-- The successive identification uses the two successive right-derived units. -/
  iterated_normalization :
    productBarIteratedUnit dG dHG I.cocomplex ≫
      ((dHG.functor.rightDerivedFunctor ⋙ dG.functor.rightDerivedFunctor).mapIso
        (productBarResolutionIso N I)).inv ≫ iteratedIso.hom =
      DerivedCategory.Q.map
        ((dG.functor.mapHomologicalComplex (.up ℤ)).map
          (HomologicalComplex.mapExtendIso I.cocomplex ComplexShape.embeddingUpNat
            dHG.functor).hom) ≫
      DerivedCategory.Q.map
        (HomologicalComplex.mapExtendIso
          ((dHG.functor.mapHomologicalComplex (.up ℕ)).obj I.cocomplex)
          ComplexShape.embeddingUpNat dG.functor).hom ≫
      productBarQ.map augmentations.iterated
  /-- Equality of the comparison arrows in the derived category, with this normalization. -/
  comparison_eq : diagonalIso.hom ≫ augmentations.comparison h ≫ iteratedIso.inv =
    (productBarDerivedComparison dG dHG dGH h).hom.app
      (productBarQ.obj ((CochainComplex.single₀ _).obj N))

/-- Product and successive internal bars identify the ordinary derived invariants,
naturally in every module, with the specified augmentation normalization of the
comparison arrow. Source: blueprint direct-image stability, paragraph (3), formal
product-to-successive augmented-bar input
(blueprint: lem-sfb-condensed-product-bar-comparison).

Proof:
1. `lem-sfb-condensed-product-action-inflation` supplies Grothendieck action categories
   and exact inflation. Resolve N nonnegatively by equivariant injectives using
   `lem-sp-grothendieck-enough-injectives`. They and their H invariants are K-injective
   by `lem-weil-pbc-bounded-below-injectives-kinjective` and the injective-preserving
   right-adjoint result `lem-sp-right-adjoint-preserves-injectives`.
2. Use `sk-def-sfb-sheaf-tensor` and
   `def-weil-pbc-internal-abelian-sheaf-module-equivalence` to retain sections and
   restrictions. Free A[P] is the sheafification of the free module on represented P,
   hence j-shriek of the unit and flat by `lem-pc-sites-modules-j-shriek-flat`.
   Induction A[P] tensor - is therefore an exact left adjoint to forgetting actions;
   restriction to H and the underlying modules of I and I^H remain injective.
3. The tensor-Hom adjunction `lem-pc-sheaf-modules-tensor-closed` identifies internal
   Hom sections with I(S × G^a × H^b). Build both group nerves on the SAME resolution.
   First faces act on I; they commute because the factor actions commute. All other
   operators change only their own parameter tuples and commute with the resolution
   differential. Thus these columns compute DERIVED internal Hom, using
   `lem-sp-derived-injective-resolution-naturality`.
4. Reorder (G × H)^n as G^n × H^n, including action faces and unit insertions.
   `lem-sfb-condensed-derived-invariant-bar` identifies the diagonal total with direct
   derived invariants by the degree-zero invariant augmentation.
5. For the successive H augmentation test on every profinite S. The augmented row is
   equivariant Hom from A[S] tensor A[G^a] tensor the homogeneous H bar into I^q.
   `lem-sfb-condensed-internal-bar-resolution` makes the tensor bar exact. Injectivity
   after restriction to H makes Hom exact, by extension across images and passage
   to quotients. Its degree-zero kernel is internal Hom(A[G^a],(I^q)^H), with G action.
6. Apply `lem-sc-first-quadrant-total-column-comparison` first in (b,q), then in a.
   Switching the two total conventions contributes (-1)^(b*q). The finite total
   has differential dG + (-1)^a dH + (-1)^(a+b) dres, as in `def-sp-double-complex-total`.
7. Apply the homogeneous G bar to the G-injective (I^q)^H. The same sectionwise
   image-and-quotient argument and first-quadrant comparison give the successive
   augmentation from ((I^q)^H)^G. The complex I^H is K-injective, so these are the
   TWO successive derived functors, not a bar applied only to N^H in degree zero.
8. `lem-sfb-bicosimplicial-shuffle-totalization` gives the diagonal-to-iterated map.
   Its augmentation clause says that it carries the direct augmentation to the
   successive one, after the ordinary invariant comparison. Since the former is
   a quasi-isomorphism, this uniquely identifies its derived arrow with `comparison`.
9. `lem-sfb-derived-composition-adjunction-normalization` represents the conjugate
   derived comparison on I by that same ordinary invariant comparison. The two
   displayed derived-unit normalizations therefore imply `comparison_eq` as an
   equality of derived arrows, not merely of their cohomology maps.
10. For N to M use `lem-weil-pbc-injective-resolution-lift-exists`; every lift induces
    all bar maps by postcomposition. By `lem-weil-pbc-lift-to-injective-unique-up-to-homotopy`
    different lifts are homotopic. Multiply the vertical homotopy in (a,b,q) by
    (-1)^(a+b), and on the diagonal by (-1)^a. The cross terms cancel. The normalized
    resolution naturality then gives all three naturality equations below, including
    independence of the resolution when the module map is the identity.
11. Trivial factors use the unnormalized constant nerve; its positive terms need not
    vanish. The same augmentations and shuffle apply. For N=0 use the zero resolution.
    All diagonals are finite; neither exact infinite products nor projectivity of free
    profinite modules nor an underived continuous-function model has been assumed.
-/
theorem condensed_product_bar_comparison
    (dG : Invariants R G) (dHG : ProductInvariants R G H)
    (dGH : Invariants R (G × H))
    (h : trivial (R := R) (P := G × H) =
      trivial (R := R) (P := G) ⋙ inflate (R := R) (ContinuousMonoidHom.fst G H)) :
    ∃ (B : ProductBar R G H)
      (c : ∀ (N : ActionModule R (G × H)) (I : InjectiveResolution N),
        ProductBarResolutionComparison B dG dHG dGH h N I),
      ∀ (N M : ActionModule R (G × H)) (f : N ⟶ M)
        (I : InjectiveResolution N) (J : InjectiveResolution M)
        (g : I.cocomplex ⟶ J.cocomplex)
        (_hg : I.ι ≫ g = (CochainComplex.single₀ _).map f ≫ J.ι),
        dGH.functor.rightDerivedFunctor.map
            (productBarQ.map ((CochainComplex.single₀ _).map f)) ≫
            (c M J).diagonalIso.hom =
          (c N I).diagonalIso.hom ≫ productBarQ.map (B.diagonalMap g) ∧
        (dHG.functor.rightDerivedFunctor ⋙ dG.functor.rightDerivedFunctor).map
            (productBarQ.map ((CochainComplex.single₀ _).map f)) ≫
            (c M J).iteratedIso.hom =
          (c N I).iteratedIso.hom ≫ productBarQ.map (B.iteratedMap g) ∧
        productBarQ.map (B.diagonalMap g) ≫ (c M J).augmentations.comparison h =
          (c N I).augmentations.comparison h ≫ productBarQ.map (B.iteratedMap g) := by
  sorry

end Profinite.CondensedAction
