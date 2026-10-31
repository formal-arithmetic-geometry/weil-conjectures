/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.RingTheory.EssentialFiniteness
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.Algebra.Module.LocalizedModule.Basic

/-! # Local algebra approximation systems

Source: Stacks Project, Algebra, Tag 046Y, middle proof paragraph and the approximation
system preceding it (blueprint: def-trf-local-algebra-approximation-system).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

/-- The local ring diagrams and finite module diagram used in Stacks Project, Algebra,
Tag 046Y. Functors encode identity/composition, cocones encode compatibility, and
`IsColimit` uses the actual ring and abelian group categories. Localization witnesses
and scalar extension isomorphisms are pinned on pure tensors; none is an arbitrary map.
The universal algebra binders permit exactly the algebra structure of the specified
transition, without choosing actions at incomparable indices.
(blueprint: def-trf-local-algebra-approximation-system) -/
structure LocalAlgebraApproximationSystem where
  /-- The common small directed index set. -/
  I : Type u
  [preorder : Preorder I]
  [nonempty : Nonempty I]
  [directed : IsDirected I (· ≤ ·)]
  /-- The two diagrams of rings. -/
  R : I ⥤ CommRingCat.{u}
  S : I ⥤ CommRingCat.{u}
  /-- Their specified colimit cocones. -/
  r : Cocone R
  s : Cocone S
  colimitR : IsColimit r
  colimitS : IsColimit s
  [localR : ∀ i : I, IsLocalRing (R.obj i)]
  [localS : ∀ i : I, IsLocalRing (S.obj i)]
  [localLimitR : IsLocalRing r.pt]
  [localLimitS : IsLocalRing s.pt]
  [stageAlgebra : ∀ i : I, Algebra (R.obj i) (S.obj i)]
  [limitAlgebra : Algebra r.pt s.pt]
  [stageLocal : ∀ i : I, IsLocalHom (algebraMap (R.obj i) (S.obj i))]
  [limitLocal : IsLocalHom (algebraMap r.pt s.pt)]
  [transitionLocalR : ∀ i j : I, ∀ h : i ≤ j, IsLocalHom (R.map (homOfLE h)).hom]
  [transitionLocalS : ∀ i j : I, ∀ h : i ≤ j, IsLocalHom (S.map (homOfLE h)).hom]
  [coconeLocalR : ∀ i : I, IsLocalHom (r.ι.app i).hom]
  [coconeLocalS : ∀ i : I, IsLocalHom (s.ι.app i).hom]
  square : ∀ i j : I, ∀ h : i ≤ j,
    (S.map (homOfLE h)).hom.comp (algebraMap (R.obj i) (S.obj i)) =
      (algebraMap (R.obj j) (S.obj j)).comp (R.map (homOfLE h)).hom
  coconeSquare : ∀ i : I,
    (algebraMap r.pt s.pt).comp (r.ι.app i).hom =
      (s.ι.app i).hom.comp (algebraMap (R.obj i) (S.obj i))
  /-- The explicit algebraic element and equality criteria of the ring colimits. -/
  repR : ∀ x : r.pt, ∃ i : I, ∃ y : R.obj i, r.ι.app i y = x
  eqR : ∀ (i j : I) (x : R.obj i) (y : R.obj j), r.ι.app i x = r.ι.app j y →
    ∃ (l : I) (hi : i ≤ l) (hj : j ≤ l),
      R.map (homOfLE hi) x = R.map (homOfLE hj) y
  repS : ∀ x : s.pt, ∃ i : I, ∃ y : S.obj i, s.ι.app i y = x
  eqS : ∀ (i j : I) (x : S.obj i) (y : S.obj j), s.ι.app i x = s.ι.app j y →
    ∃ (l : I) (hi : i ≤ l) (hj : j ≤ l),
      S.map (homOfLE hi) x = S.map (homOfLE hj) y
  /-- The module diagram and its specified abelian group colimit. -/
  M : I ⥤ AddCommGrpCat.{u}
  μ : Cocone M
  colimitM : IsColimit μ
  [stageModule : ∀ i : I, Module (S.obj i) (M.obj i)]
  [limitModule : Module s.pt μ.pt]
  [baseModule : ∀ i : I, Module (R.obj i) (M.obj i)]
  [baseTower : ∀ i : I, IsScalarTower (R.obj i) (S.obj i) (M.obj i)]
  [limitBaseModule : Module r.pt μ.pt]
  [limitTower : IsScalarTower r.pt s.pt μ.pt]
  [finiteStage : ∀ i : I, Module.Finite (S.obj i) (M.obj i)]
  semilinear : ∀ (i j : I) (h : i ≤ j) (a : S.obj i) (x : M.obj i),
    M.map (homOfLE h) (a • x) = S.map (homOfLE h) a • M.map (homOfLE h) x
  coconeSemilinear : ∀ (i : I) (a : S.obj i) (x : M.obj i),
    μ.ι.app i (a • x) = (@id s.pt (s.ι.app i a)) • (@id μ.pt (μ.ι.app i x))
  [essentiallyFiniteType : ∀ i : I, Algebra.EssFiniteType (R.obj i) (S.obj i)]
  /-- The induced action on the residue field of the limit. -/
  [residueAlgebra : ∀ i : I, Algebra (R.obj i) (IsLocalRing.ResidueField r.pt)]
  residueAlgebraMap : ∀ i : I,
    algebraMap (R.obj i) (IsLocalRing.ResidueField r.pt) =
      (IsLocalRing.residue r.pt).comp (r.ι.app i).hom
  /-- Each canonical transition of algebras is a localization at some submonoid.
  The structure `IsLocalization` gives units, fractions and the equality criterion. -/
  localization : ∀ (i j : I) (h : i ≤ j) [_a : Algebra (R.obj i) (R.obj j)],
    algebraMap (R.obj i) (R.obj j) = (R.map (homOfLE h)).hom →
    ∃ (W : Submonoid (S.obj i ⊗[R.obj i] R.obj j))
      (g : (S.obj i ⊗[R.obj i] R.obj j) →+* S.obj j),
      (∀ (x : S.obj i) (y : R.obj j),
        g (x ⊗ₜ[R.obj i] y) = S.map (homOfLE h) x * algebraMap (R.obj j) (S.obj j) y) ∧
      @IsLocalization _ _ W _ _ g.toAlgebra
  /-- The canonical scalar extension map of modules is an isomorphism. Its pure
  tensor formula also forces linearity over the target algebra. -/
  moduleBaseChange : ∀ (i j : I) (h : i ≤ j) [_a : Algebra (S.obj i) (S.obj j)],
    algebraMap (S.obj i) (S.obj j) = (S.map (homOfLE h)).hom →
    ∃ e : (M.obj i ⊗[S.obj i] S.obj j) ≃+ M.obj j,
      ∀ (x : M.obj i) (b : S.obj j), e (x ⊗ₜ[S.obj i] b) = b • M.map (homOfLE h) x

attribute [instance] LocalAlgebraApproximationSystem.preorder
  LocalAlgebraApproximationSystem.nonempty LocalAlgebraApproximationSystem.directed
  LocalAlgebraApproximationSystem.localR LocalAlgebraApproximationSystem.localS
  LocalAlgebraApproximationSystem.localLimitR LocalAlgebraApproximationSystem.localLimitS
  LocalAlgebraApproximationSystem.stageAlgebra LocalAlgebraApproximationSystem.limitAlgebra
  LocalAlgebraApproximationSystem.stageLocal LocalAlgebraApproximationSystem.limitLocal
  LocalAlgebraApproximationSystem.transitionLocalR LocalAlgebraApproximationSystem.transitionLocalS
  LocalAlgebraApproximationSystem.coconeLocalR LocalAlgebraApproximationSystem.coconeLocalS
  LocalAlgebraApproximationSystem.stageModule LocalAlgebraApproximationSystem.limitModule
  LocalAlgebraApproximationSystem.baseModule LocalAlgebraApproximationSystem.baseTower
  LocalAlgebraApproximationSystem.limitBaseModule LocalAlgebraApproximationSystem.limitTower
  LocalAlgebraApproximationSystem.finiteStage
  LocalAlgebraApproximationSystem.essentiallyFiniteType
  LocalAlgebraApproximationSystem.residueAlgebra
