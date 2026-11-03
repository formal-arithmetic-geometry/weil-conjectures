/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerCalculus.CoefficientTowerShriekInterfaces
import WeilConjectures.AlgebraicGeometry.SpTowerCalculus.CoefficientTowerShriekInterfaces
import WeilConjectures.AlgebraicGeometry.Finite.FiniteCtfTriangulated
import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantModuleConstructibility
import Mathlib.CategoryTheory.Triangulated.Subcategory
import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.AlgebraicGeometry.TowerOpenCover.TowerOpenCoverTriangleData
import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExact
import WeilConjectures.Algebra.Homology.OpenDerivedMatePresentation
import WeilConjectures.Algebra.Homology.OpenCoverMateComplexShortExact
import WeilConjectures.AlgebraicGeometry.ProEtale.Ringed.ProEtaleRingedOpenComparison
import WeilConjectures.Algebra.Homology.Scalar.ScalarExtensionRingIsoSupplement
import WeilConjectures.Algebra.Homology.SubterminalLocal.SubterminalModuleLocalCalculus
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsSupplement
import WeilConjectures.AlgebraicGeometry.RingedRestrictionExchange.ProEtaleRingedOpenCoverReflectsIso
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
import WeilConjectures.AlgebraicGeometry.SpTowerShriek.TowerOpenAdjunctionEvaluation
import WeilConjectures.Algebra.Homology.RingedOpenScalar.RingedOpenScalarAdjunction
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import WeilConjectures.AlgebraicGeometry.Finite.Ring.FiniteRingConstructibleDerivedOrigin
import WeilConjectures.SixFunctors.Supporting.PullbackTorAmplitude
import WeilConjectures.SixFunctors.Etale.Derived.Stability.Basic
import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.FlatModel
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Mathlib.CategoryTheory.Triangulated.Opposite.Functor
import Mathlib.CategoryTheory.Triangulated.Opposite.Subcategory
import Mathlib.CategoryTheory.Triangulated.Yoneda
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.CategoryTheory.Abelian.DiagramLemmas.Four

/- Source anchor for this transported binary-gluing step:
`det-sp-tower-gluing`, Gluing and Uniformity, in the current blueprint at
`part-duality-trace-formula/sec-smooth-purity/sec-sp-grp-ladic-summary/`
`sec-towers-and-integral-coefficients/sk-prop-sp-tower-geometric/`
`sk-prop-sp-tower-geometric-gluing.proof.md`.
-/

/-! # Local-to-global representability for an existing tower counit

Source: latest smooth-purity blueprint, Local pairs, Gluing and Uniformity.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u v
open CategoryTheory CategoryTheory.Limits Opposite
open scoped ZeroObject
open AlgebraicGeometry AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.ProEtale.SpTowerGluing

open CategoryTheory.Pretriangulated.Opposite

section Homological

open CategoryTheory.Pretriangulated

variable {A : Type*} [Category* A] [HasZeroObject A] [Preadditive A]
  [HasShift A ℤ] [∀ n : ℤ, (shiftFunctor A n).Additive] [Pretriangulated A]
  {B : Type*} [Category* B] [Abelian B]

omit [HasZeroObject A] [Preadditive A] [∀ n : ℤ, (shiftFunctor A n).Additive]
  [Pretriangulated A] [Abelian B] in
omit [HasZeroObject A] [Preadditive A] [∀ n : ℤ, (shiftFunctor A n).Additive]
  [Pretriangulated A] [Abelian B] in
end Homological

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
  (q : SpTowerCalculus.Coordinates l E b)

/-- An existing counit is representing if its restrictions represent on all nonempty
finite intersections of a finite open cover.
Source: latest blueprint `sk-prop-sp-tower-geometric-gluing.proof.md`, Gluing, five-lemma
argument (blueprint: lem-sp-tower-local-counit-representability).

Proof. First take a binary cover. Apply Hom(-,H) to the distinguished open-cover triangle
of every test object M. Apply Hom(-,K) after compact support to obtain the second exact row;
M is bounded below since it is uniformly bounded constructible. The two rows form a
commutative diagram under t ↦ F(t) followed by eps, including the boundary and shifts.
Open adjunction and open compact-support composition identify its local columns with the
assumed representing maps, evaluated also at shifted test objects. Biproducts identify
the two-chart column. The four exterior maps in the five-term segment are bijective, so
the abelian five lemma gives bijectivity of the middle map. For a finite cover induct on
its size: the union of the preceding opens and its intersection with the new open have
smaller covers; their finite intersections satisfy the same hypothesis by the compositor
and open-counit equations. The empty cover forces the source empty, whose derived tower
category and Hom groups are zero. No smoothness, perfectness of k, finite exceptional
adjunction or coefficient evaluation is used. This proves a property of the supplied
object and counit and makes no object or counit choice. -/
theorem tower_local_hom_criterion
    (k : Type u) [Field k]
    (X Y : Over (Spec (CommRingCat.of k)))
    [IsSeparated X.hom] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [IsSeparated Y.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
    (f : X ⟶ Y) (c : Compactification f.left)
    (hF : ∀ M : SpTowerCalculus.C l E b q X.left,
      spConstructibleTorTowers l E Y.left (q.abelian Y.left)
        ((SpTowerCalculus.F l E b o q c).obj M.obj))
    (K : SpTowerCalculus.C l E b q Y.left)
    (H : SpTowerCalculus.C l E b q X.left)
    (eps : (towerSupport l E b o q c hF).obj H ⟶ K)
    (n : ℕ) (U : Fin n → X.left.Opens) (_cover : iSup U = ⊤)
    (_local :
    ∀ (s : Finset (Fin n)), s.Nonempty →
      ∀ M : SpTowerCalculus.C l E b q (s.inf U).toScheme,
        Function.Bijective (fun a : M.obj ⟶
            (SpTowerCalculus.etalePullback l E b o q (s.inf U).ι).obj H.obj ↦
          (SpTowerCalculus.F l E b o q (c.precomp (s.inf U).ι)).map a ≫
            (SpTowerCalculus.openComposition l E b o q (s.inf U).ι c).inv.app
              ((SpTowerCalculus.etalePullback l E b o q (s.inf U).ι).obj H.obj) ≫
            (SpTowerCalculus.F l E b o q c).map
              ((towerOpenAdjunction l E b o q (s.inf U).ι).counit.app H.obj) ≫ eps.hom)) :
    ∀ M : SpTowerCalculus.C l E b q X.left,
      Function.Bijective (fun a : M ⟶ H ↦
        (towerSupport l E b o q c hF).map a ≫ eps) := by
  let := (q.abelian X.left).hasDerived
  let := (q.abelian Y.left).hasDerived
  let := b.realizationAdditive X.left
  let := b.realizationAdditive Y.left
  let := b.kinjective c.Z
  let F := SpTowerCalculus.F l E b o q c
  let _ : F.CommShift ℤ := by
    change ((b.realization X.left).functor.mapDerivedCategory ⋙
      ((o.openOp c.i).extension.mapDerivedCategory ⋙
        (o.geometry c.g).push.rightDerivedFunctor) ⋙
      (b.realization Y.left).inverse.mapDerivedCategory).CommShift ℤ
    infer_instance
  have : F.IsTriangulated := by
    change ((b.realization X.left).functor.mapDerivedCategory ⋙
      ((o.openOp c.i).extension.mapDerivedCategory ⋙
        (o.geometry c.g).push.rightDerivedFunctor) ⋙
      (b.realization Y.left).inverse.mapDerivedCategory).IsTriangulated
    infer_instance
  have : F.Additive := by
    change ((b.realization X.left).functor.mapDerivedCategory ⋙
      ((o.openOp c.i).extension.mapDerivedCategory ⋙
        (o.geometry c.g).push.rightDerivedFunctor) ⋙
      (b.realization Y.left).inverse.mapDerivedCategory).Additive
    infer_instance
  let τ := homComparison F H.obj K.obj eps.hom
  let P := (homologicalLocus τ).unop
  have hP : ∀ (s : Finset (Fin n)), s.Nonempty →
      ∀ M : SpTowerCalculus.C l E b q (s.inf U).toScheme,
        P ((SpTowerCalculus.openExtension l E b o q (s.inf U).ι).obj M.obj) := by
    intro s hs M n
    let V := s.inf U
    let := (q.abelian V.toScheme).hasDerived
    let := b.realizationAdditive V.toScheme
    let L := SpTowerCalculus.openExtension l E b o q V.ι
    let R := SpTowerCalculus.etalePullback l E b o q V.ι
    let G := SpTowerCalculus.F l E b o q (c.precomp V.ι)
    let adj : L ⊣ R :=
      (((SpTowerCalculus.realization l E b V.toScheme (q.abelian V.toScheme)).toAdjunction.comp
        (o.openOp V.ι).derivedAdjunction).comp
        (SpTowerCalculus.realization l E b X.left (q.abelian X.left)).symm.toAdjunction)
    let M' : SpTowerCalculus.C l E b q V.toScheme :=
      ⟨M.obj⟦-n⟧, tower_constructible_shift l E b q V.toScheme M (-n)⟩
    have hlocal := _local s hs M'
    have hglobal := open_hom_bijective L R adj F G
      (SpTowerCalculus.openComposition l E b o q V.ι c) H.obj K.obj eps.hom M'.obj hlocal
    have hτ : IsIso (τ.app (Opposite.op (L.obj M'.obj))) :=
      (ConcreteCategory.isIso_iff_bijective _).2 hglobal
    let _ : L.CommShift ℤ := by
      change ((b.realization V.toScheme).functor.mapDerivedCategory ⋙
        (o.openOp V.ι).extension.mapDerivedCategory ⋙
        (b.realization X.left).inverse.mapDerivedCategory).CommShift ℤ
      infer_instance
    let e := (L.commShiftIso (-n)).app M.obj
    exact (NatTrans.isIso_app_iff_of_iso τ e.op).mpr hτ
  have hglobal : ∀ M : SpTowerCalculus.C l E b q X.left,
      Function.Bijective (fun z : M.obj ⟶ H.obj ↦ F.map z ≫ eps.hom) := by
    intro M
    let : IsNoetherian X.left := isNoetherian_of_locallyOfFiniteType X.hom
    have hM := tower_finite_open_cover_generation l E b o q X.left n U _cover P hP M
    have hτ : IsIso (τ.app (Opposite.op M.obj)) :=
      (NatTrans.isIso_app_iff_of_iso τ
        ((shiftFunctorZero _ ℤ).app (Opposite.op M.obj))).mp (hM 0)
    exact ConcreteCategory.bijective_of_isIso (τ.app (Opposite.op M.obj))
  intro M
  let e₁ : (M ⟶ H) ≃ (M.obj ⟶ H.obj) :=
    (spConstructibleTorTowers l E X.left (q.abelian X.left)).fullyFaithfulι.homEquiv
  let e₂ : ((towerSupport l E b o q c hF).obj M ⟶ K) ≃
      (F.obj M.obj ⟶ K.obj) :=
    (spConstructibleTorTowers l E Y.left (q.abelian Y.left)).fullyFaithfulι.homEquiv
  exact e₂.symm.bijective.comp ((hglobal M).comp e₁.bijective)

end AlgebraicGeometry.ProEtale.SpTowerGluing
