/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import WeilConjectures.Topology.ProfiniteCondensedRing
public import WeilConjectures.AlgebraicGeometry.CondensedModuleDerivedPushpull
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek
import Mathlib.AlgebraicGeometry.PullbackCarrier
import WeilConjectures.CategoryTheory.ProEtaleCoefficients.LeftDerivedExactComparison
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.OpenClosed

/-!
# The proper square of an open subscheme and its closed complement

The closed complement is arbitrary with the prescribed point set; no reducedness is assumed.
Vanishing takes place in the ordinary unbounded derived category of internal modules.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- Pulling back a complementary open and closed pair along a proper map gives the
complementary pair on the source, with separated finite-type schemes and vanishing mixed
restriction of open extension by zero on every unbounded coefficient-module complex. -/
theorem proper_open_complement_square
    (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    {W Y Ybar Z : Over (Spec (.of k))}
    [IsSeparated W.hom] [LocallyOfFiniteType W.hom] [QuasiCompact W.hom]
    [IsSeparated Y.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
    [IsSeparated Ybar.hom] [LocallyOfFiniteType Ybar.hom] [QuasiCompact Ybar.hom]
    (r : W ⟶ Ybar) [IsProper r.left]
    (i : Y ⟶ Ybar) [IsOpenImmersion i.left] [QuasiCompact i.left]
    (c : Z ⟶ Ybar) [IsClosedImmersion c.left]
    (hcomp : Set.range c.left.base = (Set.range i.left.base)ᶜ) :
    (IsSeparated (pullback.fst r.left i.left ≫ W.hom) ∧
      LocallyOfFiniteType (pullback.fst r.left i.left ≫ W.hom) ∧
      QuasiCompact (pullback.fst r.left i.left ≫ W.hom)) ∧
    (IsSeparated Z.hom ∧ LocallyOfFiniteType Z.hom ∧ QuasiCompact Z.hom) ∧
    (IsSeparated (pullback.fst r.left c.left ≫ W.hom) ∧
      LocallyOfFiniteType (pullback.fst r.left c.left ≫ W.hom) ∧
      QuasiCompact (pullback.fst r.left c.left ≫ W.hom)) ∧
    IsOpenImmersion (pullback.fst r.left i.left) ∧
    QuasiCompact (pullback.fst r.left i.left) ∧
    IsClosedImmersion (pullback.fst r.left c.left) ∧
    IsProper (pullback.snd r.left c.left) ∧
    Set.range (pullback.fst r.left c.left).base =
      (Set.range (pullback.fst r.left i.left).base)ᶜ ∧
    ∀ (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
      (B : DerivedCategory
        (Mod (Sheaf (Scheme.ProEt.topology (pullback r.left i.left)) Ab.{u + 1})
          (condensedRingObj Λ.X (pullback r.left i.left)))),
      IsZero ((moduleObjectDerivedPullback Λ.X (pullback.fst r.left c.left)).obj
        (((openImmersionLowerShriek Λ.X (pullback.fst r.left i.left)).mapDerivedCategory).obj
          B)) := by
  have hZ : c.left ≫ Ybar.hom = Z.hom := Over.w c
  have hZsep : IsSeparated Z.hom := hZ ▸ inferInstance
  have hZft : LocallyOfFiniteType Z.hom := hZ ▸ inferInstance
  have hZqc : QuasiCompact Z.hom := hZ ▸ inferInstance
  have hcomp' : Set.range (pullback.fst r.left c.left).base =
      (Set.range (pullback.fst r.left i.left).base)ᶜ := by
    rw [Scheme.Pullback.range_fst, Scheme.Pullback.range_fst]
    rw [hcomp]
    rfl
  refine ⟨⟨inferInstance, inferInstance, inferInstance⟩, ⟨hZsep, hZft, hZqc⟩,
    ⟨inferInstance, inferInstance, inferInstance⟩, inferInstance, inferInstance,
    inferInstance, inferInstance, hcomp', ?_⟩
  intro Λ _ B
  have hdisj : Disjoint (Set.range (pullback.fst r.left i.left).base)
      (Set.range (pullback.fst r.left c.left).base) := by
    rw [hcomp']
    exact disjoint_compl_right
  let F := upperStar Λ.X (pullback.fst r.left c.left)
  let J := openImmersionLowerShriek Λ.X (pullback.fst r.left i.left)
  have hz : IsZero (F.mapDerivedCategory.obj (J.mapDerivedCategory.obj B)) := by
    apply F.isZero_mapDerivedCategory_obj
    intro n
    exact (isZero_upperStar_obj_openImmersionLowerShriek_of_disjoint Λ.X
      (pullback.fst r.left i.left) (pullback.fst r.left c.left) hdisj
      ((DerivedCategory.homologyFunctor _ n).obj B)).of_iso
      (F.mapIso ((J.mapDerivedCategoryHomologyFunctorIso n).symm.app B))
  exact hz.of_iso ((F.leftDerivedExactComparison F.leftDerivedFunctor
    F.leftDerivedFunctorCounit).app _)

end AlgebraicGeometry.ProEtale.CondensedRing
