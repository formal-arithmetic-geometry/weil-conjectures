/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsCanonicalAdjunctionSupplement
import all WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsSupplement
import WeilConjectures.AlgebraicGeometry.ProEtale.Ringed.ProEtaleRingedOpenComparison
import WeilConjectures.Algebra.Homology.Scalar.ScalarExtensionRingIsoSupplement
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.LocalProperties

/-! # Open covers detect derived isomorphisms with inverse-image coefficients

Source: Stacks Project, Tags 00XZ and 0EYZ.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme.RingedRestrictionExchange

attribute [local instance 30000]
  SheafOfModules.wEqualsLocallyBijective_coefficientUniverse
  proEtaleRingModules_hasDerivedCategory
attribute [local irreducible] proEtaleRingModulePullback Functor.mapDerivedCategory

end AlgebraicGeometry.Scheme.RingedRestrictionExchange

namespace AlgebraicGeometry.Scheme.RingedRestrictionExchange

private theorem slice_restriction_isIso {S Z : Scheme.{u}} (j : S ⟶ Z)
    [IsOpenImmersion j] (R : Sheaf (ProEt.topology Z) CommRingCat.{u + 1})
    (R' : Sheaf (ProEt.topology S) CommRingCat.{u + 1})
    (c : (proEtaleSheafInverseImage j CommRingCat.{u + 1}).obj R ≅ R')
    {M N : proEtaleRingModules Z R} (a : M ⟶ N)
    [IsIso ((proEtaleRingModulePullback j R R' c).map a)] :
    IsIso ((SheafOfModules.overFunctor.{u + 1}
      ((sheafCompose (ProEt.topology Z)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R) (ProEt.mk j)).map a) := by
  let U : Z.ProEt := ProEt.mk j
  have : IsOpenImmersion U.hom := ‹IsOpenImmersion j›
  obtain ⟨q, ⟨hq⟩⟩ := proEtale_ringed_open_comparison U R
  let e := proEtaleScalarEquivalence S ((sheafCompose (ProEt.topology S)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).mapIso c)
  obtain ⟨theta, _, _, htheta⟩ :=
    SheafOfModules.exists_scalarExtensionRingIso.{u + 1, u, u + 1, u + 1} c
  let p : proEtaleRingModulePullback j R R' c ≅
      proEtaleModuleInverseImage j R ⋙ e.inverse := by
    unfold proEtaleRingModulePullback
    exact NatIso.ofComponents (fun M ↦ theta ((proEtaleModuleInverseImage j R).obj M))
      (fun f ↦ htheta _ _ ((proEtaleModuleInverseImage j R).map f))
  have hi : IsIso ((proEtaleModuleInverseImage j R ⋙ e.inverse).map a) :=
    (NatIso.isIso_map_iff p a).mp inferInstance
  have : IsIso (e.inverse.map ((proEtaleModuleInverseImage j R).map a)) := hi
  have : IsIso ((proEtaleModuleInverseImage j R).map a) :=
    isIso_of_reflects_iso _ e.inverse
  have : IsIso ((proEtaleModuleInverseImage U.hom R).map a) :=
    ‹IsIso ((proEtaleModuleInverseImage j R).map a)›
  have hi : IsIso (q.functor.map ((proEtaleModuleInverseImage U.hom R).map a)) :=
    inferInstance
  exact (NatIso.isIso_map_iff hq a).mp hi

private theorem opens_coverTop {Z : Scheme.{u}} {ι : Type (u + 1)}
    (V : ι → Scheme.{u}) (j : ∀ i, V i ⟶ Z) [∀ i, IsOpenImmersion (j i)]
    (cover : ∀ z : Z, ∃ (i : ι) (v : V i), (j i).base v = z) :
    (ProEt.topology Z).CoversTop (fun i ↦ ProEt.mk (j i)) := by
  classical
  choose index point hpoint using cover
  intro Q
  let k (z : Z) := pullback.fst Q.hom (j (index z))
  apply ProEt.mem_topology_of_openImmersion _ k
  · intro x
    refine ⟨Q.hom x, ?_⟩
    rw [Scheme.Pullback.range_fst]
    exact ⟨point (Q.hom x), hpoint (Q.hom x)⟩
  · intro z
    refine ⟨index z, ⟨?_⟩⟩
    exact MorphismProperty.Over.homMk (pullback.snd Q.hom (j (index z)))
      (pullback.condition (f := Q.hom) (g := j (index z))).symm

end AlgebraicGeometry.Scheme.RingedRestrictionExchange
