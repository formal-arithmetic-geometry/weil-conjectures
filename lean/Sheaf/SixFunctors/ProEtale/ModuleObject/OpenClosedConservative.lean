/-
Copyright (c) 2026 Weil conjectures project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weil conjectures project
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
import all Sheaf.Paper.CondensedOpenClosedRecollement
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-!
# Open–closed conservativity for derived module objects

Source: Stacks Project, Tags 09AA and 09AH; the exact inverse images detect
kernels and cokernels, and this passes to derived categories on homology.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

set_option backward.isDefEq.respectTransparency false in
private theorem moduleJointZero
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X U Z : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] (j : U ⟶ X)
    [IsOpenImmersion j] [QuasiCompact j]
    (hij : Set.range j = (Set.range i)ᶜ)
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hi : IsZero ((upperStar Λ i).obj M))
    (hj : IsZero ((upperStar Λ j).obj M)) : IsZero M := by
  have hAb := (ProEtale.abelian_closed_support i j hij).2 M.X
    (((Mod.forget _).map_isZero hj).of_iso ((profinitePointModuleForgetPullbackIso Λ j).app M).symm)
  have := moduleUnitOfAbelian Λ i M hAb
  exact ((lowerStar Λ i).map_isZero hi).of_iso
    (asIso ((upperStarLowerStarAdjunction Λ i).unit.app M))

private theorem moduleJointIso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X U Z : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] (j : U ⟶ X)
    [IsOpenImmersion j] [QuasiCompact j]
    (hij : Set.range j = (Set.range i)ᶜ) :
    JointlyReflectIsomorphisms (pairFunctor (upperStar Λ j) (upperStar Λ i)) := by
  refine jointlyReflectIsomorphisms_pairFunctor _ _ fun M N φ hj hi ↦ ?_
  have hker : ∀ {Y : Scheme.{u}} (g : Y ⟶ X) [IsIso ((upperStar Λ g).map φ)],
      IsZero ((upperStar Λ g).obj (kernel φ)) := fun g _ ↦
    (isZero_kernel_of_mono ((upperStar Λ g).map φ)).of_iso (PreservesKernel.iso _ φ)
  have hcoker : ∀ {Y : Scheme.{u}} (g : Y ⟶ X) [IsIso ((upperStar Λ g).map φ)],
      IsZero ((upperStar Λ g).obj (cokernel φ)) := fun g _ ↦
    (isZero_cokernel_of_epi ((upperStar Λ g).map φ)).of_iso (PreservesCokernel.iso _ φ)
  have : Mono φ := Preadditive.mono_of_isZero_kernel _
    (moduleJointZero Λ i j hij _ (hker i) (hker j))
  have : Epi φ := Preadditive.epi_of_isZero_cokernel _
    (moduleJointZero Λ i j hij _ (hcoker i) (hcoker j))
  exact isIso_of_mono_of_epi φ

/-- Exact open and closed inverse images jointly detect derived isomorphisms.
Source: Stacks Project, Tags 09AA and 09AH.
(blueprint: lem-sfb-module-open-closed-conservative)

Proof: a module whose two restrictions vanish is supported on the closed part;
the closed adjunction unit is invertible there, as can be checked on underlying
abelian sheaves, and its target is zero. Apply this joint zero detection to the
kernel and cokernel of a morphism to obtain joint detection of isomorphisms in
the abelian categories. Exact inverse image commutes with homology, so the same
criterion detects isomorphisms in the unbounded derived categories. Finally the
total left derived inverse images are the exact levelwise inverse images. This
also covers the empty open and the identity open, without boundedness assumptions. -/
theorem isIso_of_isIso_module_derived_open_closed
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X U Z : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] (j : U ⟶ X)
    [IsOpenImmersion j] [QuasiCompact j]
    (hij : Set.range j = (Set.range i)ᶜ)
    {K K' : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))}
    (φ : K ⟶ K')
    (hj : IsIso ((upperStar Λ j).leftDerivedFunctor.map φ))
    (hi : IsIso ((upperStar Λ i).leftDerivedFunctor.map φ)) : IsIso φ := by
  have hd := Functor.jointlyReflectIsomorphisms_pairFunctor_mapDerivedCategory
    (upperStar Λ j) (upperStar Λ i) (moduleJointIso Λ i j hij)
  exact (hd.pairFunctor_of_iso
    (leftDerivedUpperStarIsoMapDerivedCategory Λ j).symm
    (leftDerivedUpperStarIsoMapDerivedCategory Λ i).symm).isIso_of_pairFunctor φ hj hi

end AlgebraicGeometry.ProEtale.CondensedRing
