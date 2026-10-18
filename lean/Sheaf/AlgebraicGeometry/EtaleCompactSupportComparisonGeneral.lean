/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F7
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMapProjection

import Sheaf.AlgebraicGeometry.EtaleCompactificationGraphIso
import Sheaf.AlgebraicGeometry.EtaleCompactificationAcyclic
import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory

/-!
# Compact supports along an etale map over an arbitrary scheme

Source: Stacks Project, More on Etale Cohomology, Tag 0GKM.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

/-- Compact support along a quasi-compact separated etale map is its exact sum extension,
without a Noetherian assumption on the schemes.

Source: Stacks Project, More on Etale Cohomology, Tag 0GKM, together with the
sum-extension description in Etale Cohomology, Tag 03S5.
(blueprint: lem-f7-etale-compact-support-comparison-general).

Proof: The constructed graph map is an isomorphism by
`isIso_etaleCompactificationGraphMap`. Hence the underived composite `j_!` followed by
`p_*` is exact, being isomorphic to exact etale sum extension. Independently,
`etaleCompactification_acyclic` says that every `j_!F` is `p_*`-acyclic. Proper direct
image sends acyclic complexes of such acyclic sheaves to acyclic complexes: at each
geometric point use its finite cohomological bound and then conservative inverse images.
On a K-injective complex the derived-composition unit is therefore invertible. This
exhibits `R(j_!)` followed by `Rp_*` as a right derived functor of the underived composite.
Uniqueness of right derived functors compares it with that composite's right derived
functor. Exactness identifies this with its degreewise descent, and identifies
`R(j_!)` with `D(j_!)`. Finally descend the graph isomorphism degreewise and compose the
isomorphisms. The bounds may vary with the geometric point; no global dimension,
compactness, or Noetherian assumption is needed. -/
theorem nonempty_iso_etale_compactSupport_general
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {U X : Scheme.{u}} (u : U ⟶ X) [Etale u] [IsSeparated u] [QuasiCompact u]
    (c : Compactification u) :
    Nonempty (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c ≅
      (etaleLowerShriek (ModuleCat.{u + 1} A) u inferInstance).mapDerivedCategory) := by
  let J := openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i
  let P := lowerStar (ModuleCat.{u + 1} A) c.g
  have := isIso_etaleCompactificationGraphMap A u c
  let e := (asIso (etaleCompactificationGraphMap A u c)).symm
  have hJP := etaleCompactification_acyclic A u c
  have : PreservesFiniteColimits (J ⋙ P) := preservesFiniteColimits_of_natIso e.symm
  choose d hd using exists_isZero_upperStar_rightDerived_lowerStar_of_isProper A
    isAddTorsion_of_finite c.g
  have hP : ∀ M : CochainComplex (Sheaf c.Z.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ,
      M.Acyclic → (∀ n, P.rightAcyclic (M.X n)) →
        ((P.mapHomologicalComplex _).obj M).Acyclic := by
    intro M hM hM'
    exact hM.map_of_rightAcyclic_of_forall_isZero _
      (fun y ↦ upperStar (ModuleCat.{u + 1} A) (X.algClosurePoint y))
      (isZero_of_forall_isZero_upperStar_algClosurePoint A) d hd hM'
  have hcomp : (J.rightDerivedFunctor ⋙ P.rightDerivedFunctor).IsRightDerivedFunctor
      (Functor.rightDerivedFunctorCompUnit J P)
      (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ)) := by
    refine (HomotopyCategory.KInjectives.localizerMorphism_derives
      ((J ⋙ P).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh)).isRightDerivedFunctor_of_isIso _ (fun K₁ ↦ ?_)
    obtain ⟨K, _, rfl⟩ := HomotopyCategory.KInjectives.mk_surjective K₁
    change IsIso ((Functor.rightDerivedFunctorCompUnit J P).app
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K))
    have hunit : IsIso (P.rightDerivedFunctorUnit.app
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
          ((J.mapHomologicalComplex (ComplexShape.up ℤ)).obj K))) :=
      P.isIso_rightDerivedFunctorUnit_app_of_rightAcyclic_of_map_acyclic hP _
        (fun n ↦ hJP (K.X n))
    have hunit' : IsIso (P.rightDerivedFunctorUnit.app
        ((J.mapHomotopyCategory (ComplexShape.up ℤ)).obj
          ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K))) := hunit
    dsimp [Functor.rightDerivedFunctorCompUnit]
    infer_instance
  let comp : (J ⋙ P).rightDerivedFunctor ≅
      J.rightDerivedFunctor ⋙ P.rightDerivedFunctor :=
    Functor.rightDerivedUnique (J ⋙ P).rightDerivedFunctor
      (J.rightDerivedFunctor ⋙ P.rightDerivedFunctor)
      (J ⋙ P).rightDerivedFunctorUnit (Functor.rightDerivedFunctorCompUnit J P)
      (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))
  exact ⟨Functor.isoWhiskerRight J.rightDerivedFunctorIsoMapDerivedCategory.symm _ ≪≫
    comp.symm ≪≫ (J ⋙ P).rightDerivedFunctorIsoMapDerivedCategory ≪≫
    Functor.mapDerivedCategoryNatIso e⟩

end AlgebraicGeometry.Etale
