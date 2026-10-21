/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R7
-/
module

public import Sheaf.SixFunctors.ScalarSixPullback
public import Sheaf.Paper.CoefficientHeartStratificationDefs
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
import Sheaf.SixFunctors.ScalarSixHeartLatticeExtension
import Sheaf.AlgebraicGeometry.ProEtaleModuleConstructiblePullback

/-! # Constructibility of the normalized integral extension

The statement transports the integral-generator calculation to the published
normalized locally closed extension on internal module objects.
Source: blueprint main-20261015, rational proper base change, paragraph (3).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

private theorem heartZeroConstructible {X : Scheme.{u}}
    (R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj R]
    (N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R) (hN : IsZero N) :
    IsConstructibleModuleObject R N := by
  let T : Scheme.Stratification X :=
    { n := 1
      stratum := fun _ ↦ Set.univ
      isLocallyClosed_stratum := fun _ ↦ isOpen_univ.isLocallyClosed
      isConstructible_stratum := fun _ ↦ Topology.IsConstructible.univ
      iUnion_stratum_eq_univ := Set.iUnion_const _
      pairwise_disjoint_stratum := fun i j hij ↦ (hij (Subsingleton.elim i j)).elim
      domain := fun _ ↦ X
      immersion := fun _ ↦ 𝟙 X
      range_immersion := fun _ ↦ Set.range_id' }
  refine ⟨T, fun i ↦ ?_⟩
  refine ⟨.singleton (𝟙 X) (Precoverage.mem_coverings_of_isIso _), fun j ↦ ?_⟩
  refine ⟨0, 0, 𝟙 _, ⟨?_⟩⟩
  exact (((ProEtale.upperStar Ab.{u + 1} _).mapMod _).map_isZero
    (((ProEtale.upperStar Ab.{u + 1} _).mapMod R).map_isZero hN)).iso
    (isZero_cokernel_of_epi (𝟙 _))

/-- Extending a lisse integral lattice by the normalized exact locally closed
extension gives a bounded constructible complex.

Source: blueprint main-20261015, proper-base-change rational proof, paragraph (3),
common-field argument step 4; integral generators, clause (3).
(blueprint: lem-sfb-normalized-integral-extension-constructible).

Proof: Apply normalized_integral_heart_extension_constructible to the actual
module extension transported by the internal/sectionwise equivalence. Exactness
of this equivalence, of H.extension and of the inverse equivalence gives three
mapDerivedCategorySingleFunctor isomorphisms. Compose them to identify the object
in the conclusion with the degree-zero complex of that constructible module.
Its degree-zero cohomology is the given constructible module, while every other
cohomology module is zero. A zero module has a rank-zero finite presentation on
the identity cover and one-stratum stratification. Hence the single complex is
bounded constructible with bounds [0,0]. Transport boundedness and constructible
cohomology along the constructed isomorphism.
-/
theorem normalized_integral_extension_constructible
    (ell p : ℕ) [Fact ell.Prime] [Fact p.Prime]
    (k : Type u) [Field k] [CharP k p] (hne : ell ≠ p)
    (H : LocallyClosedExtensionData.{u}) (hH : H.Coherent)
    (G : ScalarSixGeometry.{u})
    (E : PadicAlgCl.FiniteIntermediateField ell)
    (W Z : Over (Spec (.of k)))
    [LocallyOfFiniteType W.hom] [QuasiCompact W.hom] [IsSeparated W.hom]
    [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom]
    (a : Z ⟶ W) [IsImmersion a.left]
    (M : ModuleRingedComparison.internalModules
      (Profinite.padicIntegersRingObj ell E.1) Z.left)
    (hM : IsLisseCoefficientModule (Profinite.padicIntegersRingObj ell E.1) M) :
    boundedConstructible
      (condensedRingObj (Profinite.padicIntegersRingObj ell E.1) W.left)
      ((scalarSixExtension H G (⟨Profinite.padicIntegersRingObj ell E.1⟩ : ScalarSixRing) a).obj
        ((DerivedCategory.singleFunctor _ 0).obj M)) := by
  let A : ScalarSixRing.{u} := ⟨Profinite.padicIntegersRingObj ell E.1⟩
  let F := (ModuleRingedComparison.equivalence A.X Z.left).functor
  let J := H.extension (scalarSixImmersion G A a)
  let R := (ModuleRingedComparison.equivalence A.X W.left).inverse
  let N := R.obj (J.obj (F.obj M))
  let S := DerivedCategory.singleFunctor
    (ModuleRingedComparison.internalModules A.X W.left) 0
  let e : (scalarSixExtension H G A a).obj
      ((DerivedCategory.singleFunctor _ 0).obj M) ≅ S.obj N :=
    R.mapDerivedCategory.mapIso
        (J.mapDerivedCategory.mapIso ((F.mapDerivedCategorySingleFunctor 0).app M)) ≪≫
      R.mapDerivedCategory.mapIso ((J.mapDerivedCategorySingleFunctor 0).app (F.obj M)) ≪≫
      (R.mapDerivedCategorySingleFunctor 0).app (J.obj (F.obj M))
  have hN : IsConstructibleModuleObject (condensedRingObj A.X W.left) N :=
    normalized_integral_heart_extension_constructible ell p k hne H hH G E W Z a M hM
  have hsingle : boundedConstructible (condensedRingObj A.X W.left) (S.obj N) := by
    constructor
    · exact ⟨⟨0, inferInstance⟩, ⟨0, inferInstance⟩⟩
    · intro n
      by_cases hn : n = 0
      · subst n
        exact constructible_of_iso
          ((DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).app N).symm hN
      · apply heartZeroConstructible
        rcases lt_or_gt_of_ne hn with hn | hn
        · exact DerivedCategory.isZero_of_isGE _ 0 n hn
        · exact DerivedCategory.isZero_of_isLE _ 0 n hn
  constructor
  · exact (DerivedCategory.TStructure.t.bounded).prop_of_iso e.symm hsingle.1
  · intro n
    exact constructible_of_iso ((DerivedCategory.homologyFunctor _ n).mapIso e).symm
      (hsingle.2 n)

end AlgebraicGeometry.ProEtale.CondensedRing
