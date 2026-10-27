/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NU
-/
module

public import Sheaf.Topology.ProfiniteCondensedRing
public import Sheaf.Paper.CoefficientHeartStratificationDefs
public import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Topology.KrullDimension
public import Mathlib.Topology.Sober
public import WeilConjectures.Mathlib.Topology.KrullDimension
import Sheaf.AlgebraicGeometry.ProEtaleAbelianClosedCounit
import all Sheaf.Paper.CondensedOpenClosedRecollement
import WeilConjectures.Mathlib.CategoryTheory.Functor.ReflectsIso.Exact

/-!
# The finite curve complement and its coefficient-module localization sequence

Source: blueprint main-20261015, sk-lem-coefficient-heart, final curve paragraph;
Stacks Tags 01J3, 0AAX and 09AH
(blueprint: lem-sfb-coefficient-heart-curve-complement).

The reduced induced closed complement is specified by its unique characterization:
a reduced closed subscheme with underlying image the complement of the given open.
All arrows are the actual adjunction counit and unit on internal coefficient modules.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- The reduced complement of an open containing every component's generic point in a
Noetherian scheme of dimension at most one is finite and consists of closed points.
For every commutative condensed ring and every internal coefficient module, the actual
open counit and closed unit form a short exact sequence, and the closed term restricts
to zero on the open. In particular, when the open restriction is lisse in the sense of
`IsLisseCoefficientModule`, this is the extension of the finite closed-support term
`i_* i^* F` by `u_! L`, with `L = u^* F`.

Source: blueprint main-20261015, sk-lem-coefficient-heart, final curve paragraph;
Stacks Tags 01J3, 0AAX and 09AH
(blueprint: lem-sfb-coefficient-heart-curve-complement).

Proof:
1. Every point in the closed complement specializes from the generic point of an
irreducible component, and that generic point lies in U. The closed-subspace dimension
inequality therefore bounds the dimension of the complement by zero. The closed
zero-dimensional Noetherian-subset theorem makes it finite with closed singletons.
The closed immersion identifies Z with its image, transferring dimension and finiteness.
2. Use the canonical coefficient isomorphism to identify the underlying sheaf of
module pullback with abelian pullback. Disjointness makes open restriction of a closed
direct image zero. Reuse the existing
module-support lemmas from `CondensedOpenClosedRecollement`: they lift the abelian
closed counit and supported unit across the scalar equivalence, and show the open
unit invertible by full faithfulness of extension by zero and scalar restriction.
3. These units and counits imply that the open and closed restrictions jointly detect
zero objects. Exactness of the restrictions then makes them jointly detect isomorphisms,
by applying them to kernels and cokernels. The actual open counit and closed unit
compose to zero by adjunction and disjointness. On each piece, one of the two arrows is
invertible by the corresponding triangle identity, and the other has zero source or
target. Thus both restricted sequences are short exact. Joint reflection of short
exactness gives the asserted sequence on X, including every empty or zero case. -/
theorem coefficientHeart_curve_complement
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (X : Scheme.{u}) [IsLocallyNoetherian X] [CompactSpace X]
    (hdim : topologicalKrullDim X ≤ 1) (U : X.Opens)
    (hU : ∀ C ∈ irreducibleComponents X, ∀ η : X, IsGenericPoint η C → η ∈ U)
    (Z : Scheme.{u}) (i : Z ⟶ X) [IsClosedImmersion i] [IsReduced Z]
    (hi : Set.range i = (U : Set X)ᶜ)
    (F : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    topologicalKrullDim Z ≤ 0 ∧
    Finite Z ∧
    (∀ z : Z, IsClosed ({i z} : Set X)) ∧
    Mono ((CondensedRing.openImmersionLowerShriekUpperStarAdjunction Λ U.ι).counit.app F) ∧
    Epi ((CondensedRing.upperStarLowerStarAdjunction Λ i).unit.app F) ∧
    (ComposableArrows.mk₂
      ((CondensedRing.openImmersionLowerShriekUpperStarAdjunction Λ U.ι).counit.app F)
      ((CondensedRing.upperStarLowerStarAdjunction Λ i).unit.app F)).Exact ∧
    IsZero ((CondensedRing.upperStar Λ U.ι).obj
      ((CondensedRing.lowerStar Λ i).obj ((CondensedRing.upperStar Λ i).obj F))) := by
  classical
  have : IsNoetherian X := ⟨⟩
  have hT : topologicalKrullDim ((U : Set X)ᶜ : Set X) ≤ 0 := by
    have hg : ∀ w ∈ (U : Set X)ᶜ, ∃ z ∈ (Set.univ : Set X),
        z ⤳ w ∧ z ∉ (U : Set X)ᶜ := by
      intro w _
      let C := irreducibleComponent w
      have hC : C ∈ irreducibleComponents X := irreducibleComponent_mem_irreducibleComponents w
      obtain ⟨η, hη⟩ := QuasiSober.sober hC.1 (isClosed_of_mem_irreducibleComponents C hC)
      exact ⟨η, Set.mem_univ _, hη.specializes mem_irreducibleComponent,
        not_not.mpr (hU C hC η hη)⟩
    have hX : topologicalKrullDim (Set.univ : Set X) < (1 : ℕ) + 1 := by
      rw [IsHomeomorph.topologicalKrullDim_eq _ (Homeomorph.Set.univ X).isHomeomorph]
      exact hdim.trans_lt (by decide)
    have hd := topologicalKrullDim_lt_of_forall_exists_specializes
      isClosed_univ U.isOpen.isClosed_compl (Set.subset_univ _) hg hX
    exact (ENat.WithBot.lt_add_one_iff (m := 0)).mp (by simpa using hd)
  have hfin := U.isOpen.isClosed_compl
    |>.finite_and_isClosed_singleton_of_topologicalKrullDim_le_zero hT
  have hdZ : topologicalKrullDim Z ≤ 0 := by
    rw [i.isClosedEmbedding.isEmbedding.topologicalKrullDim_eq_range, hi]
    exact hT
  have : Finite ((U : Set X)ᶜ : Set X) := hfin.1
  have hfZ : Finite Z := Finite.of_injective (fun z : Z ↦
    (⟨i z, hi ▸ Set.mem_range_self z⟩ : ((U : Set X)ᶜ : Set X)))
      (fun _ _ h ↦ i.isClosedEmbedding.injective (congrArg Subtype.val h))
  have hij : Set.range U.ι = (Set.range i)ᶜ := by simp [hi]
  have hz := CondensedRing.openRestrictionPushforwardZero Λ i U.ι hij
  have hc := CondensedRing.moduleCounitOfAbelian Λ i (abelian_closed_counit i)
  have hu := CondensedRing.openUnitIsIso Λ U.ι
  let a := CondensedRing.openImmersionLowerShriekUpperStarAdjunction Λ U.ι
  let b := CondensedRing.upperStarLowerStarAdjunction Λ i
  have hjoint (M) (hiM : IsZero ((CondensedRing.upperStar Λ i).obj M))
      (hjM : IsZero ((CondensedRing.upperStar Λ U.ι).obj M)) : IsZero M := by
    have hab : IsZero ((upperStar Ab.{u + 1} U.ι).obj M.X) :=
      ((Mod.forget _).map_isZero hjM).of_iso
        ((profinitePointModuleForgetPullbackIso Λ U.ι).app M).symm
    have hunit := CondensedRing.moduleUnitOfAbelian Λ i M
      ((abelian_closed_support i U.ι hij).2 M.X hab)
    exact ((CondensedRing.lowerStar Λ i).map_isZero hiM).of_iso
      (asIso (b.unit.app M))
  have hdetect : JointlyReflectIsomorphisms
      (pairFunctor (CondensedRing.upperStar Λ U.ι) (CondensedRing.upperStar Λ i)) := by
    refine jointlyReflectIsomorphisms_pairFunctor _ _ ?_
    intro M N φ hj hiφ
    have := hj
    have := hiφ
    have hker : IsZero (kernel φ) := hjoint _
      ((isZero_kernel_of_mono _).of_iso (PreservesKernel.iso _ φ))
      ((isZero_kernel_of_mono _).of_iso (PreservesKernel.iso _ φ))
    have hcoker : IsZero (cokernel φ) := hjoint _
      ((isZero_cokernel_of_epi _).of_iso (PreservesCokernel.iso _ φ))
      ((isZero_cokernel_of_epi _).of_iso (PreservesCokernel.iso _ φ))
    have : Mono φ := Preadditive.mono_of_isZero_kernel φ hker
    have : Epi φ := Preadditive.epi_of_isZero_cokernel φ hcoker
    exact isIso_of_mono_of_epi φ
  have hzi (N) : IsZero ((CondensedRing.upperStar Λ i).obj
      ((CondensedRing.openImmersionLowerShriek Λ U.ι).obj N)) := by
    apply (IsZero.iff_id_eq_zero _).2
    apply (b.homEquiv _ _).injective
    apply (a.homEquiv _ _).injective
    exact (hz _).eq_of_tgt _ _
  have hzero : a.counit.app F ≫ b.unit.app F = 0 := by
    apply (a.homEquiv _ _).injective
    exact (hz _).eq_of_tgt _ _
  let Q := ShortComplex.mk (a.counit.app F) (b.unit.app F) hzero
  have hQ : Q.ShortExact := by
    rw [hdetect.shortExact_iff]
    rintro (_ | _)
    · have hgi : IsIso ((CondensedRing.upperStar Λ i).map (b.unit.app F)) := by
        have h := b.left_triangle_components F
        rw [← IsIso.inv_eq_of_inv_hom_id h]
        infer_instance
      have : IsIso ((Q.map (CondensedRing.upperStar Λ i)).g) := hgi
      have hfi : (Q.map (CondensedRing.upperStar Λ i)).f = 0 := (hzi _).eq_of_src _ _
      exact
        { exact := (ShortComplex.exact_iff_mono _ hfi).2 (@IsIso.mono_of_iso _ _ _ _ _ hgi)
          mono_f := ⟨fun _ _ _ ↦ (hzi _).eq_of_tgt _ _⟩
          epi_g := @IsIso.epi_of_iso _ _ _ _ _ hgi }
    · have hfj : IsIso ((CondensedRing.upperStar Λ U.ι).map (a.counit.app F)) := by
        have h := a.right_triangle_components (Y := F)
        rw [← IsIso.inv_eq_of_hom_inv_id h]
        infer_instance
      have : IsIso ((Q.map (CondensedRing.upperStar Λ U.ι)).f) := hfj
      have hgj : (Q.map (CondensedRing.upperStar Λ U.ι)).g = 0 := (hz _).eq_of_tgt _ _
      exact
        { exact := (ShortComplex.exact_iff_epi _ hgj).2 (@IsIso.epi_of_iso _ _ _ _ _ hfj)
          mono_f := @IsIso.mono_of_iso _ _ _ _ _ hfj
          epi_g := ⟨fun _ _ _ ↦ (hz _).eq_of_src _ _⟩ }
  exact ⟨hdZ, hfZ, fun z ↦ hfin.2 (i z) (hi ▸ Set.mem_range_self z),
    hQ.mono_f, hQ.epi_g, hQ.exact.exact_toComposableArrows, hz _⟩

end AlgebraicGeometry.ProEtale
