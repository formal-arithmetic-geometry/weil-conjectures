/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.AlgebraicGeometry.Sites.SupportDimension
import all WeilConjectures.AlgebraicGeometry.Sites.SupportDimension
public import WeilConjectures.AlgebraicGeometry.Sites.TorsionCohomologicalDimension

import WeilConjectures.AlgebraicGeometry.Sites.CohomologyFilteredColimit
import WeilConjectures.AlgebraicGeometry.Sites.CohomologyClopen
import WeilConjectures.SixFunctors.OpenClosed.Supported
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.FullyFaithful
import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme

/-! # Cohomology of torsion sheaves with bounded-dimensional support

Source: blueprint thm-sc-affine-torsion-cd, supported-union argument.
(blueprint: lem-sc-supported-torsion-cohomology-bound)
-/

@[expose] public section
set_option autoImplicit false

universe u
open CategoryTheory Limits
namespace AlgebraicGeometry.Scheme

private theorem isZero_upperStar_supportedIn
    {B : Scheme.{u}} (F : Sheaf B.smallEtaleTopology AddCommGrpCat.{u + 1})
    (U : B.Opens) :
    IsZero ((Etale.upperStar AddCommGrpCat.{u + 1} U.ι).obj (Etale.supportedIn F U)) := by
  let J := Etale.upperStar AddCommGrpCat.{u + 1} U.ι
  let η := (Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} U.ι).unit.app F
  have : IsIso (J.map η) := inferInstance
  exact (isZero_kernel_of_mono (J.map η)).of_iso (asIso (kernelComparison η J))

private theorem supportedIn_factor
    {B : Scheme.{u}} (F : Sheaf B.smallEtaleTopology AddCommGrpCat.{u + 1})
    (U V : B.Opens) (hVU : V ≤ U) :
    ∃ f : Etale.supportedIn F U ⟶ Etale.supportedIn F V,
      f ≫ Etale.supportedInι F V = Etale.supportedInι F U := by
  let J := Etale.upperStar AddCommGrpCat.{u + 1} V.ι
  let η := (Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} V.ι).unit
  have hsrc : IsZero (J.obj (Etale.supportedIn F U)) := by
    have hzero := (Etale.upperStar AddCommGrpCat.{u + 1} (B.homOfLE hVU)).map_isZero
      (isZero_upperStar_supportedIn F U)
    exact hzero.of_iso ((Etale.upperStarComp AddCommGrpCat.{u + 1}
      (B.homOfLE hVU) U.ι V.ι (by simp)).app (Etale.supportedIn F U))
  have hzero : Etale.supportedInι F U ≫ η.app F = 0 := by
    change (𝟭 _).map (Etale.supportedInι F U) ≫ η.app F = 0
    rw [η.naturality]
    change η.app _ ≫ (Etale.lowerStar AddCommGrpCat.{u + 1} V.ι).map
      (J.map (Etale.supportedInι F U)) = 0
    have hz : J.map (Etale.supportedInι F U) = 0 := hsrc.eq_of_src _ _
    simp only [hz, Functor.map_zero, comp_zero]
  exact ⟨kernel.lift _ (Etale.supportedInι F U) hzero, kernel.lift_ι _ _ _⟩

private theorem subsingleton_H_supportedIn
    {B : Scheme.{u}} [IsAffine B] (a : ℕ)
    (hclosed : ∀ (Z : Scheme.{u}) [IsAffine Z] (i : Z ⟶ B) [IsClosedImmersion i],
      topologicalKrullDim Z ≤ (a : WithBot ℕ∞) →
        Z.HasTorsionCohomologicalDimensionLE a)
    (F : Sheaf B.smallEtaleTopology AddCommGrpCat.{u + 1}) (N : ℕ)
    (hN : 0 < N) (hF : N • 𝟙 F = 0) (U : B.Opens)
    (hU : topologicalKrullDim ((U : Set B)ᶜ : Set B) ≤ (a : WithBot ℕ∞))
    (q : ℕ) (hq : a < q) : Subsingleton (Sheaf.H (Etale.supportedIn F U) q) := by
  let A := Etale.supportedIn F U
  let Z := (IdealSheafData.vanishingIdeal
    ⟨(U : Set B)ᶜ, U.isOpen.isClosed_compl⟩).subscheme
  let i : Z ⟶ B := U.closedComplement
  have : IsAffine Z := isAffine_of_isAffineHom i
  have hdim : topologicalKrullDim Z ≤ (a : WithBot ℕ∞) := by
    have e := i.isClosedEmbedding.isEmbedding.toHomeomorph.trans
      (Homeomorph.setCongr U.range_closedComplement)
    exact (IsHomeomorph.topologicalKrullDim_eq _ e.isHomeomorph).trans_le hU
  obtain ⟨G, ⟨e⟩⟩ := Etale.mem_essImage_lowerStar_of_isZero_upperStar i
    (by rw [U.range_closedComplement, Opens.range_ι]) (isZero_upperStar_supportedIn F U)
  have : Mono (Etale.supportedInι F U) := inferInstanceAs (Mono (kernel.ι _))
  have hA : N • 𝟙 A = 0 := by
    rw [← cancel_mono (Etale.supportedInι F U), zero_comp,
      Preadditive.nsmul_comp, Category.id_comp,
      ← Category.comp_id (Etale.supportedInι F U), ← Preadditive.comp_nsmul, hF, comp_zero]
  let eG := (asIso
    ((Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} i).counit.app G)).symm ≪≫
      (Etale.upperStar AddCommGrpCat.{u + 1} i).mapIso e
  have hG : N • 𝟙 G = 0 := by
    rw [← cancel_mono eG.hom, zero_comp, Preadditive.nsmul_comp, Category.id_comp,
      ← Category.comp_id eG.hom, ← Preadditive.comp_nsmul]
    have h : N • 𝟙 ((Etale.upperStar AddCommGrpCat.{u + 1} i).obj A) = 0 := by
      let P := Etale.upperStar AddCommGrpCat.{u + 1} i
      calc
        N • 𝟙 (P.obj A) = P.map (N • 𝟙 A) := by rw [Functor.map_nsmul, P.map_id]
        _ = P.map 0 := congrArg P.map hA
        _ = 0 := P.map_zero _ _
    rw [h, comp_zero]
  have hcoh : Subsingleton (Sheaf.H G q) :=
    hclosed Z i hdim G (isTorsion_of_nsmul_id_eq_zero hN hG) q hq
  have : Subsingleton (Sheaf.H ((𝟭 _).obj G) q) := by
    change Subsingleton (Sheaf.H G q)
    exact hcoh
  have hpushed : Subsingleton (Sheaf.H
      ((Etale.lowerStar AddCommGrpCat.{u + 1} i).obj G) q) :=
    (Etale.bijective_edgeMap_of_isFinite i G q).injective.subsingleton
  have : Subsingleton ((Sheaf.functorH B.smallEtaleTopology q).obj
      ((Etale.lowerStar AddCommGrpCat.{u + 1} i).obj G)) := hpushed
  exact ((Sheaf.functorH B.smallEtaleTopology q).mapIso e.symm).addCommGroupIsoToAddEquiv
    |>.injective.subsingleton

/-- Bounded torsion sheaves vanishing above residue transcendence degree a have no
cohomology above a, provided closed affine subschemes of dimension at most a satisfy
that torsion cohomological bound.

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-prop-sf-cbc/
thm-sc-affine-torsion-cd.proof.md, "Cohomology of the resulting sheaves on B".
(blueprint: lem-sc-supported-torsion-cohomology-bound)

Proof: For each open U whose closed complement has dimension at most a, take the kernel
of F -> j_*j^*F. Exact restriction kills this kernel, so closed-support equivalence writes
it as the finite pushforward of a sheaf on that closed affine complement. Its given positive
annihilator is inherited through the kernel, restriction, and the closed-immersion counit.
The assumed bound and finite-pushforward cohomology comparison kill its cohomology above a.
Intersections of the opens correspond to finite unions of closed complements; dimension
of such a union is the maximum of their dimensions. Naturality of the adjunction unit
therefore gives a directed family of these kernels. The support-union theorem says its
local sections exhaust F. Cohomology of a quasi-compact quasi-separated scheme commutes
with this directed union. Each cohomology class thus comes from a zero group and is zero. -/
theorem subsingleton_H_of_bounded_support
    {K : Type u} [Field K] {B : Scheme.{u}} [IsAffine B]
    (b : B ⟶ Spec (.of K)) [LocallyOfFiniteType b] [QuasiCompact b] (a : ℕ)
    (hclosed : ∀ (Z : Scheme.{u}) [IsAffine Z] (i : Z ⟶ B) [IsClosedImmersion i],
      topologicalKrullDim Z ≤ (a : WithBot ℕ∞) →
        Z.HasTorsionCohomologicalDimensionLE a)
    (F : Sheaf B.smallEtaleTopology AddCommGrpCat.{u + 1}) (N : ℕ)
    (hN : 0 < N) (hF : N • 𝟙 F = 0)
    (hstalk : ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ B),
      (a : Cardinal.{u}) < residueFieldTrdeg b (s (IsLocalRing.closedPoint Ω)) →
        IsZero ((Etale.upperStar AddCommGrpCat.{u + 1} s).obj F))
    (q : ℕ) (hq : a < q) : Subsingleton (Sheaf.H F q) := by
  classical
  let I := {U : B.Opens // topologicalKrullDim ((U : Set B)ᶜ : Set B) ≤ (a : WithBot ℕ∞)}
  have : Nonempty I := ⟨⟨⊤, by
    have : IsEmpty (((↑(⊤ : B.Opens) : Set B)ᶜ) : Set B) :=
      ⟨fun x ↦ x.property trivial⟩
    exact (topologicalKrullDim_zero_of_discreteTopology
      (((↑(⊤ : B.Opens) : Set B)ᶜ) : Set B)).trans
      (show (0 : WithBot ℕ∞) ≤ (a : WithBot ℕ∞) from by
        change ((0 : ℕ∞) : WithBot ℕ∞) ≤ ((a : ℕ∞) : WithBot ℕ∞)
        exact WithBot.coe_le_coe.mpr bot_le)⟩⟩
  let m (U : I) := Etale.supportedInι F U.val
  have : ∀ U : I, Mono (m U) := fun U ↦ inferInstanceAs (Mono (kernel.ι _))
  have hdir : ∀ U V : I, ∃ (W : I)
      (φ : Etale.supportedIn F U.val ⟶ Etale.supportedIn F W.val)
      (ψ : Etale.supportedIn F V.val ⟶ Etale.supportedIn F W.val),
      φ ≫ m W = m U ∧ ψ ≫ m W = m V := by
    intro U V
    have hd : topologicalKrullDim ((↑(U.val ⊓ V.val) : Set B)ᶜ : Set B) ≤
        (a : WithBot ℕ∞) := by
      let C : Bool → Set B := fun t ↦ if t then (U.val : Set B)ᶜ else (V.val : Set B)ᶜ
      have heq : ((↑(U.val ⊓ V.val) : Set B)ᶜ : Set B) =
          ⋃ t ∈ (Finset.univ : Finset Bool), C t := by
        ext x
        simp [C, Set.compl_inter, or_comm]
      rw [heq]
      apply Etale.dim_finite_union_le _ C
      · intro t _
        cases t <;> simp only [C, Bool.false_eq_true, ↓reduceIte] <;>
          first | exact V.val.isOpen.isClosed_compl | exact U.val.isOpen.isClosed_compl
      · intro t _
        cases t
        · exact V.property
        · exact U.property
    let W : I := ⟨U.val ⊓ V.val, hd⟩
    obtain ⟨φ, hφ⟩ := supportedIn_factor F U.val W.val inf_le_left
    obtain ⟨ψ, hψ⟩ := supportedIn_factor F V.val W.val inf_le_right
    exact ⟨W, φ, ψ, hφ, hψ⟩
  have hloc : ∀ (V : B.Etale) (s : F.obj.obj (Opposite.op V)),
      ∃ R ∈ B.smallEtaleTopology V, ∀ ⦃W : B.Etale⦄ (g : W ⟶ V), R g →
        ∃ (U : I) (t : (Etale.supportedIn F U.val).obj.obj (Opposite.op W)),
          (m U).hom.app _ t = F.obj.map g.op s := by
    intro V s
    obtain ⟨R, hR, h⟩ := Etale.exists_covering_supportedIn b a F
      (isTorsion_of_nsmul_id_eq_zero hN hF) hstalk V s
    refine ⟨R, hR, ?_⟩
    intro W g hg
    obtain ⟨U, hU, t, ht⟩ := h g hg
    exact ⟨⟨U, hU⟩, t, ht⟩
  have hsurj := (H_map_of_directed_of_locally B m hdir hloc q).1
  refine ⟨fun x y ↦ ?_⟩
  have hz (x : Sheaf.H F q) : x = 0 := by
    obtain ⟨U, z, rfl⟩ := hsurj x
    have := subsingleton_H_supportedIn a hclosed F N hN hF U.val U.property q hq
    rw [Subsingleton.elim z 0, map_zero]
  rw [hz x, hz y]

end AlgebraicGeometry.Scheme
