/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NY
-/
module

public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.AlgebraicGeometry.Over
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Sheaf.AlgebraicGeometry.TorsionEtaleSheaf
public import Sheaf.AlgebraicGeometry.EtaleSupport
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
import all Sheaf.AlgebraicGeometry.Sites.SupportedTorsionCohomologyBound
import all WeilConjectures.AlgebraicGeometry.Sites.SupportDimension
import WeilConjectures.AlgebraicGeometry.Sites.AffineTorsionCohomologicalDimension
import WeilConjectures.AlgebraicGeometry.Sites.FieldCohomologicalDimension
import WeilConjectures.AlgebraicGeometry.EtaleSheafHExtDerivedComparison
import WeilConjectures.AlgebraicGeometry.TorsionSheafCharacterizations
import Sheaf.AlgebraicGeometry.Sites.SupportDimensionFiniteUnion

/-!
# Affine torsion cohomology with a transcendence-degree support bound

Source: Stacks Project, Etale Cohomology, Tag 0F0W, lemma-interlude-II,
separably closed base-field case (blueprint: lem-kun-affine-support-vanishing).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

private theorem isTorsion_of_mono {X : Scheme.{u}}
    {F G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (f : F ⟶ G) [Mono f] (hG : G.IsTorsion) : F.IsTorsion := by
  have : Mono f.hom := (sheafToPresheaf _ _).map_mono f
  intro U s
  obtain ⟨R, hR, h⟩ := hG (f.hom.app U s)
  refine ⟨R, hR, ?_⟩
  intro V g hg
  obtain ⟨n, hn, hz⟩ := isOfFinAddOrder_iff_nsmul_eq_zero.mp (h hg)
  refine isOfFinAddOrder_iff_nsmul_eq_zero.mpr ⟨n, hn, ?_⟩
  apply (AddCommGrpCat.mono_iff_injective (f.hom.app (Opposite.op V))).mp inferInstance
  rw [map_nsmul, map_zero, NatTrans.naturality_apply]
  exact hz

private theorem subsingleton_H_supportedIn_torsion
    {B : Scheme.{u}} [IsAffine B] (a : ℕ)
    (hclosed : ∀ (Z : Scheme.{u}) [IsAffine Z] (i : Z ⟶ B) [IsClosedImmersion i],
      topologicalKrullDim Z ≤ (a : WithBot ℕ∞) →
        Z.HasTorsionCohomologicalDimensionLE a)
    (F : Sheaf B.smallEtaleTopology AddCommGrpCat.{u + 1}) (hF : F.IsTorsion)
    (U : B.Opens)
    (hU : topologicalKrullDim ((U : Set B)ᶜ : Set B) ≤ (a : WithBot ℕ∞))
    (q : ℕ) (hq : a < q) : Subsingleton (Sheaf.H (Etale.supportedIn F U) q) := by
  let A := Etale.supportedIn F U
  let Z := (Scheme.IdealSheafData.vanishingIdeal
    ⟨(U : Set B)ᶜ, U.isOpen.isClosed_compl⟩).subscheme
  let i : Z ⟶ B := U.closedComplement
  have : IsAffine Z := isAffine_of_isAffineHom i
  have hdim : topologicalKrullDim Z ≤ (a : WithBot ℕ∞) := by
    have e := i.isClosedEmbedding.isEmbedding.toHomeomorph.trans
      (Homeomorph.setCongr U.range_closedComplement)
    exact (IsHomeomorph.topologicalKrullDim_eq _ e.isHomeomorph).trans_le hU
  obtain ⟨G, ⟨e⟩⟩ := Etale.mem_essImage_lowerStar_of_isZero_upperStar i
    (by rw [U.range_closedComplement, Scheme.Opens.range_ι])
    (Scheme.isZero_upperStar_supportedIn F U)
  have : Mono (Etale.supportedInι F U) := inferInstanceAs (Mono (kernel.ι _))
  have hA : A.IsTorsion := isTorsion_of_mono (Etale.supportedInι F U) hF
  let eG := (asIso
    ((Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} i).counit.app G)).symm ≪≫
      (Etale.upperStar AddCommGrpCat.{u + 1} i).mapIso e
  have hG : G.IsTorsion :=
    isTorsion_of_mono eG.hom (Etale.isTorsion_upperStar i hA)
  have hcoh : Subsingleton (Sheaf.H G q) := hclosed Z i hdim G hG q hq
  have : Subsingleton (Sheaf.H ((𝟭 _).obj G) q) := hcoh
  have hpushed : Subsingleton (Sheaf.H
      ((Etale.lowerStar AddCommGrpCat.{u + 1} i).obj G) q) :=
    (Etale.bijective_edgeMap_of_isFinite i G q).injective.subsingleton
  have : Subsingleton ((Sheaf.functorH B.smallEtaleTopology q).obj
      ((Etale.lowerStar AddCommGrpCat.{u + 1} i).obj G)) := hpushed
  exact ((Sheaf.functorH B.smallEtaleTopology q).mapIso e.symm).addCommGroupIsoToAddEquiv
    |>.injective.subsingleton

/-- Over a separably closed field, torsion abelian etale sheaf cohomology on an affine
finite-type scheme vanishes above the transcendence-degree bound on its support.
Source: Stacks Project, Tag 0F0W, lemma-interlude-II, separably closed base-field case
(blueprint: lem-kun-affine-support-vanishing).

Proof:
1. By `def-kun-support` the geometric stalks vanish above the bound. Apply
   `lem-sc-support-dimension-union` to express the sheaf as the filtered union of
   kernels of restriction away from closed subsets of dimension at most `c`.
   The empty subset is allowed and finite unions give upper bounds.
2. Kernel inclusions are sectionwise injective (`def-pur-abelian-sheaf-kernel`),
   so the kernels are torsion and supported on their corresponding closed subsets.
   Realize these by closed subschemes (`lem-weil-pbc-closed-subset-closed-subscheme`).
   Apply `lem-kun-04ca` to express each kernel as a closed pushforward.
   The inverse-image stalk formula `lemma-openclosed-stalk-upperstar` and
   `lem-weil-pbc-torsion-sheaf-characterizations` show the sheaf upstairs is torsion.
   Here inverse and direct image are `def-weil-pbc-inverse-image` and
   `def-weil-pbc-direct-image`; open restriction is supplied by
   `lem-weil-pbc-etale-site-localization-open`.
3. A closed subscheme of an affine finite-type scheme is affine finite type,
   with dimension at most `c`: its ring is a quotient of the ambient algebra.
   The quotient is generated by one element as a module, so its immersion is finite.
   Use `def-weil-closed-immersion`, `lem-weil-pbc-lft-affine-pairs`,
   `def-weil-finite-type-morphism` and `def-weil-finite-integral-morphism`.
4. `lem-kun-cd-sep-closed-point` gives base-field cohomological dimension zero.
   The notions `def-kun-cd` and `def-sc-etale-torsion-cd` agree on torsion sheaves.
   Apply `thm-sc-affine-torsion-cd` to each closed subscheme. For an empty subscheme,
   the empty covering forces every sheaf to be zero, so cohomology is zero as well.
   `lem-weil-pbc-finite-pushforward-cohomology` transfers this vanishing downstairs.
5. The ambient affine scheme is qcqs (`lem-weil-pbc-affine-scheme-qcqs`).
   Apply `lem-weil-pbc-cohomology-filtered-colimit`: all stage cohomology groups
   in degree greater than `c` vanish, so their filtered colimit vanishes. -/
theorem affine_support_vanishing
    {L : Type u} [Field L] [IsSepClosed L]
    (T : Scheme.{u}) [IsAffine T] [T.Over (Spec (.of L))]
    [LocallyOfFiniteType (T ↘ Spec (.of L))] [QuasiCompact (T ↘ Spec (.of L))]
    (G : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hG : Scheme.IsTorsionAbelianSheaf G) (c : ℕ)
    (hsupport : Scheme.etaleSheafSupport G ⊆ (T ↘ Spec (.of L)).pointsOfTrdegLE c)
    (r : ℤ) (hr : (c : ℤ) < r) :
    IsZero ((Etale.cohomology AddCommGrpCat.{u + 1} T r).obj
      ((DerivedCategory.singleFunctor _ 0).obj G))  := by
  classical
  have hGt : G.IsTorsion := (Scheme.isTorsionAbelianSheaf_characterizations G).1.mp hG
  have hstalk : ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω]
      (s : Spec (.of Ω) ⟶ T),
      (c : Cardinal.{u}) < Scheme.residueFieldTrdeg (T ↘ Spec (.of L))
        (s (IsLocalRing.closedPoint Ω)) →
      IsZero ((Etale.upperStar AddCommGrpCat.{u + 1} s).obj G) := by
    intro Ω _ _ s hs
    apply (IsZero.iff_id_eq_zero _).2
    apply Scheme.sheafHom_ext_of_sheafFiber_map_algClosurePoint
    intro x
    let t := (Spec (.of Ω)).algClosurePoint x
    have hz : IsZero ((Scheme.pointSmallEtale (t ≫ s)).sheafFiber.obj G) := by
      by_contra hn
      have hm := hsupport ⟨_, inferInstance, inferInstance, t ≫ s, rfl, hn⟩
      have hpoint : (t ≫ s) default = s (IsLocalRing.closedPoint Ω) := by
        rw [Scheme.Hom.comp_apply]
        exact congrArg s (Subsingleton.elim _ _)
      rw [hpoint] at hm
      apply not_le_of_gt hs
      unfold Scheme.residueFieldTrdeg
      rw [Etale.residueFieldHomOfOver_eq]
      exact hm
    have hz' := hz.of_iso
      ((Etale.upperStarCompSheafFiberIso AddCommGrpCat.{u + 1} s t).app G)
    let P := (Scheme.pointSmallEtale t).sheafFiber (A := AddCommGrpCat.{u + 1})
    calc
      P.map (𝟙 _) = 𝟙 _ := P.map_id _
      _ = 0 := hz'.eq_of_src _ _
      _ = P.map 0 := (P.map_zero _ _).symm
  have hclosed : ∀ (Z : Scheme.{u}) [IsAffine Z] (i : Z ⟶ T) [IsClosedImmersion i],
      topologicalKrullDim Z ≤ (c : WithBot ℕ∞) →
        Z.HasTorsionCohomologicalDimensionLE c := by
    intro Z _ i _ hd
    simpa only [Nat.add_zero] using
      Scheme.hasTorsionCohomologicalDimensionLE_of_isAffine
        (Scheme.hasTorsionCohomologicalDimensionLE_zero_of_isSepClosed L)
        (i ≫ (T ↘ Spec (.of L))) hd
  have hnonneg : 0 ≤ r := le_trans (by positivity : (0 : ℤ) ≤ c) hr.le
  obtain ⟨q, rfl⟩ := Int.eq_ofNat_of_zero_le hnonneg
  have hq : c < q := by exact_mod_cast hr
  suffices hH : Subsingleton (Sheaf.H G q) by
    have : Subsingleton ((Sheaf.functorH T.smallEtaleTopology q).obj G) := hH
    obtain ⟨e⟩ := Scheme.nonempty_sheafH_extDerivedIso T q
    have : Subsingleton ((Etale.cohomology AddCommGrpCat.{u + 1} T q).obj
        ((DerivedCategory.singleFunctor _ 0).obj G)) :=
      (e.app G).addCommGroupIsoToAddEquiv.symm.injective.subsingleton
    exact AddCommGrpCat.isZero_of_subsingleton _
  let I := {U : T.Opens // topologicalKrullDim ((U : Set T)ᶜ : Set T) ≤ (c : WithBot ℕ∞)}
  have : Nonempty I := ⟨⟨⊤, by
    have : IsEmpty (((↑(⊤ : T.Opens) : Set T)ᶜ) : Set T) :=
      ⟨fun x ↦ x.property trivial⟩
    exact (topologicalKrullDim_zero_of_discreteTopology
      (((↑(⊤ : T.Opens) : Set T)ᶜ) : Set T)).trans
      (show (0 : WithBot ℕ∞) ≤ (c : WithBot ℕ∞) from by
        change ((0 : ℕ∞) : WithBot ℕ∞) ≤ ((c : ℕ∞) : WithBot ℕ∞)
        exact WithBot.coe_le_coe.mpr bot_le)⟩⟩
  let m (U : I) := Etale.supportedInι G U.val
  have : ∀ U : I, Mono (m U) := fun U ↦ inferInstanceAs (Mono (kernel.ι _))
  have hdir : ∀ U V : I, ∃ (W : I)
      (φ : Etale.supportedIn G U.val ⟶ Etale.supportedIn G W.val)
      (ψ : Etale.supportedIn G V.val ⟶ Etale.supportedIn G W.val),
      φ ≫ m W = m U ∧ ψ ≫ m W = m V := by
    intro U V
    have hd : topologicalKrullDim ((↑(U.val ⊓ V.val) : Set T)ᶜ : Set T) ≤
        (c : WithBot ℕ∞) := by
      let C : Bool → Set T := fun t ↦ if t then (U.val : Set T)ᶜ else (V.val : Set T)ᶜ
      have heq : ((↑(U.val ⊓ V.val) : Set T)ᶜ : Set T) =
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
    obtain ⟨φ, hφ⟩ := Scheme.supportedIn_factor G U.val W.val inf_le_left
    obtain ⟨ψ, hψ⟩ := Scheme.supportedIn_factor G V.val W.val inf_le_right
    exact ⟨W, φ, ψ, hφ, hψ⟩
  have hloc : ∀ (V : T.Etale) (s : G.obj.obj (Opposite.op V)),
      ∃ R ∈ T.smallEtaleTopology V, ∀ ⦃W : T.Etale⦄ (g : W ⟶ V), R g →
        ∃ (U : I) (t : (Etale.supportedIn G U.val).obj.obj (Opposite.op W)),
          (m U).hom.app _ t = G.obj.map g.op s := by
    intro V s
    obtain ⟨R, hR, h⟩ := Etale.exists_covering_supportedIn (T ↘ Spec (.of L)) c G
      hGt hstalk V s
    refine ⟨R, hR, ?_⟩
    intro W g hg
    obtain ⟨U, hU, t, ht⟩ := h g hg
    exact ⟨⟨U, hU⟩, t, ht⟩
  have hsurj := (Scheme.H_map_of_directed_of_locally T m hdir hloc q).1
  refine ⟨fun x y ↦ ?_⟩
  have hz (x : Sheaf.H G q) : x = 0 := by
    obtain ⟨U, z, rfl⟩ := hsurj x
    have := subsingleton_H_supportedIn_torsion c hclosed G hGt U.val U.property q hq
    rw [Subsingleton.elim z 0, map_zero]
  rw [hz x, hz y]


end AlgebraicGeometry
