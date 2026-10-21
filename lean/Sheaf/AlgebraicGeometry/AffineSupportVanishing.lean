/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NY
-/
module

public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.AlgebraicGeometry.Over
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import WeilConjectures.AlgebraicGeometry.TorsionEtaleSheaf
public import WeilConjectures.AlgebraicGeometry.EtaleSupport
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
import all Sheaf.AlgebraicGeometry.Sites.SupportedTorsionCohomologyBound
import all WeilConjectures.AlgebraicGeometry.Sites.SupportDimension
import WeilConjectures.AlgebraicGeometry.Sites.AffineTorsionCohomologicalDimension
import WeilConjectures.AlgebraicGeometry.Sites.FieldCohomologicalDimension
import WeilConjectures.AlgebraicGeometry.EtaleSheafHExtDerivedComparison
import WeilConjectures.AlgebraicGeometry.TorsionSheafCharacterizations
import Sheaf.AlgebraicGeometry.Sites.SupportDimensionFiniteUnion
import Sheaf.AlgebraicGeometry.EtaleClosedImmersionEssentialImage
import Sheaf.AlgebraicGeometry.Sites.AffineTorsionCohomologicalDimensionOfAffine
import WeilConjectures.AlgebraicGeometry.Sites.CohomologyClopen
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.FreeSheaf
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Stalk

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
      ((DerivedCategory.singleFunctor _ 0).obj G))  :=
  sorry


end AlgebraicGeometry
