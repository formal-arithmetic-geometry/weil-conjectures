/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.FinitelyGeneratedEtaleSubsheaf
public import Sheaf.AlgebraicGeometry.EtaleClosedImmersionEssentialImage
public import Mathlib.AlgebraicGeometry.Properties
import WeilConjectures.AlgebraicGeometry.Sites.ArtinVanishing.Support
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Stalk

/-! Finite support of finitely generated étale subsheaves.
Source: Stacks Project, Tags 03SA and 04CA; blueprint (blueprint: lem-kun-cp-finite-support).
-/

@[expose] public section

universe v

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

private theorem support_mono {X : Scheme.{v}}
    {G F : Sheaf X.smallEtaleTopology AddCommGrpCat.{v + 1}}
    (f : G ⟶ F) [Mono f] : etaleSheafSupport G ⊆ etaleSheafSupport F := by
  have : AB5OfSize.{v, v} AddCommGrpCat.{v + 1} :=
    AB5OfSize_shrink.{v, v, v + 1, v + 1} _
  rintro x ⟨Ω, hΩ, hc, s, hs, hn⟩
  refine ⟨Ω, hΩ, hc, s, hs, ?_⟩
  intro hz
  have : PreservesFiniteLimits
      ((pointSmallEtale s).sheafFiber (A := AddCommGrpCat.{v + 1})) := inferInstance
  have : ((pointSmallEtale s).sheafFiber (A := AddCommGrpCat.{v + 1})).PreservesMonomorphisms :=
    inferInstance
  exact hn (IsZero.of_mono ((pointSmallEtale s).sheafFiber.map f) hz)

private theorem zero_upperStar_of_not_support {X : Scheme.{v}}
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{v + 1})
    {Ω : Type v} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ X)
    (hs : s (IsLocalRing.closedPoint Ω) ∉ etaleSheafSupport F) :
    IsZero ((Etale.upperStar AddCommGrpCat.{v + 1} s).obj F) := by
  apply ((jointlyReflectIsomorphisms_ulift_pointSmallEtale (Spec (.of Ω))
    AddCommGrpCat.{v + 1}).isZero_iff).2
  rintro ⟨_, ⟨w⟩⟩
  let t := (Spec (.of Ω)).algClosurePoint w
  have hz : IsZero ((pointSmallEtale (t ≫ s)).sheafFiber.obj F) := by
    by_contra hn
    apply hs
    refine ⟨_, inferInstance, inferInstance, t ≫ s, ?_, hn⟩
    exact congrArg s (Subsingleton.elim _ _)
  have hz' := hz.of_iso ((Etale.upperStarCompSheafFiberIso
    AddCommGrpCat.{v + 1} s t).app F)
  exact hz'.of_iso ((pointSmallEtale t).uliftSheafFiberIso
    AddCommGrpCat.{v + 1} |>.app ((Etale.upperStar AddCommGrpCat.{v + 1} s).obj F))

private theorem nonvanishing_image_mem_support {X : Scheme.{v}}
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{v + 1})
    (U : X.Etale) (s : F.obj.obj (Opposite.op U)) (u : U.left)
    (hu : u ∉ Etale.vanishingLocus F s) : U.hom u ∈ etaleSheafSupport F := by
  by_contra h
  apply hu
  apply Etale.mem_vanishingLocus_of_isZero_upperStar F s u
  intro Ω _ _ t ht
  exact zero_upperStar_of_not_support F t (ht ▸ h)

private theorem section_finite_support {K : Type v} [Field K]
    {X : Scheme.{v}} (f : X ⟶ Spec (.of K)) [LocallyOfFiniteType f]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{v + 1})
    (hF : etaleSheafSupport F ⊆ {x | IsClosed ({x} : Set X)})
    (U : X.Etale) (hU : IsAffine U.left) (s : F.obj.obj (Opposite.op U)) :
    ∃ E : Set X, E.Finite ∧ (∀ x ∈ E, IsClosed ({x} : Set X)) ∧
      ∀ u : U.left, u ∉ Etale.vanishingLocus F s → U.hom u ∈ E := by
  have : Etale U.hom := U.prop
  have : IsAffine U.left := hU
  have : IsLocallyNoetherian U.left := LocallyOfFiniteType.isLocallyNoetherian (U.hom ≫ f)
  have : IsNoetherian U.left := ⟨⟩
  obtain ⟨A, hAfin, hA, hcover⟩ :=
    (Etale.isOpen_vanishingLocus s).isClosed_compl.exists_finite_forall_exists_specializes
  refine ⟨U.hom '' A, hAfin.image _, ?_, ?_⟩
  · rintro x ⟨a, ha, rfl⟩
    exact hF (nonvanishing_image_mem_support F U s a (hA ha))
  · intro u hu
    obtain ⟨a, ha, hau⟩ := hcover u hu
    have hx := hF (nonvanishing_image_mem_support F U s a (hA ha))
    have hm : U.hom u ∈ closure ({U.hom a} : Set X) :=
      specializes_iff_mem_closure.mp (hau.map U.hom.continuous)
    rw [hx.closure_eq, Set.mem_singleton_iff] at hm
    exact ⟨a, ha, hm.symm⟩

private theorem support_subset_of_zero_restriction {X : Scheme.{v}}
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{v + 1}) (U : X.Opens)
    (hz : IsZero ((Etale.upperStar AddCommGrpCat.{v + 1} U.ι).obj F)) :
    etaleSheafSupport F ⊆ (U : Set X)ᶜ := by
  rintro x ⟨Ω, hΩ, hc, s, rfl, hn⟩ hx
  have hm : s.base (IsLocalRing.closedPoint Ω) ∈ Set.range U.ι.base := by
    rw [Scheme.Opens.range_ι]
    exact (congrArg s (Subsingleton.elim _ _)) ▸ hx
  let t := IsOpenImmersion.lift U.ι s (Scheme.range_base_subset_of_closedPoint_mem s hm)
  have ht : t ≫ U.ι = s := IsOpenImmersion.lift_fac _ _ _
  have hz' := ((pointSmallEtale t).sheafFiber.map_isZero hz).of_iso
    ((Etale.upperStarCompSheafFiberIso AddCommGrpCat.{v + 1} U.ι t).app F).symm
  rw [ht] at hz'
  exact hn hz'

/-- Every finitely generated étale subsheaf has finite closed support and is the direct image from
its reduced closed support. Source: Stacks Project, Tags 03SA and 04CA;
blueprint `lem-kun-cp-approximation` (blueprint: lem-kun-cp-finite-support).

Proof: the complement of a generator's vanishing locus in its affine chart is closed.
The chart is Noetherian, so finitely many points specialize to every point of this locus.
Their images belong to the support of `F` and are closed; specialization forces all image
points to be among these finitely many images. For the finite union `T` of these sets,
each generator vanishes over the open complement. It therefore lifts to the kernel of
restriction to that complement, and the minimality of the generated subsheaf puts `G`
inside this kernel. Its support is contained in `T`. A monomorphism gives inclusion of
supports, so every support point is closed and the finite support is closed. Give it the
reduced induced subscheme structure. The closed-immersion essential-image theorem and
invertibility of the adjunction counit make the unit of `G` invertible, giving the stated
isomorphism. Empty generator families and empty support are included.
-/
theorem closedPointSheaf_finitelyGenerated_finiteSupport
    {K : Type v} [Field K] [IsSepClosed K] (X : Scheme.{v})
    [X.Over (Spec (.of K))] [LocallyOfFiniteType (X ↘ Spec (.of K))]
    [QuasiCompact (X ↘ Spec (.of K))]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{v + 1})
    (hF : etaleSheafSupport F ⊆ {x | IsClosed ({x} : Set X)}) :
    ∀ G : Subobject F, IsFinitelyGeneratedEtaleSubsheaf G →
      (etaleSheafSupport (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{v + 1})).Finite ∧
      etaleSheafSupport (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{v + 1}) ⊆
        {x | IsClosed ({x} : Set X)} ∧
      ∃ (Z : Scheme.{v}) (i : Z ⟶ X) (_ : IsClosedImmersion i) (_ : IsReduced Z),
        Set.range i.base =
          etaleSheafSupport (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{v + 1}) ∧
        Nonempty ((G : Sheaf X.smallEtaleTopology AddCommGrpCat.{v + 1}) ≅
          (Etale.lowerStar AddCommGrpCat.{v + 1} i).obj
            ((Etale.upperStar AddCommGrpCat.{v + 1} i).obj
              (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{v + 1}))) := by
  classical
  intro G hG
  have hclosed := (support_mono G.arrow).trans hF
  obtain ⟨n, V, hV, s, hs, hmin⟩ := hG
  choose E hE hEc hEs using fun j ↦
    section_finite_support (X ↘ Spec (.of K)) F hF (V j) (hV j) (s j)
  let T : Set X := ⋃ j : Fin n, E j
  have hT : T.Finite := Set.finite_iUnion hE
  have hTc : IsClosed T := by
    have hc (x : X) (hx : x ∈ T) : IsClosed ({x} : Set X) := by
      obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hx
      exact hEc j x hj
    simpa only [Set.biUnion_of_singleton] using hT.isClosed_biUnion hc
  let U : X.Opens := ⟨Tᶜ, hTc.isOpen_compl⟩
  let H : Subobject F := Subobject.mk (Etale.supportedInι F U)
  have hGH : G ≤ H := by
    apply hmin H
    intro j
    have hz := Etale.unit_app_eq_zero_of_forall_mem_vanishingLocus F U (s j)
      (fun v hv ↦ by
        by_contra hn
        exact hv (Set.mem_iUnion.mpr ⟨j, hEs j v hn⟩))
    obtain ⟨t, ht⟩ := Scheme.exists_kernel_ι_app_eq_ab _ (s j) hz
    refine ⟨((Subobject.underlyingIso (Etale.supportedInι F U)).inv).hom.app
      (Opposite.op (V j)) t, ?_⟩
    have he := congrArg (fun q : Etale.supportedIn F U ⟶ F ↦
      q.hom.app (Opposite.op (V j)) t)
      (Subobject.underlyingIso_arrow (Etale.supportedInι F U))
    exact he.trans ht
  have hzH : IsZero ((Etale.upperStar AddCommGrpCat.{v + 1} U.ι).obj
      (H : Sheaf X.smallEtaleTopology AddCommGrpCat.{v + 1})) :=
    (Etale.isZero_upperStar_supportedIn F U).of_iso
      ((Etale.upperStar AddCommGrpCat.{v + 1} U.ι).mapIso
        (Subobject.underlyingIso (Etale.supportedInι F U)))
  have hzG := IsZero.of_mono
    ((Etale.upperStar AddCommGrpCat.{v + 1} U.ι).map (Subobject.ofLE G H hGH)) hzH
  have hGT : etaleSheafSupport
      (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{v + 1}) ⊆ T := by
    simpa only [U, TopologicalSpace.Opens.coe_mk, compl_compl] using
      support_subset_of_zero_restriction _ U hzG
  have hfin := hT.subset hGT
  have hC : IsClosed (etaleSheafSupport
      (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{v + 1})) :=
    by simpa only [Set.biUnion_of_singleton] using
      hfin.isClosed_biUnion (fun x hx ↦ hclosed hx)
  let Z := (Scheme.IdealSheafData.vanishingIdeal ⟨_, hC⟩).subscheme
  let i : Z ⟶ X := (Scheme.IdealSheafData.vanishingIdeal ⟨_, hC⟩).subschemeι
  have hi : Set.range i.base = etaleSheafSupport
      (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{v + 1}) := by
    exact Scheme.IdealSheafData.range_subschemeι _
  have hess := (Etale.lowerStar_closedImmersion_fullyFaithful_leftInverse_essImage i).2.2.2
  obtain ⟨A, ⟨e⟩⟩ := (hess (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{v + 1})).mpr
    (by rw [hi])
  let L := Etale.upperStar AddCommGrpCat.{v + 1} i
  let R := Etale.lowerStar AddCommGrpCat.{v + 1} i
  let adj := Etale.upperStarLowerStarAdjunction AddCommGrpCat.{v + 1} i
  have : IsIso (adj.unit.app (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{v + 1})) := by
    have : IsIso (adj.unit.app (R.obj A)) := inferInstance
    have hi : IsIso (e.hom ≫ adj.unit.app
        (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{v + 1})) := by
      rw [← adj.unit_naturality]
      infer_instance
    exact IsIso.of_isIso_comp_left e.hom _
  exact ⟨hfin, hclosed, Z, i, inferInstance, inferInstance, hi,
    ⟨asIso (adj.unit.app (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{v + 1}))⟩⟩

end AlgebraicGeometry.Scheme
