/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.PrescribedPointSystemData
import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import WeilConjectures.AlgebraicGeometry.Modules.HomSection
import Mathlib.LinearAlgebra.StdBasis
import WeilConjectures.AlgebraicGeometry.PrescribedPointNonzeroJetOpen
import WeilConjectures.AlgebraicGeometry.PrescribedPointJetSmoothNeighborhood

/-!
# Bertini for a linear system with finite prescribed base locus

Source: Stacks Project, Tag 0FD6, and blueprint main-20261015,
finite-cover-curve proof, paragraph 2, first derivative conditions.
(blueprint: lem-zl-prescribed-point-bertini-open).
-/

@[expose] public section

universe u

set_option autoImplicit false
set_option relaxedAutoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
open scoped AlgebraicGeometry

namespace AlgebraicGeometry

open Scheme.Modules

noncomputable section

private def tensorComparison {X Y : Scheme.{u}} (f : X ⟶ Y) :
    tensorPullback f ≅ Scheme.Modules.pullback f :=
  (Classical.choose (exists_tensorPullbackAdjunction f)).leftAdjointUniq
    (pullbackPushforwardAdjunction f)

attribute [local irreducible] tensorPullback tensorPullbackObj

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem tensorUnit_eq {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Y.Modules) :
    tensorSectionsUnit f M =
      (show Γ(M, ⊤) ⟶ Γ((tensorPullback f).obj M, ⊤) from
        ((Classical.choose (exists_tensorPullbackAdjunction f)).unit.app M).app ⊤) := by
  unfold tensorSectionsUnit
  have hi : (homOfLE f.preimage_top.ge).op = 𝟙 (op (⊤ : X.Opens)) := rfl
  erw [hi, ((tensorPullback f).obj M).presheaf.map_id, Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem tensorUnit_smul {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Y.Modules)
    (r : Γ(Y, ⊤)) (s : Γ(M, ⊤)) :
    tensorSectionsUnit f M (r • s) = f.appTop r • tensorSectionsUnit f M s := by
  rw [tensorUnit_eq]
  exact Hom.app_smul _ r s

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem tensorUnit_comp {X Y Z : Scheme.{u}} (a : X ⟶ Y) (b : Y ⟶ Z)
    (M : Z.Modules) (s : Γ(M, ⊤)) :
    ((tensorSectionsComp a b).hom.app M).app ⊤
      (tensorSectionsUnit a _ (tensorSectionsUnit b M s)) =
        tensorSectionsUnit (a ≫ b) M s := by
  have hu := congrArg (fun t ↦ t.app ⊤)
    (unit_conjugateEquiv_symm
      (Classical.choose (exists_tensorPullbackAdjunction (a ≫ b)))
      ((Classical.choose (exists_tensorPullbackAdjunction b)).comp
        (Classical.choose (exists_tensorPullbackAdjunction a)))
      (pushforwardComp a b).inv M)
  rw [tensorUnit_eq, tensorUnit_eq, tensorUnit_eq]
  simp only [Adjunction.comp_unit_app, Hom.comp_app, pushforward_map_app,
    Functor.comp_map, pushforwardComp_inv_app_app] at hu
  exact (ConcreteCategory.congr_hom hu s).symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem tensorUnit_comparison {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Y.Modules)
    (s : Γ(M, ⊤)) :
    ((tensorComparison f).hom.app M).app ⊤
      (tensorSectionsUnit f M s) = pullbackSection f s := by
  rw [tensorUnit_eq]
  exact congrArg (fun t ↦ t.app ⊤ s)
    ((Classical.choose (exists_tensorPullbackAdjunction f)).unit_leftAdjointUniq_hom_app
      (pullbackPushforwardAdjunction f) M)

private theorem zeroLocus_section_iso {X : Scheme.{u}} {M N : X.Modules}
    (e : M ≅ N) (s : Γ(M, ⊤)) :
    (homOfGlobalSection N (e.hom.app ⊤ s)).zeroLocus =
      (homOfGlobalSection M s).zeroLocus := by
  have h : homOfGlobalSection M s ≫ e.hom =
      homOfGlobalSection N (e.hom.app ⊤ s) := by
    apply unit_hom_ext
    simp only [Hom.comp_app, ConcreteCategory.comp_apply, homOfGlobalSection_app_one,
      presheaf_map_id_apply]
  exact Hom.zeroLocus_eq_of_arrowIso _ _
    (Arrow.isoMk (Iso.refl _) e.symm (by
      change 𝟙 _ ≫ homOfGlobalSection M s =
        homOfGlobalSection N (e.hom.app ⊤ s) ≫ e.inv
      rw [← h, Category.assoc, Iso.hom_inv_id, Category.comp_id, Category.id_comp]))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem zeroLocus_tensorUnit {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : Y.Modules) [M.IsInvertible] (s : Γ(M, ⊤)) :
    (homOfGlobalSection M s).zeroLocus.comap f =
      (homOfGlobalSection ((tensorPullback f).obj M) (tensorSectionsUnit f M s)).zeroLocus := by
  have := IsInvertible.sheafOfModules_isInvertible M
  have : SheafOfModules.IsInvertible.{u, u, u} (unit Y) :=
    IsInvertible.sheafOfModules_isInvertible (𝟙_ Y.Modules)
  rw [Hom.comap_zeroLocus]
  let e := (tensorComparison f).app M
  have he := zeroLocus_section_iso e (tensorSectionsUnit f M s)
  change (homOfGlobalSection _
    (((tensorComparison f).hom.app M).app ⊤ (tensorSectionsUnit f M s))).zeroLocus = _ at he
  rw [tensorUnit_comparison] at he
  rw [← he]
  apply Hom.zeroLocus_eq_of_arrowIso _ _
  refine Arrow.isoMk (pullbackObjUnitIso f) (Iso.refl _) ?_
  change (pullbackObjUnitIso f).hom ≫
    homOfGlobalSection _ (pullbackSection f s) =
      (Scheme.Modules.pullback f).map (homOfGlobalSection M s) ≫ 𝟙 _
  symm
  rw [Category.comp_id]
  rw [← cancel_epi (pullbackObjUnitIso f).inv, Iso.inv_hom_id_assoc]
  apply unit_hom_ext
  have h := pullbackSection_app_one f (homOfGlobalSection M s)
  simpa only [Scheme.Hom.preimage_top, homOfGlobalSection_app_one,
    presheaf_map_id_apply] using h.symm

private theorem tensorPullback_invertible {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : Y.Modules) [M.IsInvertible] : ((tensorPullback f).obj M).IsInvertible :=
  IsInvertible.of_iso ((tensorComparison f).app M).symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem zeroLocus_tensorUnit_comp {X Y Z : Scheme.{u}}
    (a : X ⟶ Y) (b : Y ⟶ Z) (M : Z.Modules) [M.IsInvertible]
    (s : Γ((tensorPullback b).obj M, ⊤)) :
    (homOfGlobalSection _ s).zeroLocus.comap a =
      (homOfGlobalSection _ (((tensorSectionsComp a b).hom.app M).app ⊤
        (tensorSectionsUnit a _ s))).zeroLocus := by
  have := tensorPullback_invertible b M
  rw [zeroLocus_tensorUnit]
  exact (zeroLocus_section_iso ((tensorSectionsComp a b).app M)
    (tensorSectionsUnit a _ s)).symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem zeroLocus_sum_triangle {X Y Z : Scheme.{u}}
    (a : X ⟶ Y) (b : Y ⟶ Z) (c : X ⟶ Z) (p : a ≫ b = c)
    (M : Z.Modules) [M.IsInvertible] {I : Type u} [Fintype I]
    (s : I → Γ(M, ⊤)) (r : I → Γ(Y, ⊤)) (t : I → Γ(X, ⊤))
    (hr : ∀ i, a.appTop (r i) = t i) :
    (homOfGlobalSection _ (∑ i, r i • tensorSectionsUnit b M (s i))).zeroLocus.comap a =
      (homOfGlobalSection _ (∑ i, t i • tensorSectionsUnit c M (s i))).zeroLocus := by
  subst c
  rw [zeroLocus_tensorUnit_comp]
  congr 1
  congr 1
  rw [map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [tensorUnit_smul, Hom.app_smul, tensorUnit_comp, hr]


set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem exists_open_smooth_native
    {k : Type u} [Field k] {T : Scheme.{u}} (g : T ⟶ Spec (.of k)) [Smooth g]
    (L : T.Modules) [L.IsInvertible] {I : Type u} [Fintype I]
    (s : I → Γ(L, ⊤))
    (hgen : Epi (L.freeHomEquiv.symm (bertiniSectionFamily L s)))
    [IsImmersion (ProjectiveSpace.homOfGeneratingSections I g L
      (bertiniSectionFamily L s) hgen)] :
    ∃ O : (Spec (CommRingCat.of (MvPolynomial I k))).Opens,
      (O : Set (Spec (CommRingCat.of (MvPolynomial I k)))).Nonempty ∧
      ∀ a : I → k, Set.range (bertiniCoefficientPoint (k := k) a) ⊆ (O : Set _) →
        Smooth ((homOfGlobalSection L (prescribedPointCombination g L s a)).zeroLocus.subschemeι
          ≫ g) := by
  classical
  let ψ : (I → k) →+ Γ(L, ⊤) :=
    { toFun := prescribedPointCombination g L s
      map_zero' := by
        simp only [prescribedPointCombination, Pi.zero_apply, map_zero, zero_smul,
          Finset.sum_const_zero]
      map_add' := by
        intro a b
        simp only [prescribedPointCombination, Pi.add_apply, map_add, add_smul,
          Finset.sum_add_distrib] }
  have hlinear (c : k) (a : I → k) : ψ (c • a) =
      g.appTop ((Scheme.ΓSpecIso (.of k)).inv c) • ψ a := by
    simp only [ψ, AddMonoidHom.coe_mk, ZeroHom.coe_mk, prescribedPointCombination,
      Pi.smul_apply, smul_eq_mul, map_mul, mul_smul, Finset.smul_sum]
  have hb (i : I) : ψ (Pi.basisFun k I i) = s i := by
    change prescribedPointCombination g L s (Pi.basisFun k I i) = _
    unfold prescribedPointCombination
    rw [Finset.sum_eq_single i]
    · simp
    · intro l _ hli
      simp [Pi.basisFun_apply, Ne.symm hli]
    · simp
  have hbs : (fun i ↦ ψ (Pi.basisFun k I i)) = s := funext hb
  have hg : Epi (L.freeHomEquiv.symm
      (bertiniSectionFamily L (fun i ↦ ψ (Pi.basisFun k I i)))) := by
    rwa [hbs]
  have : IsImmersion (ProjectiveSpace.homOfGeneratingSections I g L
      (bertiniSectionFamily L (fun i ↦ ψ (Pi.basisFun k I i))) hg) := by
    simpa only [hbs] using
      (inferInstance : IsImmersion (ProjectiveSpace.homOfGeneratingSections I g L
        (bertiniSectionFamily L s) hgen))
  obtain ⟨O, hO, hgood⟩ := exists_open_smooth_bertiniMember g L (Pi.basisFun k I)
    ψ hlinear hg
  refine ⟨O, hO, fun a ha ↦ ?_⟩
  have h := hgood k a ha
  rw [hbs] at h
  let q := pullback.fst g (Spec.map (CommRingCat.ofHom (algebraMap k k)))
  have hid : Spec.map (CommRingCat.ofHom (algebraMap k k)) = 𝟙 (Spec (.of k)) := by
    simp
  have : IsIso (Spec.map (CommRingCat.ofHom (algebraMap k k))) := by
    rw [hid]
    infer_instance
  have : IsIso q := inferInstance
  let J := (homOfGlobalSection L (prescribedPointCombination g L s a)).zeroLocus
  have hJ : J.comap q = (homOfGlobalSection _ (bertiniMemberSection g L s a)).zeroLocus := by
    rw [zeroLocus_tensorUnit]
    congr 2
    simp only [prescribedPointCombination, map_sum, tensorUnit_smul, bertiniMemberSection]
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    change (q ≫ g).appTop _ = _
    rw [show q ≫ g = pullback.snd g
      (Spec.map (CommRingCat.ofHom (algebraMap k k))) by
        simpa only [hid, Category.comp_id] using
          (pullback.condition (f := g)
            (g := Spec.map (CommRingCat.ofHom (algebraMap k k))))]
  rw [← hJ] at h
  let e := J.comapIso q ≪≫ asIso (pullback.snd q J.subschemeι)
  rw [← MorphismProperty.cancel_left_of_respectsIso (P := @Smooth) e.hom]
  have he : e.hom ≫ J.subschemeι ≫ g = (J.comap q).subschemeι ≫
      pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap k k))) := by
    dsimp only [e, Iso.trans_hom, asIso_hom]
    simp only [Category.assoc]
    rw [← pullback.condition_assoc, Scheme.IdealSheafData.comapIso_hom_fst_assoc]
    congr 1
    simpa only [hid, Category.comp_id] using
      (pullback.condition (f := g)
            (g := Spec.map (CommRingCat.ofHom (algebraMap k k))))
  exact he.symm ▸ h

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem prescribedPointMember_comap_open
    {k : Type u} [Field k] {X Y : Scheme.{u}}
    (f : Y ⟶ Spec (.of k)) (j : X ⟶ Y) (g : X ⟶ Spec (.of k))
    (hover : j ≫ f = g) (M : Y.Modules) [M.IsInvertible]
    (U : X.Opens) {I : Type u} [Fintype I] (s : I → Γ(M, ⊤)) (a : I → k) :
    (prescribedPointMember f j M s a).comap U.ι =
      (homOfGlobalSection ((tensorPullback (U.ι ≫ j)).obj M)
        (prescribedPointCombination (U.ι ≫ g) ((tensorPullback (U.ι ≫ j)).obj M)
          (fun i ↦ tensorSectionsUnit (U.ι ≫ j) M (s i)) a)).zeroLocus := by
  unfold prescribedPointMember prescribedPointCombination
  rw [map_sum]
  simp_rw [tensorUnit_smul]
  apply zeroLocus_sum_triangle U.ι j (U.ι ≫ j) rfl M s
  intro i
  change (U.ι ≫ j ≫ f).appTop _ = _
  rw [hover]

private theorem smooth_open_preimage_of_comap
    {k : Type u} [Field k] {X : Scheme.{u}} (p : X ⟶ Spec (.of k))
    (J : X.IdealSheafData) (U : X.Opens)
    (hs : Smooth ((J.comap U.ι).subschemeι ≫ U.ι ≫ p)) :
    Smooth ((J.subschemeι ⁻¹ᵁ U).ι ≫ J.subschemeι ≫ p) := by
  let h := isPullback_morphismRestrict J.subschemeι U
  let h' := J.isPullback_comap U.ι
  let e := h.isoIsPullback _ _ h'
  have he : e.hom ≫ (J.comap U.ι).subschemeι = J.subschemeι ∣_ U :=
    h.isoIsPullback_hom_fst _ _ h'
  have ht : Smooth (e.hom ≫ (J.comap U.ι).subschemeι ≫ U.ι ≫ p) := by
    infer_instance
  rwa [← Category.assoc e.hom, he, morphismRestrict_ι_assoc] at ht

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The smoothness and nonzero-jet open for a finite linear system with prescribed
base points. The ambient smooth scheme need not be affine or connected.

Source: Stacks Project, Tag 0FD6; blueprint main-20261015, finite-cover-curve proof,
paragraph 2, derivative conditions at the prescribed points.
(blueprint: lem-zl-prescribed-point-bertini-open).

Proof: Apply Bertini smoothness to the system on the complement U. At each closed
base point, smoothness and pure dimension identify the dimension of the cotangent
fibre with d, which is positive. The invertible stalk is free of rank one, so its
jet module is nonzero. The jet map on the vanishing subspace is k-linear: changing
a stalk frame cancels between the two tensor factors. Each zero-jet locus is
therefore a linear closed subset of affine coefficient space. Choose nonzero
vectors at every base point and lift the tuple by simultaneous jet surjectivity.
The complements of these finitely many zero-jet loci have nonempty intersection.
Intersect this open with the Bertini open; affine space over k is irreducible, so
the intersection is still nonempty. At each base point the cotangent map to the
relative differential fibre is an isomorphism (the residue field is k). Hence
a nonzero jet gives a nonzero differential of the local equation; the smooth
hypersurface criterion supplies a smooth neighbourhood. Together with the open
complement of the base points these neighbourhoods cover the member, which is
smooth. The resulting coefficient open has both asserted properties.
-/
theorem exists_open_prescribedPoint_bertini
    {k : Type u} [Field k] [IsAlgClosed k]
    (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [Smooth (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))]
    (d : ℕ) (hd : 2 ≤ d) (hdim : X.IsPureDimension d)
    (S : Finset X) (hS : S.Nonempty) (hclosed : ∀ x ∈ S, IsClosed ({x} : Set X))
    {Y : Scheme.{u}} (f : Y ⟶ Spec (.of k)) (j : X ⟶ Y)
    (hover : j ≫ f = X ↘ Spec (.of k))
    (M : Y.Modules) [M.IsInvertible] [((tensorPullback j).obj M).IsInvertible]
    (U : X.Opens) (hU : ∀ x : X, x ∈ U ↔ x ∉ S)
    {I : Type u} [Fintype I] (s : I → Γ(M, ⊤))
    (hvan : ∀ a : I → k, prescribedPointVanishes ((tensorPullback j).obj M) S
      (tensorSectionsUnit j M (prescribedPointCombination f M s a)))
    (hgen : ∃ ht : Epi ((((tensorPullback (U.ι ≫ j)).obj M).freeHomEquiv).symm
        (prescribedPointRestrictedFamily M j U s)),
      @IsImmersion U.toScheme _
        (@ProjectiveSpace.homOfGeneratingSections I inferInstance U.toScheme
          (Spec (.of k)) (U.ι ≫ (X ↘ Spec (.of k)))
          ((tensorPullback (U.ι ≫ j)).obj M)
          ((invertible_pullback_tensor (U.ι ≫ j)).1 M).2
          (prescribedPointRestrictedFamily M j U s) ht))
    (hjet : Function.Surjective (fun a : I → k ↦ fun x : S ↦
      prescribedPointJet ((tensorPullback j).obj M) x.val
        (tensorSectionsUnit j M (prescribedPointCombination f M s a)))) :
    ∃ O : (Spec (CommRingCat.of (MvPolynomial I k))).Opens,
      (O : Set (Spec (CommRingCat.of (MvPolynomial I k)))).Nonempty ∧
      ∀ a : I → k, Set.range (bertiniCoefficientPoint (k := k) a) ⊆ (O : Set _) →
        Smooth ((prescribedPointMember f j M s a).subschemeι ≫ (X ↘ Spec (.of k))) ∧
        ∀ x ∈ S, prescribedPointJet ((tensorPullback j).obj M) x
          (tensorSectionsUnit j M (prescribedPointCombination f M s a)) ≠ 0 := by
  classical
  obtain ⟨x₀, hx₀⟩ := hS
  let L := (tensorPullback (U.ι ≫ j)).obj M
  have : L.IsInvertible := ((invertible_pullback_tensor (U.ι ≫ j)).1 M).2
  obtain ⟨ht, hImm⟩ := hgen
  have : IsImmersion (ProjectiveSpace.homOfGeneratingSections I
      (U.ι ≫ (X ↘ Spec (.of k))) L
      (bertiniSectionFamily L (fun i ↦ tensorSectionsUnit (U.ι ≫ j) M (s i))) ht) := hImm
  have : Smooth (U.ι ≫ (X ↘ Spec (.of k))) := inferInstance
  obtain ⟨O, hO, hgood⟩ := exists_open_smooth_native
    (U.ι ≫ (X ↘ Spec (.of k))) L
    (fun i ↦ tensorSectionsUnit (U.ι ≫ j) M (s i)) ht
  obtain ⟨W, hW, hjets⟩ := exists_open_prescribedPoint_nonzeroJets
    X d hd hdim S hclosed f j hover M s hvan hjet
  refine ⟨O ⊓ W, ?_, ?_⟩
  · exact nonempty_preirreducible_inter O.isOpen W.isOpen hO hW
  · intro a ha
    have haO : Set.range (bertiniCoefficientPoint (k := k) a) ⊆ (O : Set _) :=
      fun x hx ↦ (ha hx).1
    have haW : Set.range (bertiniCoefficientPoint (k := k) a) ⊆ (W : Set _) :=
      fun x hx ↦ (ha hx).2
    have hj := hjets a haW
    refine ⟨?_, hj⟩
    let J := prescribedPointMember f j M s a
    have hcomp : Smooth ((J.comap U.ι).subschemeι ≫ U.ι ≫ (X ↘ Spec (.of k))) := by
      rw [prescribedPointMember_comap_open f j (X ↘ Spec (.of k)) hover M U s a]
      exact hgood a haO
    have hloc (z : J.subscheme) : ∃ V : J.subscheme.Opens,
        z ∈ V ∧ Smooth (V.ι ≫ J.subschemeι ≫ (X ↘ Spec (.of k))) := by
      by_cases hz : J.subschemeι z ∈ S
      · exact exists_smooth_neighborhood_of_prescribedPointJet (X ↘ Spec (.of k))
          ((tensorPullback j).obj M)
          (tensorSectionsUnit j M (prescribedPointCombination f M s a)) z
          (hclosed _ hz) (hj _ hz)
      · exact ⟨J.subschemeι ⁻¹ᵁ U, (hU _).mpr hz,
          smooth_open_preimage_of_comap (X ↘ Spec (.of k)) J U hcomp⟩
    choose V hz hV using hloc
    apply IsZariskiLocalAtSource.of_iSup_eq_top (P := @Smooth) V
    · apply eq_top_iff.mpr
      intro z _
      exact TopologicalSpace.Opens.mem_iSup.mpr ⟨z, hz z⟩
    · intro z
      exact hV z

end

end AlgebraicGeometry
