/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective
public import WeilConjectures.AlgebraicGeometry.InvertibleSectionRing
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Twist
public import WeilConjectures.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import WeilConjectures.AlgebraicGeometry.Ample
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization
import WeilConjectures.AlgebraicGeometry.SectionRingLocalizationBijective
import WeilConjectures.AlgebraicGeometry.SectionRingCoefficientHom
import WeilConjectures.AlgebraicGeometry.ClosedImmersionUnitKernel
import WeilConjectures.AlgebraicGeometry.Modules.LocalPresentation
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed
import Mathlib.Algebra.DirectSum.Algebra
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
import WeilConjectures.AlgebraicGeometry.Modules.HilbertPolynomial
import WeilConjectures.AlgebraicGeometry.Cohomology.AcyclicResolution
import WeilConjectures.AlgebraicGeometry.Cohomology.ProjectiveFinite
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.CoordinateSection
import WeilConjectures.AlgebraicGeometry.Modules.AffineComplement
import WeilConjectures.AlgebraicGeometry.SectionNonvanishingZeroLocus
import Mathlib.AlgebraicGeometry.Noetherian

/-! # Section algebras of projective polarizations

Source: Stacks Project, coherent.tex, Tag 0B5T(1),(3),(4); morphisms.tex,
Tags 0C6J and 0EKE (blueprint: lem-sfb-projective-polarization-section-algebra).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry.Scheme.Modules


open CategoryTheory.Limits in
open scoped DirectSum in
private theorem coordinate_cover {X : Scheme.{u}} (k : Type u) [Field k]
    (ι : Type u) [Finite ι] (j : X ⟶ ProjectiveSpace ι (Spec (CommRingCat.of k)))
    [IsClosedImmersion j] (N : X.Modules) [N.IsInvertible]
    (e : ProjectiveSpace.twistRestrict j 1 ≅ N) :
    ∃ a : ι → (𝟙_ X.Modules ⟶ N),
      (∀ l, IsAffineOpen (Hom.zeroLocus (a l)).support.compl) ∧
      (⨆ l, (Hom.zeroLocus (a l)).support.compl) = ⊤ := by
  classical
  have := IsInvertible.sheafOfModules_isInvertible N
  have := IsInvertible.sheafOfModules_isInvertible
    (ProjectiveSpace.twistRestrict j 1)
  have := IsInvertible.sheafOfModules_isInvertible (𝟙_ X.Modules)
  have := IsInvertible.sheafOfModules_isInvertible
    (𝟙_ (ProjectiveSpace ι (Spec (CommRingCat.of k))).Modules)
  let a (l : ι) : 𝟙_ X.Modules ⟶ N := (pullbackObjUnitIso j).inv ≫
    (pullback j).map (ProjectiveSpace.coordinateSection ι (Spec (.of k)) l) ≫ e.hom
  have ha (l : ι) : (Hom.zeroLocus (a l)).support.compl =
      j ⁻¹ᵁ ProjectiveSpace.standardOpen ι (Spec (.of k)) l := by
    let b := (pullback j).map (ProjectiveSpace.coordinateSection ι (Spec (.of k)) l)
    have h₁ : Hom.zeroLocus (a l) = Hom.zeroLocus b :=
      Hom.zeroLocus_eq_of_arrowIso _ _
        (Arrow.isoMk (pullbackObjUnitIso j).symm e.symm (by simp [a, b]))
    rw [h₁, ← Hom.comap_zeroLocus,
      ← ProjectiveSpace.compl_support_zeroLocus_coordinateSection]
    exact (congrArg TopologicalSpace.Closeds.compl
      (Scheme.IdealSheafData.support_comap _ j)).trans rfl
  have h_aff (l : ι) : IsAffineOpen (Hom.zeroLocus (a l)).support.compl := by
    rw [ha l]
    exact (ProjectiveSpace.isAffineOpen_standardOpen ι (Spec (.of k)) l).preimage j
  refine ⟨a, h_aff, ?_⟩
  simp_rw [ha]
  rw [← Scheme.Hom.preimage_iSup, ProjectiveSpace.iSup_standardOpen,
    Scheme.Hom.preimage_top]

open CategoryTheory.Limits in
open scoped DirectSum in
private theorem affine_locus {X : Scheme.{u}} (k : Type u) [Field k]
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
    (ι : Type u) [Finite ι] (j : X ⟶ ProjectiveSpace ι (Spec (.of k)))
    [IsClosedImmersion j] (L : X.Modules) [L.IsInvertible]
    (r : ℕ) (hr : 0 < r) (e : ProjectiveSpace.twistRestrict j 1 ≅ L.tensorPow r)
    (d : ℕ) (hd : 0 < d) (s : Γ(L.tensorPow d, ⊤)) :
    ∃ U : X.Opens, (U : Set X) = nonvanishingLocus (L.tensorPow d) s ∧
      IsAffineOpen U := by
  classical
  have := IsInvertible.sheafOfModules_isInvertible (L.tensorPow r)
  have := IsInvertible.sheafOfModules_isInvertible ((L.tensorPow r).tensorPow d)
  have := IsInvertible.sheafOfModules_isInvertible (L.tensorPow d)
  have := IsInvertible.sheafOfModules_isInvertible ((L.tensorPow d).tensorPow r)
  have := IsInvertible.sheafOfModules_isInvertible (𝟙_ X.Modules)
  obtain ⟨a, ha, hcov⟩ := coordinate_cover k ι j (L.tensorPow r) e
  let E : (L.tensorPow r).tensorPow d ≅ (L.tensorPow d).tensorPow r :=
    (L.tensorPowMulIso r d).symm ≪≫
      eqToIso (congrArg L.tensorPow (Nat.mul_comm r d)) ≪≫ L.tensorPowMulIso d r
  let b (l : ι) : 𝟙_ X.Modules ⟶ (L.tensorPow d).tensorPow r :=
    tensorPowSection (a l) d ≫ E.hom
  have hb (l : ι) : (Hom.zeroLocus (b l)).support.compl =
      (Hom.zeroLocus (a l)).support.compl := by
    have heq : Hom.zeroLocus (b l) = Hom.zeroLocus (tensorPowSection (a l) d) :=
      Hom.zeroLocus_eq_of_arrowIso _ _
        (Arrow.isoMk (Iso.refl _) E.symm (by simp [b]))
    rw [heq, compl_support_zeroLocus_tensorPowSection _ _ hd]
  have hbcov : (⨆ l, (Hom.zeroLocus (b l)).support.compl) = ⊤ := by
    simpa only [hb] using hcov
  have hA := isAffineOpen_compl_support_zeroLocus f ((L.tensorPow d).tensorPow r) b
    (by intro l; rw [hb l]; exact ha l) hbcov (tensorPowSection (homOfGlobalSection _ s) r)
  rw [compl_support_zeroLocus_tensorPowSection _ _ hr] at hA
  exact ⟨(Hom.zeroLocus (homOfGlobalSection _ s)).support.compl,
    (nonvanishingLocus_eq_compl_support_zeroLocus X _ s).symm, hA⟩

open CategoryTheory.Limits in
open scoped DirectSum in
private theorem fraction_chart
    (k : Type u) [Field k] (X : Scheme.{u}) (f : X ⟶ Spec (CommRingCat.of k))
    [IsProper f] (ι : Type u) [Finite ι]
    (j : X ⟶ ProjectiveSpace ι (Spec (.of k))) [IsClosedImmersion j]
    (L : X.Modules) [L.IsInvertible] (r : ℕ) (hr : 0 < r)
    (e : ProjectiveSpace.twistRestrict j 1 ≅ L.tensorPow r)
    (d : ℕ) (hd : 0 < d) (s : sectionRingGrade L d) :
    ∃ U : X.Opens,
      (U : Set X) = nonvanishingLocus (L.tensorPow d) (s.val d) ∧
      IsAffineOpen U ∧ LocallyOfFiniteType (U.ι ≫ f) ∧ QuasiCompact (U.ι ≫ f) ∧
      ∃ e : HomogeneousLocalization.Away (sectionRingGrade L) s.val ≃+* Γ(X, U),
        ∀ (n : ℕ) (a : sectionRingGrade L (n • d)),
          e (HomogeneousLocalization.Away.mk (sectionRingGrade L) s.property n
            a.val a.property) •
            (L.tensorPow (n • d)).presheaf.map (homOfLE (le_top : U ≤ ⊤)).op
              ((s.val ^ n) (n • d)) =
          (L.tensorPow (n • d)).presheaf.map (homOfLE (le_top : U ≤ ⊤)).op
            (a.val (n • d)) := by
  classical
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : IsNoetherian X := ⟨⟩
  obtain ⟨U, hU, ha⟩ := affine_locus k f ι j L r hr e d hd (s.val d)
  have := IsInvertible.sheafOfModules_isInvertible (L.tensorPow d)
  have := IsInvertible.sheafOfModules_isInvertible (𝟙_ X.Modules)
  have hle : U ≤ (Hom.zeroLocus (homOfGlobalSection _ (s.val d))).support.compl := by
    intro x hx
    change x ∈ ((Hom.zeroLocus (homOfGlobalSection _ (s.val d))).support.compl : Set X)
    rw [← nonvanishingLocus_eq_compl_support_zeroLocus]
    exact hU ▸ hx
  have hs : IsFreeGenerator ((L.tensorPow d).presheaf.map
      (homOfLE (le_top : U ≤ ⊤)).op (s.val d)) := by
    rw [← homOfGlobalSection_app_one]
    exact isFreeGenerator_app_one_of_le _ hle
  obtain ⟨ρ, hρ⟩ := exists_sectionRing_coefficient_hom X L d s hd U hs
  have hbij := sectionRing_localization_bijective X L d hd s U hU
    (CommRingCat.ofHom ρ) hρ
  let E := RingEquiv.ofBijective ρ hbij
  have hE : ∀ (n : ℕ) (a : sectionRingGrade L (n • d)),
      E (HomogeneousLocalization.Away.mk (sectionRingGrade L) s.property n
        a.val a.property) •
        (L.tensorPow (n • d)).presheaf.map (homOfLE (le_top : U ≤ ⊤)).op
          ((s.val ^ n) (n • d)) =
        (L.tensorPow (n • d)).presheaf.map (homOfLE (le_top : U ≤ ⊤)).op
          (a.val (n • d)) := hρ
  have hft : LocallyOfFiniteType (U.ι ≫ f) := inferInstance
  have hqc : QuasiCompact (U.ι ≫ f) := inferInstance
  exact ⟨U, hU, ha, hft, hqc, E, hE⟩

open CategoryTheory.Limits in
open scoped DirectSum in
private theorem restriction_surjective
    (k : Type u) [Field k] (X : Scheme.{u}) (f : X ⟶ Spec (CommRingCat.of k))
    [IsProper f] (L : X.Modules) [L.IsInvertible]
    (hL : AlgebraicGeometry.IsAmple f L) (Y : Scheme.{u}) (i : Y ⟶ X)
    [IsClosedImmersion i] (adj' : tensorPullback i ⊣ pushforward i) :
    ∃ M : ℕ, ∀ m : ℕ, M ≤ m → Function.Surjective
      (fun t : SectionRingComponent L m ↦
        (adj'.unit.app (L.tensorPow m)).app ⊤ t) := by
  classical
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have := isQuasicoherent_toModules i.ker
  have := isFinitePresentation_toModules i.ker
  obtain ⟨M, hM⟩ := exists_subsingleton_H_tensorObj_tensorPow k f L hL i.ker.toModules
  refine ⟨M, ?_⟩
  intro m hm
  let N := L.tensorPow m
  let adj := Classical.choice (nonempty_tensorPullbackAdjunction i)
  let μ : i.ker.toModules ⊗ N ⟶ N := i.ker.toModulesι ▷ N ≫ (λ_ N).hom
  have : Mono μ := inferInstance
  obtain ⟨hepi, w, ⟨hk⟩⟩ := closedImmersion_unit_kernel i N
  let e : kernel (adj.unit.app N) ≅ i.ker.toModules ⊗ N :=
    (hk.conePointUniqueUpToIso (kernelIsKernel (adj.unit.app N))).symm ≪≫
      imageMonoIsoSource μ
  have : Subsingleton ((i.ker.toModules ⊗ N).H 1) := hM m hm 1 Nat.zero_lt_one
  have : Subsingleton ((kernel (adj.unit.app N)).H 1) :=
    subsingleton_H_of_iso e.symm 1
  have : Epi (adj.unit.app N) := hepi
  have hS : (ShortComplex.kernelSequence (adj.unit.app N)).ShortExact :=
    ShortComplex.ShortExact.mk' (ShortComplex.kernelSequence_exact _)
      inferInstance (show Epi (adj.unit.app N) from hepi)
  have : Subsingleton ((ShortComplex.kernelSequence (adj.unit.app N)).X₁.H 1) :=
    (inferInstance : Subsingleton ((kernel (adj.unit.app N)).H 1))
  have hs := surjective_app_g_of_subsingleton hS
  have hη : adj'.unit.app N = adj.unit.app N ≫
      (pushforward i).map ((adj.leftAdjointUniq adj').hom.app N) :=
    (adj.unit_leftAdjointUniq_hom_app adj' N).symm
  change Function.Surjective (fun t ↦ (adj'.unit.app N).app ⊤ t)
  rw [hη]
  change Function.Surjective (fun t ↦
    (((pushforward i).map ((adj.leftAdjointUniq adj').hom.app N)).app ⊤)
      ((adj.unit.app N).app ⊤ t))
  exact Function.Surjective.comp
    (ConcreteCategory.bijective_of_isIso
      (((pushforward i).map ((adj.leftAdjointUniq adj').hom.app N)).app ⊤)).2 hs

open CategoryTheory.Limits in
open scoped DirectSum in
private theorem epi_of_section_cover {X : Scheme.{u}} (N : X.Modules)
    [N.IsInvertible] (ι : Type u) [Fintype ι] [DecidableEq ι]
    (a : ι → (𝟙_ X.Modules ⟶ N))
    (ha : ∀ l, IsAffineOpen (Hom.zeroLocus (a l)).support.compl)
    (hcov : (⨆ l, (Hom.zeroLocus (a l)).support.compl) = ⊤) :
    Epi (∑ l, SheafOfModules.freeπ l ≫ a l) := by
  have := IsInvertible.sheafOfModules_isInvertible N
  apply epi_of_surjective_app _ _ ha hcov
  intro l y
  let U := (Hom.zeroLocus (a l)).support.compl
  have hgen := isFreeGenerator_app_one_of_le (a l) (U := U) le_rfl
  obtain ⟨c, hc⟩ := (hgen U le_rfl).2 y
  rw [presheaf_map_id_apply] at hc
  refine ⟨Hom.app (show 𝟙_ X.Modules ⟶ SheafOfModules.free (R := X.ringCatSheaf) ι from
    SheafOfModules.ιFree l) U (unitSectionsEquiv U c), ?_⟩
  have heq : SheafOfModules.ιFree l ≫
      (∑ t, SheafOfModules.freeπ t ≫ a t) = a l := by
    rw [Preadditive.comp_sum, Finset.sum_eq_single l]
    · rw [SheafOfModules.ιFree_freeπ_assoc, if_pos rfl, Category.id_comp]
    · intro t _ ht
      rw [SheafOfModules.ιFree_freeπ_assoc, if_neg (Ne.symm ht), zero_comp]
    · simp
  have he := congrArg (fun b : 𝟙_ X.Modules ⟶ N ↦
    b.app U (unitSectionsEquiv U c)) heq
  rw [Hom.comp_app, ConcreteCategory.comp_apply] at he
  rw [he, unitSectionsEquiv_eq_smul_one, Hom.app_smul]
  exact hc

open CategoryTheory.Limits in
open scoped DirectSum in
private theorem eventually_surjective_tensor
    (k : Type u) [Field k] (X : Scheme.{u}) (f : X ⟶ Spec (CommRingCat.of k))
    [IsProper f] (L : X.Modules) [L.IsInvertible]
    (hL : AlgebraicGeometry.IsAmple f L) {P Q : X.Modules}
    [P.IsQuasicoherent] [P.IsFinitePresentation] [Q.IsQuasicoherent]
    (p : P ⟶ Q) [Epi p] :
    ∃ M : ℕ, ∀ n : ℕ, M ≤ n → Function.Surjective ((p ▷ L.tensorPow n).app ⊤) := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have := isQuasicoherent_kernel p
  have := isFinitePresentation_kernel p
  obtain ⟨M, hM⟩ := exists_subsingleton_H_tensorObj_tensorPow k f L hL (kernel p)
  refine ⟨M, fun n hn ↦ ?_⟩
  have := isEquivalence_tensorRight (L.tensorPow n)
  have hS : (ShortComplex.kernelSequence p).ShortExact :=
    .mk' (ShortComplex.kernelSequence_exact p) inferInstance (show Epi p from inferInstance)
  have : Subsingleton (((ShortComplex.kernelSequence p).map
      (tensorRight (L.tensorPow n))).X₁.H 1) := hM n hn 1 Nat.zero_lt_one
  exact surjective_app_g_of_subsingleton (hS.map_of_exact (tensorRight (L.tensorPow n)))

open CategoryTheory.Limits in
open scoped DirectSum in
private theorem tensor_sum_app {X : Scheme.{u}} {P Q T : X.Modules}
    {ι : Type u} [Fintype ι] (δ : ι → (P ⟶ 𝟙_ X.Modules))
    (a : ι → (𝟙_ X.Modules ⟶ Q)) (w : Γ(P ⊗ T, ⊤)) :
    ((∑ l, δ l ≫ a l) ▷ T).app ⊤ w =
      ∑ l, tmulSection ((a l).app ⊤ (unitSectionsEquiv ⊤ 1))
        ((λ_ T).hom.app ⊤ ((δ l ▷ T).app ⊤ w)) := by
  have : MonoidalPreadditive X.Modules := (SheafOfModules.tensorClosed X.sheaf).1.some
  rw [sum_whiskerRight, Hom.sum_app_apply]
  apply Finset.sum_congr rfl
  intro l _
  rw [comp_whiskerRight, Hom.comp_app, ConcreteCategory.comp_apply]
  have he : (δ l ▷ T).app ⊤ w =
      (λ_ T).inv.app ⊤ ((λ_ T).hom.app ⊤ ((δ l ▷ T).app ⊤ w)) :=
    (inv_app_hom_app_apply_of_iso (λ_ T) _).symm
  calc
    _ = (a l ▷ T).app ⊤ ((λ_ T).inv.app ⊤
        ((λ_ T).hom.app ⊤ ((δ l ▷ T).app ⊤ w))) := congrArg _ he
    _ = _ := by rw [leftUnitor_inv_app, whiskerRight_app_tmulSection]

open CategoryTheory.Limits in
open scoped DirectSum in
private theorem section_recurrence
    (k : Type u) [Field k] (X : Scheme.{u}) (f : X ⟶ Spec (CommRingCat.of k))
    [IsProper f] (L : X.Modules) [L.IsInvertible]
    (hL : AlgebraicGeometry.IsAmple f L) (r : ℕ)
    (ι : Type u) [Fintype ι]
    (a : ι → (𝟙_ X.Modules ⟶ L.tensorPow r))
    (ha : ∀ l, IsAffineOpen (Hom.zeroLocus (a l)).support.compl)
    (hcov : (⨆ l, (Hom.zeroLocus (a l)).support.compl) = ⊤) :
    ∃ M : ℕ, ∀ n : ℕ, M ≤ n → ∀ t : SectionRingComponent L (r + n),
      ∃ b : ι → SectionRingComponent L n,
        t = ∑ l, (L.tensorPowAddIso r n).inv.app ⊤
          (tmulSection ((a l).app ⊤ (unitSectionsEquiv ⊤ 1)) (b l)) := by
  classical
  let P : X.Modules := SheafOfModules.free (R := X.ringCatSheaf) ι
  let δ (l : ι) : P ⟶ 𝟙_ X.Modules := SheafOfModules.freeπ l
  let p : P ⟶ L.tensorPow r := ∑ l, δ l ≫ a l
  have hp : Epi p := epi_of_section_cover (L.tensorPow r) ι a ha hcov
  have := IsInvertible.sheafOfModules_isInvertible (L.tensorPow r)
  have : P.IsQuasicoherent := SheafOfModules.isQuasicoherent_free ι
  have : P.IsFinitePresentation := isFinitePresentation_free (X := X) ι
  obtain ⟨M, hM⟩ := eventually_surjective_tensor k X f L hL p
  refine ⟨M, ?_⟩
  intro n hn t
  obtain ⟨w, hw⟩ := hM n hn ((L.tensorPowAddIso r n).hom.app ⊤ t)
  let b (l : ι) : SectionRingComponent L n :=
    (λ_ (L.tensorPow n)).hom.app ⊤ ((δ l ▷ L.tensorPow n).app ⊤ w)
  refine ⟨b, ?_⟩
  have hw' : (L.tensorPowAddIso r n).hom.app ⊤ t =
      ∑ l, tmulSection ((a l).app ⊤ (unitSectionsEquiv ⊤ 1)) (b l) :=
    hw.symm.trans (tensor_sum_app δ a w)
  have he := congrArg (fun t ↦ (L.tensorPowAddIso r n).inv.app ⊤ t) hw'
  rw [inv_app_hom_app_apply_of_iso] at he
  rw [map_sum] at he
  exact he

open CategoryTheory.Limits in
open scoped DirectSum in
private theorem transport_section_heq {X : Scheme.{u}} {P Q : X.Modules}
    (h : P = Q) {U : X.Opens} (t : Γ(P, U)) :
    HEq ((eqToHom h).app U t) t := by
  subst Q
  rfl

open scoped DirectSum in
@[instance_reducible]
private noncomputable def section_algebra {X : Scheme.{u}}
    (L : X.Modules) [L.IsInvertible] :
    DirectSum.GAlgebra Γ(X, ⊤) (SectionRingComponent L) where
  toFun := (unitSectionsEquiv ⊤).toAddMonoidHom
  map_one := rfl
  map_mul a b := by
    apply Sigma.ext (Nat.zero_add 0).symm
    apply heq_of_eq
    change unitSectionsEquiv ⊤ (a * b) =
      (L.tensorPowAddIso 0 0).inv.app ⊤
        (tmulSection (unitSectionsEquiv ⊤ a) (unitSectionsEquiv ⊤ b))
    simp only [tensorPowAddIso, Iso.trans_inv, Iso.symm_inv, eqToIso.inv,
      eqToHom_refl, Category.comp_id]
    change unitSectionsEquiv ⊤ (a * b) =
      (λ_ (𝟙_ X.Modules)).hom.app ⊤
        (tmulSection (unitSectionsEquiv ⊤ a) (unitSectionsEquiv ⊤ b))
    exact (leftUnitor_hom_app_tmulSection a (unitSectionsEquiv ⊤ b)).symm
  commutes r x := mul_comm _ _
  smul_def r x := by
    obtain ⟨n, t⟩ := x
    apply Sigma.ext (Nat.zero_add n).symm
    change HEq (r • t) ((L.tensorPowAddIso 0 n).inv.app ⊤
      (tmulSection (unitSectionsEquiv ⊤ r) t))
    simp only [tensorPowAddIso, Iso.trans_inv, Iso.symm_inv, eqToIso.inv,
      Hom.comp_app, ConcreteCategory.comp_apply]
    exact (heq_of_eq (leftUnitor_hom_app_tmulSection r t).symm).trans
      (transport_section_heq _ _).symm


open scoped DirectSum in
@[instance_reducible]
private noncomputable def section_algebra_over {X : Scheme.{u}}
    (L : X.Modules) [L.IsInvertible] (k : Type u) [Field k] (c : k →+* Γ(X, ⊤)) :
    let : ∀ n, Module k (SectionRingComponent L n) := fun _ ↦ Module.compHom _ c
    DirectSum.GAlgebra k (SectionRingComponent L) := by
  let : DirectSum.GAlgebra Γ(X, ⊤) (SectionRingComponent L) := section_algebra L
  let : ∀ n, Module k (SectionRingComponent L n) := fun _ ↦ Module.compHom _ c
  exact {
    toFun := (unitSectionsEquiv ⊤).toAddMonoidHom.comp c.toAddMonoidHom
    map_one := by change unitSectionsEquiv ⊤ (c 1) = _; rw [map_one]; rfl
    map_mul := fun a b ↦ by
      change GradedMonoid.mk (A := SectionRingComponent L) 0 (unitSectionsEquiv ⊤ (c (a * b))) = _
      rw [map_mul]
      exact DirectSum.GAlgebra.map_mul (R := Γ(X, ⊤)) (c a) (c b)
    commutes := fun _ _ ↦ mul_comm _ _
    smul_def := fun a x ↦ by
      obtain ⟨n, t⟩ := x
      exact DirectSum.GAlgebra.smul_def (R := Γ(X, ⊤)) (c a) ⟨n, t⟩ }

open CategoryTheory.Limits in
open scoped DirectSum in
private theorem finite_type_of_recurrence
    (k : Type u) [Field k] (A : ℕ → Type u) [∀ n, AddCommGroup (A n)]
    [DirectSum.GCommRing A] [∀ n, Module k (A n)] [DirectSum.GAlgebra k A]
    (hfin : ∀ n, Module.Finite k (A n))
    (r : ℕ) (hr : 0 < r) (ι : Type u) [Fintype ι] (a : ι → A r)
    (M : ℕ) (hrec : ∀ n, M ≤ n → ∀ t : A (r + n),
      ∃ b : ι → A n, t = ∑ l, GradedMonoid.GMul.mul (A := A) (a l) (b l)) :
    Algebra.FiniteType k (⨁ n, A n) := by
  classical
  have gens (n : Fin (r + M)) : ∃ (v : ℕ) (g : Fin v → A n),
      Submodule.span k (Set.range g) = ⊤ := by
    have := hfin n
    exact Module.Finite.exists_fin
  choose v g hg using gens
  let c : (Σ n : Fin (r + M), Fin (v n)) → (⨁ n, A n) :=
    fun j ↦ DirectSum.of A j.1 (g j.1 j.2)
  let d : ι → (⨁ n, A n) := fun l ↦ DirectSum.of A r (a l)
  let T := Algebra.adjoin k (Set.range c ∪ Set.range d)
  have hfg : T.FG := Subalgebra.fg_def.mpr
    ⟨_, (Set.finite_range c).union (Set.finite_range d), rfl⟩
  have hd (l : ι) : d l ∈ T := Algebra.subset_adjoin (Or.inr ⟨l, rfl⟩)
  have hlow (n : Fin (r + M)) (t : A n) : DirectSum.of A n t ∈ T := by
    have ht : t ∈ Submodule.span k (Set.range (g n)) := by rw [hg]; trivial
    induction ht using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨j, rfl⟩ := hx
      exact Algebra.subset_adjoin (Or.inl ⟨⟨n, j⟩, rfl⟩)
    | zero => simp
    | add x y _ _ hx hy => simpa using T.add_mem hx hy
    | smul a x _ hx =>
      rw [DirectSum.of_smul]
      exact T.smul_mem hx a
  have hall (n : ℕ) (t : A n) : DirectSum.of A n t ∈ T := by
    induction n using Nat.strong_induction_on with
    | h n ih =>
      by_cases hn : n < r + M
      · exact hlow ⟨n, hn⟩ t
      have hnr : r ≤ n := by omega
      obtain ⟨b, hb⟩ := hrec (n - r) (by omega)
        (Eq.mp (congrArg A (Nat.add_sub_of_le hnr).symm) t)
      have heq : r + (n - r) = n := Nat.add_sub_of_le hnr
      have hsum : DirectSum.of A (r + (n - r))
          (Eq.mp (congrArg A heq.symm) t) ∈ T := by
        rw [hb, map_sum]
        apply T.sum_mem
        intro l _
        rw [← DirectSum.of_mul_of]
        exact T.mul_mem (hd l) (ih (n - r) (by omega) (b l))
      have hcast : ∀ (q : ℕ) (e : q = n) (t : A n),
          DirectSum.of A q (Eq.mp (congrArg A e.symm) t) = DirectSum.of A n t := by
        intro q e t
        subst q
        rfl
      rwa [hcast _ heq t] at hsum
  have htop : T = ⊤ := by
    apply top_unique
    intro x
    have hx : x ∈ T := by
      induction x using DirectSum.induction_on with
      | zero => exact T.zero_mem
      | of n t => exact hall n t
      | add x y hx hy => exact T.add_mem hx hy
    exact fun _ ↦ hx
  exact ⟨htop ▸ hfg⟩

open CategoryTheory.Limits in
open scoped DirectSum in
private theorem finite_piece
    (k : Type u) [Field k] (X : Scheme.{u}) (f : X ⟶ Spec (CommRingCat.of k))
    [IsHProjective f] (L : X.Modules) [L.IsInvertible] (m : ℕ) :
    @Module.Finite k (SectionRingComponent L m) _ _
      (Module.compHom (SectionRingComponent L m)
        (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom)) := by
  obtain ⟨ι, _, j, _, hj⟩ := IsHProjective.exists_isClosedImmersion (f := f)
  have := IsInvertible.sheafOfModules_isInvertible (L.tensorPow m)
  have := SheafOfModules.IsInvertible.isFiniteLocallyFree.{u, u, u} (L.tensorPow m)
  have := SheafOfModules.IsFiniteLocallyFree.isFinitePresentation.{u, u, u} (L.tensorPow m)
  have h := finite_H_of_isClosedImmersion k j (L.tensorPow m) 0
  rw [hj] at h
  let := moduleHOfSpec f (L.tensorPow m) 0
  let : Module k (SectionRingComponent L m) :=
    Module.compHom _ (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom)
  let e : (L.tensorPow m).H 0 ≃ₗ[k] SectionRingComponent L m :=
    { (H.zeroLinearEquiv (L.tensorPow m)).toAddEquiv with
      map_smul' := fun a t ↦ (H.zeroLinearEquiv (L.tensorPow m)).map_smul _ t }
  exact Module.Finite.equiv e

/-- A projective polarization has a finite-type section algebra, finite-dimensional
homogeneous pieces, affine finite-type fraction charts, and eventually surjective
restriction to every closed subscheme.

The degree-zero equation fixes the algebra map to be the structure map on constants.
The fraction equation fixes the ring equivalence: its value times the restricted
section s^n equals the restricted numerator. On X_s, s generates its line module,
so this is exactly division, also for the empty open and zero localization.

Source: Stacks Project, Tag 0B5T(1),(3),(4), Tags 0C6J and 0EKE
(blueprint: lem-sfb-projective-polarization-section-algebra).

Proof:
Pull back the coordinate sections through the given closed immersion to obtain
an affine nonvanishing cover by sections of L^r. Their evaluation map from a
finite free sheaf onto L^r is epi. Its coherent kernel, tensored with L^n,
has vanishing H^1 for n sufficiently large by Serre vanishing. Consequently
every high-degree section is a sum of products of these coordinate sections
with lower-degree sections. Each degree is finite-dimensional by coherent
cohomology finiteness for projective schemes. Choose finite vector-space
generators in the finitely many low degrees; induction on degree shows that
they and the coordinate sections generate the whole section algebra. The
scalar action is explicitly the structural map into degree zero.

For an arbitrary positive-degree section, raise the coordinate sections and
the given section to a common tensor power. The affine-complement theorem
for universally closed schemes gives affineness of its nonvanishing locus.
The coefficient homomorphism and section-ring localization theorem give the
canonical fraction isomorphism. Noetherianity makes the open quasi-compact,
and its structural morphism is of finite type.

For a closed immersion, the kernel of its pullback adjunction unit on L^m
is the defining ideal tensored with L^m. Serre vanishing kills its H^1 for
large m, and the cohomology exact sequence gives surjectivity on sections.
Uniqueness of left adjoints transports this to the section-normalized unit.
No step assumes reducedness, connectedness, or S_0 = k.
-/
theorem projectivePolarizationSectionAlgebra
    (k : Type u) [Field k] (X : Scheme.{u}) (f : X ⟶ Spec (CommRingCat.of k))
    [IsHProjective f] [LocallyOfFiniteType f] [QuasiCompact f]
    (L : X.Modules) [L.IsInvertible]
    (hpol : ∃ (ι : Type u) (_ : Finite ι)
      (j : X ⟶ ProjectiveSpace ι (Spec (CommRingCat.of k))),
      IsClosedImmersion j ∧
      j ≫ (ProjectiveSpace ι (Spec (CommRingCat.of k))) ↘ Spec (CommRingCat.of k) = f ∧
      ∃ r : ℕ, 0 < r ∧ Nonempty
        ((tensorPullback j).obj (ProjectiveSpace.twist ι (Spec (CommRingCat.of k)) 1) ≅
          L.tensorPow r)) :
    (∃ ρ : k →+* InvertibleSectionRing L,
      (∀ c : k, ρ c = DirectSum.of (SectionRingComponent L) 0
        (unitSectionsEquiv ⊤ (f.appTop ((Scheme.ΓSpecIso (CommRingCat.of k)).inv c)))) ∧
      ρ.FiniteType) ∧
    (∀ m : ℕ, @Module.Finite k (SectionRingComponent L m) _ _
      (Module.compHom (SectionRingComponent L m)
        (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom))) ∧
    (∀ (d : ℕ), 0 < d → ∀ s : sectionRingGrade L d,
      ∃ U : X.Opens,
        (U : Set X) = nonvanishingLocus (L.tensorPow d) (s.val d) ∧
        IsAffineOpen U ∧ LocallyOfFiniteType (U.ι ≫ f) ∧ QuasiCompact (U.ι ≫ f) ∧
        ∃ e : HomogeneousLocalization.Away (sectionRingGrade L) s.val ≃+* Γ(X, U),
          ∀ (n : ℕ) (a : sectionRingGrade L (n • d)),
            e (HomogeneousLocalization.Away.mk (sectionRingGrade L) s.property n
              a.val a.property) •
              (L.tensorPow (n • d)).presheaf.map (homOfLE (le_top : U ≤ ⊤)).op
                ((s.val ^ n) (n • d)) =
            (L.tensorPow (n • d)).presheaf.map (homOfLE (le_top : U ≤ ⊤)).op
              (a.val (n • d))) ∧
    (∀ (Y : Scheme.{u}) (i : Y ⟶ X), IsClosedImmersion i →
      ∃ M : ℕ, ∀ m : ℕ, M ≤ m → Function.Surjective
        (fun t : SectionRingComponent L m ↦
          ((tensorPullbackSectionAdjunction i).unit.app (L.tensorPow m)).app ⊤ t)) := by
  classical
  obtain ⟨ι, hι, j, hj, hjf, r, hr, ⟨ep⟩⟩ := hpol
  let : Finite ι := hι
  let : Fintype ι := Fintype.ofFinite ι
  let : IsClosedImmersion j := hj
  let eb := (tensorPullbackSectionAdjunction j).leftAdjointUniq
    (pullbackPushforwardAdjunction j)
  let e : ProjectiveSpace.twistRestrict j 1 ≅ L.tensorPow r :=
    (eb.app (ProjectiveSpace.twist ι (Spec (.of k)) 1)).symm ≪≫ ep
  have hL : AlgebraicGeometry.IsAmple f L :=
    ⟨inferInstance, r, hr, ι, j, hι, hj, hjf, ⟨e⟩⟩
  have hfinite : ∃ ρ : k →+* InvertibleSectionRing L,
      (∀ c : k, ρ c = DirectSum.of (SectionRingComponent L) 0
        (unitSectionsEquiv ⊤ (f.appTop ((Scheme.ΓSpecIso (CommRingCat.of k)).inv c)))) ∧
      ρ.FiniteType := by
    obtain ⟨a, ha, hcov⟩ := coordinate_cover k ι j (L.tensorPow r) e
    obtain ⟨M, hM⟩ := section_recurrence k X f L hL r ι a ha hcov
    let c : k →+* Γ(X, ⊤) :=
      f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom
    let : ∀ n, Module k (SectionRingComponent L n) := fun _ ↦ Module.compHom _ c
    let : DirectSum.GAlgebra k (SectionRingComponent L) := section_algebra_over L k c
    have hfin : ∀ n, Module.Finite k (SectionRingComponent L n) := finite_piece k X f L
    have hft : Algebra.FiniteType k (InvertibleSectionRing L) :=
      finite_type_of_recurrence k (SectionRingComponent L) hfin r hr ι
        (fun l ↦ (a l).app ⊤ (unitSectionsEquiv ⊤ 1)) M hM
    exact ⟨algebraMap k (InvertibleSectionRing L), fun _ ↦ rfl,
      RingHom.finiteType_algebraMap.mpr hft⟩
  have hrestriction (Y : Scheme.{u}) (i : Y ⟶ X) (hi : IsClosedImmersion i) :
      ∃ M : ℕ, ∀ m : ℕ, M ≤ m → Function.Surjective
        (fun t : SectionRingComponent L m ↦
          ((tensorPullbackSectionAdjunction i).unit.app (L.tensorPow m)).app ⊤ t) := by
    let : IsClosedImmersion i := hi
    exact restriction_surjective k X f L hL Y i (tensorPullbackSectionAdjunction i)
  exact ⟨hfinite, finite_piece k X f L, fraction_chart k X f ι j L r hr e, hrestriction⟩

end AlgebraicGeometry.Scheme.Modules
