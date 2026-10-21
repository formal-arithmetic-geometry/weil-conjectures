/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M5
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.LinearAlgebra.Basis.Defs
public import Sheaf.AlgebraicGeometry.PureDimension
public import WeilConjectures.AlgebraicGeometry.Modules.ZeroLocus
public import WeilConjectures.AlgebraicGeometry.EtaleTensorSections
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction

import WeilConjectures.AlgebraicGeometry.GeneratingSectionsStalkSpan
import WeilConjectures.AlgebraicGeometry.InvertibleStalkLinearEquiv
import WeilConjectures.AlgebraicGeometry.SectionNonvanishingZeroLocus
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import WeilConjectures.RingTheory.FiniteTypeDomainDimensionLocalRingLocalization
import WeilConjectures.AlgebraicGeometry.Regular
import WeilConjectures.AlgebraicGeometry.Modules.HomSection
import WeilConjectures.AlgebraicGeometry.Modules.PullbackFreeGenerator
import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.RingTheory.LocalRing.Module

/-! # BertiniFiniteCoverBaseCodimension

Source: blueprint paragraph 3 of the finite-cover Bertini argument
(blueprint: lem-zl-bertini-finite-cover-base-codimension).
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

namespace AlgebraicGeometry

open Scheme.Modules Opposite MonoidalCategory

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


private theorem generating_nonvanishing {Y : Scheme.{u}} (M : Y.Modules)
    [M.IsInvertible] {I : Type u} [Finite I] (s : I → Γ(M, ⊤))
    (hgen : Epi (M.freeHomEquiv.symm (fun i ↦
      SheafOfModules.unitHomEquiv _ (homOfGlobalSection M (s i))))) :
    ∀ y : Y, ∃ i, y ∈ nonvanishingLocus M (s i) := by
  intro y
  obtain ⟨e⟩ := invertible_stalk_linearEquiv Y M y
  have hspan := (generating_sections_iff_stalk_span Y M _).mp hgen y
  have hfamily (i : I) :
      (SheafOfModules.unitHomEquiv _ (homOfGlobalSection M (s i))).val (op ⊤) = s i := by
    exact (homOfGlobalSection_app_one M (s i) ⊤).trans (presheaf_map_id_apply _ _)
  simp only [hfamily] at hspan
  by_contra! hn
  let P : Submodule (Y.presheaf.stalk y) ↑(TopCat.Presheaf.stalk M.val.presheaf y) :=
    (IsLocalRing.maximalIdeal (Y.presheaf.stalk y)) • ⊤
  have hle : Submodule.span (Y.presheaf.stalk y)
      (Set.range fun i ↦ TopCat.Presheaf.germ M.val.presheaf ⊤ y trivial (s i)) ≤ P := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact not_not.mp (hn i)
  have hm : P.map e.toLinearMap = IsLocalRing.maximalIdeal (Y.presheaf.stalk y) := by
    simp only [P, Submodule.map_smul'', Submodule.map_top, LinearEquiv.range,
      Ideal.smul_eq_mul, Ideal.mul_top]
  have h1 : (1 : Y.presheaf.stalk y) ∈ IsLocalRing.maximalIdeal (Y.presheaf.stalk y) := by
    rw [← hm]
    exact ⟨e.symm 1, hle (hspan ▸ Submodule.mem_top), e.apply_symm_apply 1⟩
  exact (IsLocalRing.maximalIdeal.isMaximal (Y.presheaf.stalk y)).ne_top
    (Ideal.eq_top_of_isUnit_mem _ h1 isUnit_one)

private theorem closedPoint_coheight
    {k : Type u} [Field k] (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [IsAffine X] [ConnectedSpace X] [Smooth (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))]
    (d : ℕ) (hdim : X.IsPureDimension d) {x : X} (hx : IsClosed ({x} : Set X)) :
    Order.coheight x = d := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian
    (X ↘ Spec (.of k))
  have : IsRegular X := IsRegular.of_smooth (X ↘ Spec (.of k))
  have : IsIntegral X := IsRegular.isIntegral X
  have hXdim : topologicalKrullDim X = (d : WithBot ℕ∞) := by
    have h := hdim Set.univ (by simp [irreducibleComponents_eq_singleton])
    rwa [(Homeomorph.Set.univ X).isHomeomorph.topologicalKrullDim_eq] at h
  let A : CommRingCat.{u} := Γ(X, ⊤)
  let e : X ≅ Spec A := X.isoSpec
  let y : Spec A := e.hom x
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (e.inv ≫ (X ↘ Spec (.of k)))
  have hft : LocallyOfFiniteType (Spec.map φ) := hφ ▸ inferInstance
  let : Algebra k A := φ.hom.toAlgebra
  have : Algebra.FiniteType k A := HasRingHomProperty.Spec_iff.mp hft
  have : IsDomain A := inferInstance
  have hAdim : ringKrullDim A = (d : WithBot ℕ∞) := by
    rw [← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
    exact e.hom.homeomorph.isHomeomorph.topologicalKrullDim_eq.symm.trans hXdim
  have hy : IsClosed ({y} : Set (Spec A)) := by
    simpa only [Set.image_singleton] using e.hom.isClosedEmbedding.isClosedMap _ hx
  have : y.asIdeal.IsMaximal := (PrimeSpectrum.isClosed_singleton_iff_isMaximal _).mp hy
  have hloc := finiteTypeDomain_ringKrullDim_localizationAtMaximal_localization
    (k := k) (S := A) y.asIdeal
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height y.asIdeal
    (Localization.AtPrime y.asIdeal), idealHeight_eq_coheight, hAdim] at hloc
  have hco : Order.coheight y = d := by exact_mod_cast hloc
  rw [← coheight_eq_of_isOpenImmersion e.hom]
  exact hco

/-- Every component of the pulled-back base locus has codimension equal to dim X.

Source: main-20261015, `lem-zl-bertini-finite-cover-curve.proof.md`, paragraph 3;
Stacks Project, Tag 0G4F, condition (4).
(blueprint: lem-zl-bertini-finite-cover-base-codimension).

Proof: generation on U₀ implies that the common zero support on X is contained
in S. Zero schemes commute with tensor pullback, so the common zero support on T
is contained in π⁻¹(S). Let t be the generic point of any base component. Its image
x belongs to S and is therefore closed. Smooth connected X is integral, and its
pure dimension d equals the dimension of its affine coordinate domain. The finite
type domain dimension theorem gives coheight x = d. An etale morphism preserves
coheight, so coheight t = d. The point/irreducible-closed-set order isomorphism
identifies coheight t with the component's coheight, proving equality with d. -/
theorem bertini_finiteCover_base_codimension
    (k : Type u) [Field k]
    (X : Scheme.{u}) [X.Over (Spec (.of k))] [IsAffine X] [ConnectedSpace X]
    [Smooth (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))]
    (d : ℕ) (hdim : X.IsPureDimension d)
    (T : Scheme.{u}) (π : T ⟶ X) [Etale π]
    (S : Finset X) (hclosed : ∀ x ∈ S, IsClosed ({x} : Set X))
    (U₀ : X.Opens) (hU₀ : (U₀ : Set X) = (S : Set X)ᶜ)
    (L : X.Modules) [L.IsInvertible]
    (V : Type v) [AddCommGroup V] [Module k V]
    (r : ℕ) (b : Module.Basis (Fin r) k V) (ψ : V →+ Γ(L, ⊤))
    (hgen : Epi (((Scheme.Modules.tensorPullback U₀.ι).obj L).freeHomEquiv.symm
      (fun i : ULift.{u} (Fin r) ↦ SheafOfModules.unitHomEquiv _
        (Scheme.Modules.homOfGlobalSection _
          (Scheme.Modules.tensorSectionsUnit U₀.ι L (ψ (b i.down)))))))
 :
    letI : ((Scheme.Modules.tensorPullback π).obj L).IsInvertible :=
      Scheme.Modules.IsInvertible.of_iso
        (((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction π)).leftAdjointUniq
          (Scheme.Modules.pullbackPushforwardAdjunction π)).app L).symm
    ∀ B : TopologicalSpace.IrreducibleCloseds T,
      Maximal (fun Z : TopologicalSpace.IrreducibleCloseds T ↦
        (Z : Set T) ⊆ ⋂ w : V,
          ((Scheme.Modules.homOfGlobalSection ((Scheme.Modules.tensorPullback π).obj L)
            (Scheme.Modules.tensorSectionsUnit π L (ψ w))).zeroLocus.support : Set T)) B →
      Order.coheight B = d := by
  classical
  dsimp only
  let LT := (tensorPullback π).obj L
  have : LT.IsInvertible := IsInvertible.of_iso ((tensorComparison π).app L).symm
  have hsupport (w : V) :
      ((homOfGlobalSection LT (tensorSectionsUnit π L (ψ w))).zeroLocus.support : Set T) =
        π ⁻¹' ((homOfGlobalSection L (ψ w)).zeroLocus.support : Set X) := by
    rw [← zeroLocus_tensorUnit, Scheme.IdealSheafData.coe_support_comap]
  have hbase : (⋂ w : V,
      ((homOfGlobalSection LT (tensorSectionsUnit π L (ψ w))).zeroLocus.support : Set T)) ⊆
        π ⁻¹' (S : Set X) := by
    intro t ht
    by_contra hnot
    have hxU : π t ∈ U₀ := by rw [← SetLike.mem_coe, hU₀]; exact hnot
    let y : U₀.toScheme := ⟨π t, hxU⟩
    let LU := (tensorPullback U₀.ι).obj L
    have : LU.IsInvertible := IsInvertible.of_iso ((tensorComparison U₀.ι).app L).symm
    obtain ⟨i, hi⟩ := generating_nonvanishing LU
      (fun i : ULift.{u} (Fin r) ↦ tensorSectionsUnit U₀.ι L (ψ (b i.down))) hgen y
    rw [nonvanishingLocus_eq_compl_support_zeroLocus] at hi
    have hzero := Set.mem_iInter.mp ht (b i.down)
    rw [hsupport] at hzero
    have hzerou : y ∈
        (homOfGlobalSection LU (tensorSectionsUnit U₀.ι L (ψ (b i.down)))).zeroLocus.support := by
      rw [← zeroLocus_tensorUnit, Scheme.IdealSheafData.support_comap]
      exact hzero
    exact hi hzerou
  intro B hB
  let t : T := irreducibleSetEquivPoints B
  have htB : t ∈ (B : Set T) := (B.2.isGenericPoint_genericPoint B.3).mem
  have hxS : π t ∈ S := hbase (hB.1 htB)
  have hco := closedPoint_coheight (k := k) X d hdim (hclosed (π t) hxS)
  rw [π.coheight_apply_of_flat] at hco
  have hBt : Order.coheight B = Order.coheight t := (Order.coheight_orderIso
    irreducibleSetEquivPoints B).symm
  exact hBt.trans hco

end

end AlgebraicGeometry
