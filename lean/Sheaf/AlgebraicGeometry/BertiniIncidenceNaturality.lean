/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.BertiniUniversalFamily
import Sheaf.AlgebraicGeometry.BertiniUniversalBaseChange
import WeilConjectures.AlgebraicGeometry.Modules.PullbackFreeGenerator
import WeilConjectures.AlgebraicGeometry.Modules.HomSection
import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

/-! Base change of the Bertini incidence construction. -/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
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

private theorem tensorUnit_comparisonGlobal {X Y : Scheme.{u}} (f : X ⟶ Y)
    (L : Y.Modules) (s : Γ(L, ⊤)) :
    ((tensorComparison f).hom.app L).app ⊤ (tensorSectionsUnit f L s) =
      ((Scheme.Modules.pullback f).obj L).presheaf.map
        (homOfLE f.preimage_top.ge).op (pullbackSection f s) := by
  unfold tensorSectionsUnit
  change ((tensorComparison f).hom.app L).app ⊤
    (((tensorPullback f).obj L).presheaf.map (homOfLE f.preimage_top.ge).op
      (((Classical.choose (exists_tensorPullbackAdjunction f)).unit.app L).app ⊤ s)) = _
  rw [Hom.app_presheaf_map]
  congr 1
  exact congrArg (fun t ↦ t.app ⊤ s)
    ((Classical.choose (exists_tensorPullbackAdjunction f)).unit_leftAdjointUniq_hom_app
      (pullbackPushforwardAdjunction f) L)

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


/-- The tensor-pullback unit is semilinear on global sections.
Source: Stacks Project, Tag 01CR (blueprint: lem-zl-bertini-incidence-naturality). -/
theorem bertiniTensorSectionsUnit_smul {X Y : Scheme.{u}} (f : X ⟶ Y)
    (L : Y.Modules) (r : Γ(Y, ⊤)) (s : Γ(L, ⊤)) :
    tensorSectionsUnit f L (r • s) = f.appTop r • tensorSectionsUnit f L s :=
  tensorUnit_smul f L r s

/-- Tensor pullback preserves invertible modules, via uniqueness of the left adjoint.
Source: Stacks Project, Tag 01CR (blueprint: lem-zl-bertini-incidence-naturality). -/
theorem bertiniTensorPullback_invertible {X Y : Scheme.{u}} (f : X ⟶ Y)
    (L : Y.Modules) [L.IsInvertible] : ((tensorPullback f).obj L).IsInvertible :=
  IsInvertible.of_iso ((tensorComparison f).app L).symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- A section relation on an open containing the image pulls back to a global relation.
Source: Stacks Project, Tag 01CR (blueprint: lem-zl-bertini-incidence-naturality). -/
theorem bertiniTensorSectionsUnit_local_smul
    {X Y : Scheme.{u}} (f : X ⟶ Y) (L : Y.Modules) {U : Y.Opens}
    (hU : ⊤ ≤ f ⁻¹ᵁ U) (s t : Γ(L, ⊤)) (c : Γ(Y, U))
    (h : L.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op s =
      c • L.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op t) :
    tensorSectionsUnit f L s = f.appLE U ⊤ hU c • tensorSectionsUnit f L t := by
  let E := (tensorComparison f).app L
  apply (ConcreteCategory.bijective_of_isIso (E.hom.app ⊤)).injective
  rw [Hom.app_smul]
  dsimp only [E]
  simp only [Iso.app_hom]
  rw [tensorUnit_comparisonGlobal, tensorUnit_comparisonGlobal]
  have hh := congrArg (fun z ↦ ((Scheme.Modules.pullback f).obj L).presheaf.map
    (homOfLE hU).op (pullbackSection f z)) h
  rw [pullbackSection_smul, map_smul, pullbackSection_map, pullbackSection_map] at hh
  simp only [presheaf_map_map_apply] at hh
  exact hh

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- A free generator on an open containing the image pulls back to a global free generator.
Source: Stacks Project, Tag 01CR (blueprint: lem-zl-bertini-incidence-naturality). -/
theorem bertiniTensorSectionsUnit_freeGenerator
    {X Y : Scheme.{u}} (f : X ⟶ Y) (L : Y.Modules) {U : Y.Opens}
    (hU : ⊤ ≤ f ⁻¹ᵁ U) (s : Γ(L, ⊤))
    (hs : IsFreeGenerator (L.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op s)) :
    IsFreeGenerator (tensorSectionsUnit f L s) := by
  let E := (tensorComparison f).app L
  have hp := (hs.pullback_unit_app f).map hU
  change IsFreeGenerator (((Scheme.Modules.pullback f).obj L).presheaf.map
    (homOfLE hU).op (pullbackSection f
      (L.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op s))) at hp
  rw [pullbackSection_map] at hp
  simp only [presheaf_map_map_apply] at hp
  have hq := hp.app_hom E.symm
  change IsFreeGenerator (E.inv.app ⊤
    (((Scheme.Modules.pullback f).obj L).presheaf.map
      (homOfLE f.preimage_top.ge).op (pullbackSection f s))) at hq
  rw [← tensorUnit_comparisonGlobal f L s] at hq
  change IsFreeGenerator (E.inv.app ⊤ (E.hom.app ⊤ (tensorSectionsUnit f L s))) at hq
  rw [← ConcreteCategory.comp_apply, ← Hom.comp_app, Iso.hom_inv_id, Hom.id_app] at hq
  exact hq

/-- A local trivialization pulls back to a global trivialization when its open contains
all of the image, with the expected coefficient formula.
Source: Stacks Project, Tag 01CR (blueprint: lem-zl-bertini-incidence-naturality).

Proof: Pull back the local generator by the adjunction unit and restrict to the whole
source. The unit's semilinearity carries its coefficient identities to the source.
The tensor-pullback comparison preserves these identities and the free-generator property. -/
theorem exists_bertiniTensorLocalGenerator
    {X Y : Scheme.{u}} (f : X ⟶ Y) (L : Y.Modules) {U : Y.Opens}
    (hU : ⊤ ≤ f ⁻¹ᵁ U) {e : Γ(L, U)} (he : IsFreeGenerator e) :
    ∃ (e' : Γ((tensorPullback f).obj L, ⊤)) (he' : IsFreeGenerator e'),
      ∀ s : Γ(L, ⊤), he'.coeff (tensorSectionsUnit f L s) =
        f.appLE U ⊤ hU (he.coeff (L.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op s)) := by
  let E := (tensorComparison f).app L
  let e₀ := ((Scheme.Modules.pullback f).obj L).presheaf.map
    (homOfLE hU).op (pullbackSection f e)
  let e' := E.inv.app ⊤ e₀
  have he' : IsFreeGenerator e' := ((he.pullback_unit_app f).map hU).app_hom E.symm
  refine ⟨e', he', fun s ↦ (he'.coeff_eq_iff _ _).mpr ?_⟩
  apply (ConcreteCategory.bijective_of_isIso (E.hom.app ⊤)).injective
  rw [Hom.app_smul]
  have hcancel : E.hom.app ⊤ e' = e₀ := by
    dsimp only [e']
    rw [← ConcreteCategory.comp_apply, ← Hom.comp_app, Iso.inv_hom_id, Hom.id_app]
    rfl
  rw [hcancel]
  change _ = ((tensorComparison f).hom.app L).app ⊤ (tensorSectionsUnit f L s)
  rw [tensorUnit_comparisonGlobal]
  have hh := congrArg (fun z ↦ ((Scheme.Modules.pullback f).obj L).presheaf.map
    (homOfLE hU).op (pullbackSection f z))
    (he.coeff_smul (L.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op s))
  rw [pullbackSection_smul, map_smul, pullbackSection_map] at hh
  simp only [presheaf_map_map_apply] at hh
  exact hh

/-- The ambient map induced by base change on the source scheme.
Source: Stacks Project, Tag 0FD3 (blueprint: lem-zl-bertini-incidence-naturality). -/
def bertiniAmbientBaseChange {k : Type u} [Field k] {Y X : Scheme.{u}}
    (f : Y ⟶ Spec (.of k)) (u : X ⟶ Y) (I : Type u) :
    pullback (Spec.map (CommRingCat.ofHom (MvPolynomial.C : k →+* MvPolynomial I k)))
      (u ≫ f) ⟶
    pullback (Spec.map (CommRingCat.ofHom (MvPolynomial.C : k →+* MvPolynomial I k))) f :=
  pullback.map _ _ _ _ (𝟙 _) u (𝟙 _) (by simp) (by simp)

/-- Formation of the incidence ideal commutes with base change on its source.
Source: Stacks Project, Tag 0FD3 (blueprint: lem-zl-bertini-incidence-naturality).

Proof: Pull back the universal section. The adjunction composition comparison identifies
its summands with the corresponding summands for the pulled-back sections, and a module
isomorphism preserves the zero ideal. -/
theorem bertiniUniversalIdeal_baseChange
    {k : Type u} [Field k] {Y X : Scheme.{u}} (f : Y ⟶ Spec (.of k))
    (u : X ⟶ Y) (L : Y.Modules) [L.IsInvertible]
    {I : Type u} [Fintype I] (s : I → Γ(L, ⊤)) :
    (bertiniUniversalIdeal f L s).comap (bertiniAmbientBaseChange f u I) =
      bertiniUniversalIdeal (u ≫ f) ((tensorPullback u).obj L)
        (fun i ↦ tensorSectionsUnit u L (s i)) := by
  classical
  rw [bertiniUniversalIdeal_comap]
  let a := pullback.snd
    (Spec.map (CommRingCat.ofHom (MvPolynomial.C : k →+* MvPolynomial I k))) (u ≫ f)
  have hfst : bertiniAmbientBaseChange f u I ≫ pullback.fst _ _ =
      pullback.fst _ (u ≫ f) := by
    simp [bertiniAmbientBaseChange, pullback.map]
  have hsnd : bertiniAmbientBaseChange f u I ≫ pullback.snd _ _ = a ≫ u := by
    simp [bertiniAmbientBaseChange, pullback.map, a]
  rw [hfst, hsnd]
  let E := (tensorSectionsComp a u).app L
  have he := zeroLocus_section_iso E
    (bertiniUniversalSection (u ≫ f) ((tensorPullback u).obj L)
      (fun i ↦ tensorSectionsUnit u L (s i)))
  dsimp only [bertiniUniversalSection] at he
  have hsec : E.hom.app ⊤
      (bertiniUniversalSection (u ≫ f) ((tensorPullback u).obj L)
        (fun i ↦ tensorSectionsUnit u L (s i))) =
      ∑ i, (pullback.fst
        (Spec.map (CommRingCat.ofHom (MvPolynomial.C : k →+* MvPolynomial I k)))
          (u ≫ f)).appTop
            ((Scheme.ΓSpecIso (.of (MvPolynomial I k))).inv (MvPolynomial.X i)) •
        tensorSectionsUnit (a ≫ u) L (s i) := by
    dsimp only [bertiniUniversalSection]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Hom.app_smul]
    congr 1
    exact tensorUnit_comp a u L (s i)
  dsimp only [bertiniUniversalSection] at hsec
  rw [hsec] at he
  exact he

/-- The ambient source square is cartesian.
Source: Stacks Project, Tag 0FD3 (blueprint: lem-zl-bertini-incidence-naturality). -/
theorem isPullback_bertiniAmbientBaseChange
    {k : Type u} [Field k] {Y X : Scheme.{u}}
    (f : Y ⟶ Spec (.of k)) (u : X ⟶ Y) (I : Type u) :
    IsPullback (bertiniAmbientBaseChange f u I) (pullback.snd _ (u ≫ f))
      (pullback.snd _ f) u := by
  let φ := Spec.map (CommRingCat.ofHom (MvPolynomial.C : k →+* MvPolynomial I k))
  have hout : IsPullback
      (bertiniAmbientBaseChange f u I ≫ pullback.fst φ f)
      (pullback.snd φ (u ≫ f)) φ (u ≫ f) := by
    dsimp only [φ]
    simp only [bertiniAmbientBaseChange, pullback.map, pullback.lift_fst, Category.comp_id]
    exact IsPullback.of_hasPullback _ _
  exact hout.of_right (by simp [bertiniAmbientBaseChange, pullback.map, φ])
    (IsPullback.of_hasPullback φ f)

/-- The map of incidence schemes induced by base change on the source.
Source: Stacks Project, Tag 0FD3 (blueprint: lem-zl-bertini-incidence-naturality). -/
def bertiniIncidenceBaseChange
    {k : Type u} [Field k] {Y X : Scheme.{u}} (f : Y ⟶ Spec (.of k))
    (u : X ⟶ Y) (L : Y.Modules) [L.IsInvertible]
    {I : Type u} [Fintype I] (s : I → Γ(L, ⊤)) :
    (bertiniUniversalIdeal (u ≫ f) ((tensorPullback u).obj L)
      (fun i ↦ tensorSectionsUnit u L (s i))).subscheme ⟶
      (bertiniUniversalIdeal f L s).subscheme :=
  Scheme.IdealSheafData.subschemeMap _ _ (bertiniAmbientBaseChange f u I)
    (Scheme.IdealSheafData.le_map_iff_comap_le.mpr
      (bertiniUniversalIdeal_baseChange f u L s).le)

/-- Source base change preserves the projection to coefficient affine space.
Source: Stacks Project, Tag 0FD3 (blueprint: lem-zl-bertini-incidence-naturality). -/
theorem bertiniIncidenceBaseChange_projection
    {k : Type u} [Field k] {Y X : Scheme.{u}} (f : Y ⟶ Spec (.of k))
    (u : X ⟶ Y) (L : Y.Modules) [L.IsInvertible]
    {I : Type u} [Fintype I] (s : I → Γ(L, ⊤)) :
    bertiniIncidenceBaseChange f u L s ≫ bertiniUniversalProjection f L s =
      bertiniUniversalProjection (u ≫ f) ((tensorPullback u).obj L)
        (fun i ↦ tensorSectionsUnit u L (s i)) := by
  dsimp only [bertiniUniversalProjection]
  rw [← Category.assoc]
  simp only [bertiniIncidenceBaseChange,
    Scheme.IdealSheafData.subschemeMap_subschemeι, Category.assoc]
  congr 1
  simp [bertiniAmbientBaseChange, pullback.map]

/-- The incidence source square is cartesian.
Source: Stacks Project, Tag 0FD3 (blueprint: lem-zl-bertini-incidence-naturality).

Proof: The equality of the pulled-back ideal gives the first cartesian square of closed
subschemes. Paste it with the ambient cartesian square. -/
theorem isPullback_bertiniIncidenceBaseChange
    {k : Type u} [Field k] {Y X : Scheme.{u}} (f : Y ⟶ Spec (.of k))
    (u : X ⟶ Y) (L : Y.Modules) [L.IsInvertible]
    {I : Type u} [Fintype I] (s : I → Γ(L, ⊤)) :
    IsPullback (bertiniIncidenceBaseChange f u L s)
      ((bertiniUniversalIdeal (u ≫ f) ((tensorPullback u).obj L)
        (fun i ↦ tensorSectionsUnit u L (s i))).subschemeι ≫ pullback.snd _ _)
      ((bertiniUniversalIdeal f L s).subschemeι ≫ pullback.snd _ _) u := by
  have h := isPullback_of_isClosedImmersion
    (bertiniUniversalIdeal (u ≫ f) ((tensorPullback u).obj L)
      (fun i ↦ tensorSectionsUnit u L (s i))).subschemeι
    (bertiniUniversalIdeal f L s).subschemeι
    (bertiniIncidenceBaseChange f u L s) (bertiniAmbientBaseChange f u I)
    (by simp [bertiniIncidenceBaseChange]) (by
      simp only [Scheme.IdealSheafData.ker_subschemeι]
      exact bertiniUniversalIdeal_baseChange f u L s)
  exact h.flip.paste_vert (isPullback_bertiniAmbientBaseChange f u I)

end
end AlgebraicGeometry
