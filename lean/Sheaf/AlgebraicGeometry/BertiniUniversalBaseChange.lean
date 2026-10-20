/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF groups Q107 and C8
-/
module

public import Sheaf.AlgebraicGeometry.BertiniUniversalFamily
import WeilConjectures.AlgebraicGeometry.Modules.PullbackFreeGenerator
import WeilConjectures.AlgebraicGeometry.Modules.HomSection
import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

/-!
# Base change of the universal linear-system zero scheme

Source: Stacks Project, Varieties, Situation 0G47 and its universal divisor.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory

namespace AlgebraicGeometry

noncomputable section

open Scheme.Modules

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

/-- Pulling back the universal zero scheme substitutes the pulled-back coordinates
and pulls back the original sections by the canonical tensor-pullback unit.

Source: Stacks Project, Varieties, Situation 0G47, definition of the universal divisor;
Divisors, definition-zero-scheme-s and lemma-zero-scheme.
(blueprint: lem-zl-bertini-universal-base-change).

Proof: The canonical tensor pullback is uniquely isomorphic, compatibly with its unit,
to the existing module pullback. The zero scheme commutes with the latter pullback.
Composition of adjunctions identifies the iterated units with the unit of the composite.
The unit is additive and semilinear, so it sends the universal sum to the displayed sum.
Transport through these module isomorphisms does not change a zero scheme. -/
theorem bertiniUniversalIdeal_comap
    {k : Type u} [Field k] {Y X : Scheme.{u}}
    (f : Y ⟶ Spec (CommRingCat.of k)) (L : Y.Modules) [L.IsInvertible]
    {I : Type u} [Fintype I] (s : I → Γ(L, ⊤))
    (g : X ⟶ pullback
      (Spec.map (CommRingCat.ofHom (MvPolynomial.C : k →+* MvPolynomial I k))) f) :
    (bertiniUniversalIdeal f L s).comap g =
      (homOfGlobalSection _ (∑ i,
        (g ≫ pullback.fst
          (Spec.map (CommRingCat.ofHom (MvPolynomial.C : k →+* MvPolynomial I k))) f).appTop
          ((Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial I k))).inv (MvPolynomial.X i)) •
        tensorSectionsUnit (g ≫ pullback.snd
          (Spec.map (CommRingCat.ofHom (MvPolynomial.C : k →+* MvPolynomial I k))) f)
          L (s i))).zeroLocus := by
  apply zeroLocus_sum_triangle g _ _ rfl L s
  intro i
  rfl

end

end AlgebraicGeometry
