/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group O4
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.LinearAlgebra.Basis.Defs
public import Sheaf.AlgebraicGeometry.PureDimension
public import Sheaf.AlgebraicGeometry.ProjectiveSpaceHomOfGeneratingSections
public import WeilConjectures.AlgebraicGeometry.Modules.ZeroLocus
public import WeilConjectures.AlgebraicGeometry.EtaleTensorSections
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions

import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Connected
import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Irreducible
import Sheaf.AlgebraicGeometry.BertiniFiniteCoverBaseCodimension
import Sheaf.AlgebraicGeometry.BertiniFiniteCoverTransverseComponent
import Sheaf.AlgebraicGeometry.BertiniIrreducibleMember
import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
import WeilConjectures.AlgebraicGeometry.Regular
import WeilConjectures.AlgebraicGeometry.Modules.HomSection
import WeilConjectures.AlgebraicGeometry.Modules.PullbackFreeGenerator
import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

/-! # Simultaneous irreducibility on a finite étale cover

Source: main-20261015 blueprint, proof of `lem-zl-bertini-finite-cover-curve`, paragraph 3;
Stacks Project, Tag 0G4F (blueprint: lem-zl-bertini-finite-cover-irreducible-system).
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

namespace AlgebraicGeometry

open Scheme.Modules Opposite MonoidalCategory

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

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


private theorem memberIdeal_eq_comap
    {k : Type u} [Field k] {Y : Scheme.{u}} [Y.Over (Spec (.of k))]
    (L : Y.Modules) [L.IsInvertible]
    {V : Type v} [AddCommGroup V] [Module k V]
    (r : ℕ) (b : Module.Basis (Fin r) k V) (ψ : V →+ Γ(L, ⊤))
    (hlinear : ∀ (c : k) (v : V),
      ψ (c • v) = (Y ↘ Spec (.of k)).appTop ((Scheme.ΓSpecIso (.of k)).inv c) • ψ v)
    (v : V) :
    linearSystemMemberIdeal (Y ↘ Spec (.of k)) L (fun i ↦ ψ (b i)) k (b.repr v) =
      (homOfGlobalSection L (ψ v)).zeroLocus.comap
        (pullback.fst (Y ↘ Spec (.of k))
          (Spec.map (CommRingCat.ofHom (algebraMap k k)))) := by
  unfold linearSystemMemberIdeal
  rw [zeroLocus_tensorUnit]
  congr 1
  congr 1
  have heq : ψ v = ∑ i : Fin r,
      (Y ↘ Spec (.of k)).appTop ((Scheme.ΓSpecIso (.of k)).inv (b.repr v i)) • ψ (b i) := by
    conv_lhs => rw [← b.sum_repr v, map_sum]
    exact Finset.sum_congr rfl (fun i _ ↦ hlinear _ _)
  rw [heq, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [tensorUnit_smul]
  congr 1
  · have h := congrArg (fun q : pullback (Y ↘ Spec (.of k))
        (Spec.map (CommRingCat.ofHom (algebraMap k k))) ⟶ Spec (.of k) ↦
          q.appTop ((Scheme.ΓSpecIso (.of k)).inv (b.repr v i)))
      (pullback.condition (f := Y ↘ Spec (.of k))
        (g := Spec.map (CommRingCat.ofHom (algebraMap k k))))
    have hi : (Spec.map (CommRingCat.ofHom (algebraMap k k))).appTop
        ((Scheme.ΓSpecIso (.of k)).inv (b.repr v i)) =
        (Scheme.ΓSpecIso (.of k)).inv (b.repr v i) := by
      rw [show Spec.map (CommRingCat.ofHom (algebraMap k k)) = 𝟙 _ from
        Scheme.Spec.map_id _, Scheme.Hom.id_appTop]
      rfl
    simp only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply] at h
    rw [hi] at h
    exact h.symm
  · simp only [tensorUnit_eq, id_eq]; rfl

private theorem geometric_member_of_bertini
    {k : Type u} [Field k] {Y : Scheme.{u}} [Y.Over (Spec (.of k))]
    (L : Y.Modules) [L.IsInvertible]
    {V : Type v} [AddCommGroup V] [Module k V]
    (r : ℕ) (b : Module.Basis (Fin r) k V) (ψ : V →+ Γ(L, ⊤))
    (hlinear : ∀ (c : k) (v : V),
      ψ (c • v) = (Y ↘ Spec (.of k)).appTop ((Scheme.ΓSpecIso (.of k)).inv c) • ψ v)
    (v : V)
    (h : GeometricallyIrreducible
      ((linearSystemMemberIdeal (Y ↘ Spec (.of k)) L (fun i ↦ ψ (b i)) k
        (b.repr v)).subschemeι ≫
        pullback.snd (Y ↘ Spec (.of k))
          (Spec.map (CommRingCat.ofHom (algebraMap k k))))) :
    GeometricallyIrreducible ((homOfGlobalSection L (ψ v)).zeroLocus.subschemeι ≫
      (Y ↘ Spec (.of k))) := by
  rw [memberIdeal_eq_comap L r b ψ hlinear v] at h
  let J := (homOfGlobalSection L (ψ v)).zeroLocus
  let f := Y ↘ Spec (.of k)
  let g := Spec.map (CommRingCat.ofHom (algebraMap k k))
  have hg : g = 𝟙 _ := by
    exact Scheme.Spec.map_id _
  have : IsIso g := hg ▸ inferInstance
  let p := pullback.fst f g
  let e := (J.comapIso p) ≪≫ asIso (pullback.snd p J.subschemeι)
  have he' : e.hom ≫ J.subschemeι = (J.comap p).subschemeι ≫ p := by
    change ((J.comapIso p).hom ≫ pullback.snd p J.subschemeι) ≫ J.subschemeι = _
    rw [Category.assoc, ← pullback.condition, ← Category.assoc, J.comapIso_hom_fst]
  have hright : pullback.snd f g ≫ g = pullback.snd f g :=
    (congrArg (fun q ↦ pullback.snd f g ≫ q) hg).trans (Category.comp_id _)
  have he : e.hom ≫ J.subschemeι ≫ f =
      (J.comap p).subschemeι ≫ pullback.snd f g := by
    rw [← Category.assoc, he', Category.assoc]
    have hp : p ≫ f = pullback.snd f g :=
      (pullback.condition (f := f) (g := g)).trans hright
    rw [hp]
  rw [← he] at h
  exact (MorphismProperty.cancel_left_of_respectsIso
    (P := @GeometricallyIrreducible) e.hom _).mp h

private theorem exists_open_on_finiteCover
    (k : Type u) [Field k] [IsAlgClosed k]
    (X : Scheme.{u}) [X.Over (Spec (.of k))] [IsAffine X] [ConnectedSpace X]
    [Smooth (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))]
    (d : ℕ) (hd : 2 ≤ d) (hdim : X.IsPureDimension d)
    (T : Scheme.{u}) [ConnectedSpace T] (π : T ⟶ X) [IsFinite π] [Etale π]
    (S : Finset X) (hclosed : ∀ x ∈ S, IsClosed ({x} : Set X))
    (U₀ : X.Opens) (hU₀ : (U₀ : Set X) = (S : Set X)ᶜ)
    (L : X.Modules) [L.IsInvertible]
    (V : Type v) [AddCommGroup V] [Module k V]
    (r : ℕ) (b : Module.Basis (Fin r) k V) (ψ : V →+ Γ(L, ⊤))
    (hlinear : ∀ (c : k) (v : V),
      ψ (c • v) = (X ↘ Spec (.of k)).appTop ((Scheme.ΓSpecIso (.of k)).inv c) • ψ v)
    (hgen : Epi (((Scheme.Modules.tensorPullback U₀.ι).obj L).freeHomEquiv.symm
      (fun i : ULift.{u} (Fin r) ↦ SheafOfModules.unitHomEquiv _
        (Scheme.Modules.homOfGlobalSection _
          (Scheme.Modules.tensorSectionsUnit U₀.ι L (ψ (b i.down)))))))
    [IsImmersion (@ProjectiveSpace.homOfGeneratingSections
      (ULift.{u} (Fin r)) inferInstance U₀.toScheme (Spec (.of k))
      (U₀.ι ≫ (X ↘ Spec (.of k))) ((Scheme.Modules.tensorPullback U₀.ι).obj L)
      (Scheme.Modules.IsInvertible.of_iso
        (((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction U₀.ι)).leftAdjointUniq
          (Scheme.Modules.pullbackPushforwardAdjunction U₀.ι)).app L).symm)
      (fun i : ULift.{u} (Fin r) ↦ SheafOfModules.unitHomEquiv _
        (Scheme.Modules.homOfGlobalSection _
          (Scheme.Modules.tensorSectionsUnit U₀.ι L (ψ (b i.down))))) hgen)] :
    ∃ U : (Spec (.of (MvPolynomial (Fin r) k))).Opens,
      (U : Set (Spec (.of (MvPolynomial (Fin r) k)))).Nonempty ∧
      ∀ v : V,
        Set.range (Spec.map (CommRingCat.ofHom
          (MvPolynomial.eval₂Hom (RingHom.id k) (fun i ↦ b.repr v i)))) ⊆ (U : Set _) →
        GeometricallyIrreducible
          (((homOfGlobalSection L (ψ v)).zeroLocus.comap π).subschemeι ≫
            π ≫ (X ↘ Spec (.of k))) := by
  classical
  let f := X ↘ Spec (.of k)
  let : T.Over (Spec (.of k)) := ⟨π ≫ f⟩
  have : Smooth (T ↘ Spec (.of k)) := show Smooth (π ≫ f) from inferInstance
  have : LocallyOfFiniteType (T ↘ Spec (.of k)) := inferInstance
  have : QuasiCompact (T ↘ Spec (.of k)) := show QuasiCompact (π ≫ f) from inferInstance
  have : GeometricallyConnected (T ↘ Spec (.of k)) :=
    GeometricallyConnected.of_connectedSpace_of_isSepClosed _
  have : GeometricallyIrreducible (T ↘ Spec (.of k)) :=
    GeometricallyIrreducible.of_smooth_of_geometricallyConnected _
  let LT := (tensorPullback π).obj L
  have : LT.IsInvertible := IsInvertible.of_iso ((tensorComparison π).app L).symm
  let ψT : V →+ Γ(LT, ⊤) := (tensorSectionsUnit π L).hom.comp ψ
  have hlinearT (c : k) (v : V) :
      ψT (c • v) = (T ↘ Spec (.of k)).appTop
        ((Scheme.ΓSpecIso (.of k)).inv c) • ψT v := by
    change tensorSectionsUnit π L (ψ (c • v)) = _
    rw [hlinear, tensorUnit_smul]
    rfl
  let : Module k Γ(LT, ⊤) := Module.compHom Γ(LT, ⊤)
    (Scheme.globalSectionsRingHom k (X := T))
  let ψL : V →ₗ[k] Γ(LT, ⊤) := { ψT with map_smul' := hlinearT }
  have : FiniteDimensional k V := Module.Finite.of_basis b
  have hcomp := bertini_finiteCover_transverse_component k X d hd hdim T π S
    hclosed U₀ hU₀ L V r b ψ hlinear hgen
  have hbase := bertini_finiteCover_base_codimension k X d hdim T π S
    hclosed U₀ hU₀ L V r b ψ hgen
  obtain ⟨U, hU, hmem⟩ := exists_open_geometricallyIrreducible_linearSystemMember
    k T LT V ψL hcomp (fun B hB ↦ by
      rw [hbase B hB]
      exact_mod_cast hd) r b
  refine ⟨U, hU, fun v hv ↦ ?_⟩
  have ha : Set.range (Spec.map
      (CommRingCat.ofHom (MvPolynomial.aeval (R := k) (b.repr v)).toRingHom)) ⊆ U := hv
  have hm := hmem k (b.repr v) ha
  have hg := geometric_member_of_bertini LT r b ψT hlinearT v hm
  change GeometricallyIrreducible
    ((homOfGlobalSection ((tensorPullback π).obj L)
      (tensorSectionsUnit π L (ψ v))).zeroLocus.subschemeι ≫ π ≫ f) at hg
  rw [← zeroLocus_tensorUnit π L (ψ v)] at hg
  exact hg

/-- General sections cut geometrically irreducible subschemes simultaneously on `X` and `T`.
A finite set of closed points represents the reduced finite set of rational points: over
an algebraically closed field, closed points of a finite-type scheme are exactly rational
points. `U₀` is its open complement. The basis supplies coordinates on `A(V)` and on `P(V)`;
no injectivity of `ψ` is assumed. An additive map with the displayed scalar identity is
precisely a `k`-linear map for the canonical action on global sections.

Source: main-20261015 blueprint, `lem-zl-bertini-finite-cover-curve.proof.md`, paragraph 3;
Stacks Project, Tag 0G4F (blueprint: lem-zl-bertini-finite-cover-irreducible-system).

Proof: apply irreducible Bertini to the tensor-pulled-back system on T.
Smoothness and connectedness over an algebraically closed field give geometric
irreducibility of T. The base-codimension lemma verifies the common-zero condition,
and the transverse-component lemma supplies the codimension-two witness. Linearity
identifies the section with the basis-coordinate combination in the Bertini conclusion.
Zero schemes commute with tensor pullback; the self-field base change and the ideal-sheaf
pullback isomorphisms identify the resulting member with T_v. The finite etale map π has
nonempty clopen image in connected X, hence is surjective. Its base change T_v → H_v is
surjective, so geometric irreducibility descends from T_v to H_v. Finite etaleness is
preserved by base change, and smoothness by composition. Geometric irreducibility implies
connectedness.
-/
theorem exists_open_geometricallyIrreducible_finiteCover_linearSystem
    (k : Type u) [Field k] [IsAlgClosed k]
    (X : Scheme.{u}) [X.Over (Spec (.of k))] [IsAffine X] [ConnectedSpace X]
    [Smooth (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))]
    (d : ℕ) (_hd : 2 ≤ d) (_hdim : X.IsPureDimension d)
    (T : Scheme.{u}) [ConnectedSpace T] (π : T ⟶ X) [IsFinite π] [Etale π]
    (S : Finset X) (_hS : S.Nonempty) (_hclosed : ∀ x ∈ S, IsClosed ({x} : Set X))
    (U₀ : X.Opens) (_hU₀ : (U₀ : Set X) = (S : Set X)ᶜ)
    (L : X.Modules) [L.IsInvertible]
    (V : Type v) [AddCommGroup V] [Module k V]
    (r : ℕ) (b : Module.Basis (Fin r) k V) (ψ : V →+ Γ(L, ⊤))
    (_hlinear : ∀ (c : k) (v : V),
      ψ (c • v) = (X ↘ Spec (.of k)).appTop ((Scheme.ΓSpecIso (.of k)).inv c) • ψ v)
    (_hvan : ∀ (v : V) (x : X), x ∈ S →
      x ∈ (Scheme.Modules.homOfGlobalSection L (ψ v)).zeroLocus.support)
    (hgen : Epi (((Scheme.Modules.tensorPullback U₀.ι).obj L).freeHomEquiv.symm
      (fun i : ULift.{u} (Fin r) ↦ SheafOfModules.unitHomEquiv _
        (Scheme.Modules.homOfGlobalSection _
          (Scheme.Modules.tensorSectionsUnit U₀.ι L (ψ (b i.down)))))))
    [IsImmersion (@ProjectiveSpace.homOfGeneratingSections
      (ULift.{u} (Fin r)) inferInstance U₀.toScheme (Spec (.of k))
      (U₀.ι ≫ (X ↘ Spec (.of k))) ((Scheme.Modules.tensorPullback U₀.ι).obj L)
      (Scheme.Modules.IsInvertible.of_iso
        (((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction U₀.ι)).leftAdjointUniq
          (Scheme.Modules.pullbackPushforwardAdjunction U₀.ι)).app L).symm)
      (fun i : ULift.{u} (Fin r) ↦ SheafOfModules.unitHomEquiv _
        (Scheme.Modules.homOfGlobalSection _
          (Scheme.Modules.tensorSectionsUnit U₀.ι L (ψ (b i.down))))) hgen)] :
    ∃ U : (Spec (.of (MvPolynomial (Fin r) k))).Opens,
      (U : Set (Spec (.of (MvPolynomial (Fin r) k)))).Nonempty ∧
      ∀ v : V,
        Set.range (Spec.map (CommRingCat.ofHom
          (MvPolynomial.eval₂Hom (RingHom.id k) (fun i ↦ b.repr v i)))) ⊆ (U : Set _) →
        GeometricallyIrreducible
          ((Scheme.Modules.homOfGlobalSection L (ψ v)).zeroLocus.subschemeι ≫
            (X ↘ Spec (.of k))) ∧
        GeometricallyIrreducible
          (pullback.snd π (Scheme.Modules.homOfGlobalSection L (ψ v)).zeroLocus.subschemeι ≫
            (Scheme.Modules.homOfGlobalSection L (ψ v)).zeroLocus.subschemeι ≫
              (X ↘ Spec (.of k))) ∧
        (Smooth ((Scheme.Modules.homOfGlobalSection L (ψ v)).zeroLocus.subschemeι ≫
            (X ↘ Spec (.of k))) →
          Smooth
            (pullback.snd π (Scheme.Modules.homOfGlobalSection L (ψ v)).zeroLocus.subschemeι ≫
              (Scheme.Modules.homOfGlobalSection L (ψ v)).zeroLocus.subschemeι ≫
                (X ↘ Spec (.of k))) ∧
          IsFinite (pullback.snd π
            (Scheme.Modules.homOfGlobalSection L (ψ v)).zeroLocus.subschemeι) ∧
          Etale (pullback.snd π
            (Scheme.Modules.homOfGlobalSection L (ψ v)).zeroLocus.subschemeι) ∧
          ConnectedSpace (Scheme.Modules.homOfGlobalSection L (ψ v)).zeroLocus.subscheme ∧
          ConnectedSpace
            (pullback π (Scheme.Modules.homOfGlobalSection L (ψ v)).zeroLocus.subschemeι :
              Scheme.{u})) := by
  classical
  have : Surjective π := by
    have hc : IsClopen (Set.range π) :=
      ⟨π.isClosedMap.isClosed_range, π.isOpenMap.isOpen_range⟩
    exact ⟨fun x ↦ (hc.eq_univ (Set.range_nonempty π) ▸ Set.mem_univ x : x ∈ Set.range π)⟩
  obtain ⟨U, hU, hT⟩ := exists_open_on_finiteCover k X d _hd _hdim T π S
    _hclosed U₀ _hU₀ L V r b ψ _hlinear hgen
  refine ⟨U, hU, fun v hv ↦ ?_⟩
  have ht := hT v hv
  let J := (homOfGlobalSection L (ψ v)).zeroLocus
  let e := J.comapIso π
  have he' : e.hom ≫ pullback.snd π J.subschemeι ≫ J.subschemeι =
      (J.comap π).subschemeι ≫ π := by
    change (J.comapIso π).hom ≫ pullback.snd π J.subschemeι ≫ J.subschemeι = _
    rw [← pullback.condition, ← Category.assoc, J.comapIso_hom_fst]
  have he : e.hom ≫ pullback.snd π J.subschemeι ≫ J.subschemeι ≫
      (X ↘ Spec (.of k)) = (J.comap π).subschemeι ≫ π ≫
        (X ↘ Spec (.of k)) := by
    simpa only [Category.assoc] using
      congrArg (fun q ↦ q ≫ (X ↘ Spec (.of k))) he'
  have htv : GeometricallyIrreducible
      (pullback.snd π J.subschemeι ≫ J.subschemeι ≫ (X ↘ Spec (.of k))) := by
    rw [← he] at ht
    exact (MorphismProperty.cancel_left_of_respectsIso
      (P := @GeometricallyIrreducible) e.hom _).mp ht
  have : GeometricallyIrreducible
      (pullback.snd π J.subschemeι ≫ J.subschemeι ≫ (X ↘ Spec (.of k))) := htv
  have hx : GeometricallyIrreducible (J.subschemeι ≫ (X ↘ Spec (.of k))) :=
    GeometricallyIrreducible.of_surjective (pullback.snd π J.subschemeι) _
  refine ⟨hx, htv, ?_⟩
  intro hs
  have : Smooth (J.subschemeι ≫ (X ↘ Spec (.of k))) := hs
  have : GeometricallyIrreducible (J.subschemeι ≫ (X ↘ Spec (.of k))) := hx
  have : GeometricallyIrreducible
      (pullback.snd π J.subschemeι ≫ J.subschemeι ≫ (X ↘ Spec (.of k))) := htv
  have : IrreducibleSpace J.subscheme :=
    GeometricallyIrreducible.irreducibleSpace_of_subsingleton
      (J.subschemeι ≫ (X ↘ Spec (.of k)))
  have : IrreducibleSpace (pullback π J.subschemeι : Scheme.{u}) :=
    GeometricallyIrreducible.irreducibleSpace_of_subsingleton
      (pullback.snd π J.subschemeι ≫ J.subschemeι ≫ (X ↘ Spec (.of k)))
  exact ⟨inferInstance, inferInstance, inferInstance, inferInstance, inferInstance⟩

end

end AlgebraicGeometry
