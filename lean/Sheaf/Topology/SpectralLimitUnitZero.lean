/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group W3
-/
module

public import Mathlib.Topology.Spectral.Basic
public import Mathlib.Topology.Spectral.Hom
public import Mathlib.Topology.Sheaves.Functors
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Sheaf.Topology.AbelianLargeCompactOpenColimit
import Mathlib.Topology.Sheaves.Points
import Mathlib.CategoryTheory.Sites.Point.Skyscraper
import Sheaf.Topology.SpectralLimitDescendOpens
import Sheaf.Topology.SpectralDirectedLimit
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

/-! # Finite-stage detection of zero unit sections

Source: Stacks Project, Sheaves, Tag 0A33, proof of lemma-descend-opens,
using Tag 0A32, lemma-compute-pullback-to-limit.
(blueprint: lem-weil-pbc-spectral-limit-unit-eventually-zero)
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace


namespace TopCat.Sheaf

set_option backward.isDefEq.respectTransparency false in
private theorem pullback_unit_locally_zero
    {X Y : TopCat.{u}} (f : X ⟶ Y) (F : Y.Sheaf AddCommGrpCat.{max u v})
    (U : Opens Y) (s : F.obj.obj (op U))
    (hs : (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
      (Opens.map f) AddCommGrpCat.{max u v} (Opens.grothendieckTopology Y)
        (Opens.grothendieckTopology X)).unit.app F).hom.app (op U)) s = 0)
    (x : X) (hx : f x ∈ U) :
    ∃ (W : Opens Y) (_hxW : f x ∈ W) (hWU : W ≤ U),
      F.obj.map (homOfLE hWU).op s = 0 := by
  let Φ := Opens.pointGrothendieckTopology x
  let Ψ := Opens.pointGrothendieckTopology (f x)
  let T := Ψ.sheafFiber.obj F
  let q := Ψ.skyscraperSheafAdjunction.unit.app F
  let q' : F ⟶ (pushforward AddCommGrpCat.{max u v} f).obj (Φ.skyscraperSheaf T) := q
  let adj := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (Opens.map f) AddCommGrpCat.{max u v} (Opens.grothendieckTopology Y)
      (Opens.grothendieckTopology X)
  let r := (adj.homEquiv F (Φ.skyscraperSheaf T)).symm q'
  have hq : adj.unit.app F ≫ (pushforward AddCommGrpCat.{max u v} f).map r = q' :=
    (adj.homEquiv F (Φ.skyscraperSheaf T)).apply_symm_apply q'
  have hqzero : q'.hom.app (op U) s = 0 := by
    have h := congrArg (fun a ↦ a.hom.app (op U) s) hq
    change r.hom.app (op ((Opens.map f).obj U))
      ((adj.unit.app F).hom.app (op U) s) = q'.hom.app (op U) s at h
    rw [hs, map_zero] at h
    exact h.symm
  have hcoord : q.hom.app (op U) ≫ Pi.π (fun _ : Ψ.fiber.obj U ↦ T) ⟨⟨hx⟩⟩ =
      Ψ.toPresheafFiber U ⟨⟨hx⟩⟩ F.obj := by
    dsimp [q]
    rw [← Ψ.skyscraperSheafAdjunction.homEquiv_id]
    have hqhom := Ψ.skyscraperSheafAdjunction_homEquiv_apply_hom (F := F) (𝟙 T)
    change ((Ψ.skyscraperSheafAdjunction.homEquiv F T) (𝟙 T)).hom =
      Ψ.skyscraperPresheafHomEquiv (𝟙 T) at hqhom
    rw [hqhom]
    rw [Ψ.skyscraperPresheafHomEquiv_app_π]
    exact Category.comp_id _
  have hg : Ψ.toPresheafFiber U ⟨⟨hx⟩⟩ F.obj s =
      Ψ.toPresheafFiber U ⟨⟨hx⟩⟩ F.obj 0 := by
    rw [map_zero, ← hcoord]
    change (Pi.π (fun _ : Ψ.fiber.obj U ↦ T) ⟨⟨hx⟩⟩) (q'.hom.app (op U) s) = 0
    rw [hqzero, map_zero]
  obtain ⟨W, a, y, _, he⟩ := (Ψ.toPresheafFiber_eq_iff' U ⟨⟨hx⟩⟩ s 0).mp hg
  refine ⟨W, y.down.down, a.le, ?_⟩
  have ea : a = homOfLE a.le := Subsingleton.elim _ _
  simpa only [ea, map_zero] using he

/-- A coefficient section with zero inverse-image unit vanishes after applying a
coefficient transition at a sufficiently late stage. No coefficient cocycle is needed.

Proof: At every image point p_j(x), map the coefficient sheaf to the skyscraper of
its fiber. By the inverse-image adjunction this map factors through the pullback unit.
Its value on s is zero, hence the germ of s is zero. Filtered-colimit equality gives
an open neighborhood on which s vanishes. Refine these neighborhoods by compact
opens in S_j. Their inverse images cover the compact limit open, so finitely many
suffice. Their union A is compact open, and descent of open inclusions gives a later
stage where the inverse image of V lies in that of A. Naturality of alpha makes the
later section zero on each covering open; sheaf separation makes it zero globally.
If the limit open is empty, the finite cover is empty and descent makes the stage
domain empty. The maps alpha need only be sheaf morphisms; coherence is unnecessary.
Source: Stacks Project, Sheaves, Tags 008H and 0A32 (injectivity argument);
Topology, Tag 0A30(2), descent of compact-open inclusions.
(blueprint: lem-weil-pbc-spectral-limit-unit-eventually-zero) -/
theorem spectralLimit_unit_eventually_zero
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (S : I → TopCat.{u}) [∀ j : I, SpectralSpace (S j)]
    (f : ∀ (j k : I), j ≤ k → (S k ⟶ S j))
    (hf : ∀ (j k : I) (h : j ≤ k), IsSpectralMap (f j k h))
    (hfid : ∀ j : I, f j j le_rfl = 𝟙 (S j))
    (hfcomp : ∀ (j k l : I) (hjk : j ≤ k) (hkl : k ≤ l),
      f k l hkl ≫ f j k hjk = f j l (hjk.trans hkl))
    (X : TopCat.{u}) (p : ∀ j : I, X ⟶ S j)
    (hpcomp : ∀ (j k : I) (h : j ≤ k), p k ≫ f j k h = p j)
    (hlimit : ∀ a : ∀ j : I, S j,
      (∀ (j k : I) (h : j ≤ k), f j k h (a k) = a j) →
      ∃! x : X, ∀ j : I, p j x = a j)
    (htop : X.str = ⨅ j : I, TopologicalSpace.induced (p j) (S j).str)
    (F : ∀ j : I, (S j).Sheaf AddCommGrpCat.{max u v})
    (alpha : ∀ (j k : I) (h : j ≤ k),
      F j ⟶ (pushforward AddCommGrpCat.{max u v} (f j k h)).obj (F k))
    (j : I) (V : Opens (S j)) (hVc : IsCompact (V : Set (S j)))
    (s : (F j).obj.obj (op V))
    (hs : (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
      (Opens.map (p j)) AddCommGrpCat.{max u v} (Opens.grothendieckTopology (S j))
        (Opens.grothendieckTopology X)).unit.app (F j)).hom.app (op V)) s = 0) :
    ∃ (l : I) (hjl : j ≤ l), (alpha j l hjl).hom.app (op V) s = 0 := by
  classical
  let k := j
  let W := V
  let t := s
  have ht := hs
  have hlocal (x : X) (hx : p k x ∈ W) :=
    pullback_unit_locally_zero (p k) (F k) W t ht x hx
  have hspec := Topology.spectralSpace_directedLimit (fun a ↦ S a)
    (fun a b h ↦ f a b h) hf
    (fun a ↦ congrArg (fun g : S a ⟶ S a ↦ (g : S a → S a)) (hfid a))
    (fun a b d hab hbd ↦ congrArg (fun g : S d ⟶ S a ↦ (g : S d → S a))
      (hfcomp a b d hab hbd)) X (fun a ↦ p a) (fun a ↦ (p a).hom.continuous)
    (fun a b h ↦ congrArg (fun g : X ⟶ S a ↦ (g : X → S a)) (hpcomp a b h))
    (by
      intro x y he
      apply (hlimit (fun a ↦ p a x) (by
        intro a b h
        exact ConcreteCategory.congr_hom (hpcomp a b h) x)).unique
      · exact fun a ↦ rfl
      · exact fun a ↦ (congrFun he a).symm)
    (fun a ha ↦ (hlimit a ha).exists) htop
  have hWcompact : IsCompact (W : Set (S k)) := hVc
  let Z := (Opens.map (p k)).obj W
  have hZcompact : IsCompact (Z : Set X) :=
    (hspec.2 k).isCompact_preimage_of_isOpen W.isOpen hWcompact
  have hsmall (x : Z) :
      ∃ (D : Opens (S k)), p k x ∈ D ∧ IsCompact (D : Set (S k)) ∧
        ∃ (hDW : D ≤ W), (F k).obj.map (homOfLE hDW).op t = 0 := by
    obtain ⟨A, hxA, hAW, hAt⟩ := hlocal x x.property
    obtain ⟨D, ⟨hDo, hDc⟩, hxD, hDA⟩ :=
      PrespectralSpace.isTopologicalBasis.exists_subset_of_mem_open hxA A.isOpen
    let D' : Opens (S k) := ⟨D, hDo⟩
    have hDW : D' ≤ W := hDA.trans hAW
    refine ⟨D', hxD, hDc, hDW, ?_⟩
    have hDA' : D' ≤ A := hDA
    have he := congrArg ((F k).obj.map (homOfLE hDA').op) hAt
    simpa only [← ConcreteCategory.comp_apply, ← Functor.map_comp,
      ← op_comp, homOfLE_comp, map_zero] using he
  choose D hDx hDc hDW hDz using hsmall
  obtain ⟨b, hb⟩ := hZcompact.elim_finite_subcover
    (fun x : Z ↦ ((Opens.map (p k)).obj (D x) : Set X))
    (fun x ↦ ((Opens.map (p k)).obj (D x)).isOpen) (by
      intro x hx
      exact Set.mem_iUnion.mpr ⟨⟨x, hx⟩, hDx ⟨x, hx⟩⟩)
  let A : Opens (S k) := ⨆ x : b, D x
  have hAc : IsCompact (A : Set (S k)) := by
    simpa only [A, Opens.coe_iSup] using isCompact_iUnion (fun x : b ↦ hDc x)
  have hIncl : p k ⁻¹' (W : Set (S k)) ⊆ p k ⁻¹' (A : Set (S k)) := by
    intro x hx
    obtain ⟨a, hab, hxa⟩ := Set.mem_iUnion₂.mp (hb hx)
    exact Opens.mem_iSup.mpr ⟨⟨a, hab⟩, hxa⟩
  have hd := Topology.spectralLimit_descend_opens (fun a ↦ S a)
    (fun a b h ↦ f a b h) hf
    (fun a x ↦ ConcreteCategory.congr_hom (hfid a) x)
    (fun a b d hab hbd x ↦ ConcreteCategory.congr_hom (hfcomp a b d hab hbd) x)
    X (fun a ↦ p a) (fun a ↦ (p a).hom.continuous)
    (fun a b h x ↦ ConcreteCategory.congr_hom (hpcomp a b h) x) hlimit htop
  obtain ⟨l, hkl, _, hincl⟩ :=
    hd.2.1 k k (W : Set (S k)) (A : Set (S k))
      W.isOpen hWcompact A.isOpen hAc hIncl
  have hlate : (alpha k l hkl).hom.app (op W) t = 0 := by
    let Dl (x : b) := (Opens.map (f k l hkl)).obj (D x)
    let Wl := (Opens.map (f k l hkl)).obj W
    have hDl (x : b) : Dl x ≤ Wl := fun _ hx ↦ hDW x hx
    apply (F l).eq_of_locally_eq' Dl Wl (fun x ↦ homOfLE (hDl x))
    · intro x hx
      have hxa := hincl hx
      obtain ⟨a, ha⟩ := Opens.mem_iSup.mp hxa
      exact Opens.mem_iSup.mpr ⟨a, ha⟩
    · intro x
      have hnatur := (alpha k l hkl).hom.naturality (homOfLE (hDW x)).op
      have he := ConcreteCategory.congr_hom hnatur t
      change (alpha k l hkl).hom.app (op (D x))
          ((F k).obj.map (homOfLE (hDW x)).op t) =
        (F l).obj.map ((Opens.map (f k l hkl)).map (homOfLE (hDW x))).op
          ((alpha k l hkl).hom.app (op W) t) at he
      rw [hDz, map_zero] at he
      have hh : (Opens.map (f k l hkl)).map (homOfLE (hDW x)) =
          homOfLE (hDl x) := Subsingleton.elim _ _
      simpa only [hh, map_zero] using he.symm
  exact ⟨l, hkl, hlate⟩

end TopCat.Sheaf
