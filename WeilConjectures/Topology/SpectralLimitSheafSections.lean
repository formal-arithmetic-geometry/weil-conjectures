/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Topology.Spectral.Basic
public import Mathlib.Topology.Spectral.Hom
public import Mathlib.Topology.Sheaves.Functors
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
import WeilConjectures.Topology.AbelianLargeCompactOpenColimit
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
import WeilConjectures.Topology.SpectralDirectedLimit
import WeilConjectures.Topology.SpectralLimitUnitGeneration
import WeilConjectures.Topology.SpectralLimitUnitZero

/-!
# Sections of abelian sheaf systems on spectral inverse limits

Source: Stacks Project, Sheaves on Spaces, Tag 0A33, lemma-descend-opens
(blueprint: lem-weil-pbc-spectral-limit-sheaf-sections).
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

/-- Restrict the existing filtered-colimit preservation to a smaller indexing universe.
This supplies sheafification for abelian coefficients larger than the space universe.
Source: Stacks Project, Sheaves on Spaces, Tag 0A33, passage to abelian sheaves;
Mathlib's `preservesFilteredColimitsOfSize_of_univLE`
(blueprint: lem-weil-pbc-spectral-limit-sheaf-sections). -/
noncomputable instance (priority := 90) AddCommGrpCat.forget_preservesSmallerFilteredColimits
    [UnivLE.{u, v}] :
    PreservesFilteredColimitsOfSize.{u, u} (forget AddCommGrpCat.{v}) :=
  preservesFilteredColimitsOfSize_of_univLE.{v, v} (forget AddCommGrpCat.{v})

namespace TopCat.Sheaf

/-- The canonical map from the colimit of finite-stage section groups is an isomorphism.
Source: Stacks Project, Sheaves on Spaces, Tag 0A33, lemma-descend-opens
(blueprint: lem-weil-pbc-spectral-limit-sheaf-sections).

The isomorphisms `eG` and `eB` identify the objects of the two diagrams with their
specified formulas. `hGmap` characterizes the pulled-back transition on every unit
section: this is precisely pullback of the adjoint of `alpha`. `hBmap` specifies the
finite-stage transition, and `hm` specifies the comparison on every coprojection.
Heterogeneous equality only transports across equal inverse-image opens. Thus none
of these maps is an unspecified comparison. The inverse image is the recorded
sheafification construction, allowing the coefficient universe to exceed that of the spaces.

Proof: The spectral inverse-limit theorem makes the limit spectral and the
inverse-image open compact. Evaluation on that open preserves the given colimit
of large-universe abelian sheaves, by the compact-basis and compact-intersection
properties. Thus sections of the colimit have representatives in G and equality
is detected at a later G-stage. Construct n_j by the pullback unit, eG_j inverse
and transport of the open; hm identifies its colimit comparison with m.
For injectivity, represent a kernel element by a coefficient section at j.
Its unit image becomes zero at a later G-stage. The transition formula hGmap
identifies this with the unit of its coefficient transition. Zero detection on
a compact open gives vanishing at a later coefficient stage; the alpha cocycle
and hBmap make the B-colimit representative zero. Applying this to differences
proves injectivity. For surjectivity, represent the target section in some G_j,
move above i and use finite-stage unit generation to obtain a coefficient section.
The cocone identities and hm identify its B-colimit image with the given section.
The resulting bijective homomorphism is an isomorphism. -/
theorem spectralLimit_sheaf_sections
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
    (halpha_id : ∀ (j : I) (V : Opens (S j)) (s : (F j).obj.obj (op V)),
      HEq ((alpha j j le_rfl).hom.app (op V) s) s)
    (halpha_comp : ∀ (j k l : I) (hjk : j ≤ k) (hkl : k ≤ l)
        (V : Opens (S j)) (s : (F j).obj.obj (op V)),
      HEq ((alpha k l hkl).hom.app (op ((Opens.map (f j k hjk)).obj V))
          ((alpha j k hjk).hom.app (op V) s))
        ((alpha j l (hjk.trans hkl)).hom.app (op V) s))
    (G : I ⥤ X.Sheaf AddCommGrpCat.{max u v})
    (eG : ∀ j : I, G.obj j ≅
      (Functor.sheafPullbackConstruction.sheafPullback (Opens.map (p j))
        AddCommGrpCat.{max u v} (Opens.grothendieckTopology (S j))
          (Opens.grothendieckTopology X)).obj (F j))
    (hGmap : ∀ (j k : I) (hjk : j ≤ k) (V : Opens (S j))
        (s : (F j).obj.obj (op V)),
      HEq (((G.map (homOfLE hjk)) ≫ (eG k).hom).hom.app
          (op ((Opens.map (p j)).obj V))
        ((eG j).inv.hom.app (op ((Opens.map (p j)).obj V))
          (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
            (Opens.map (p j)) AddCommGrpCat.{max u v}
            (Opens.grothendieckTopology (S j)) (Opens.grothendieckTopology X)).unit.app
              (F j)).hom.app (op V) s)))
        (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
          (Opens.map (p k)) AddCommGrpCat.{max u v}
          (Opens.grothendieckTopology (S k)) (Opens.grothendieckTopology X)).unit.app
            (F k)).hom.app (op ((Opens.map (f j k hjk)).obj V))
              ((alpha j k hjk).hom.app (op V) s)))
    (c : Cocone G) (hc : IsColimit c)
    (i : I) (U : Opens (S i)) (hU : IsCompact (U : Set (S i)))
    (B : Set.Ici i ⥤ AddCommGrpCat.{max u v})
    (eB : ∀ j : Set.Ici i, B.obj j ≅
      (F j.val).obj.obj (op ((Opens.map (f i j.val j.property)).obj U)))
    (hBmap : ∀ (j k : Set.Ici i) (hjk : j ≤ k)
        (s : (F j.val).obj.obj (op ((Opens.map (f i j.val j.property)).obj U))),
      HEq ((eB k).hom (B.map (homOfLE hjk) ((eB j).inv s)))
        ((alpha j.val k.val hjk).hom.app
          (op ((Opens.map (f i j.val j.property)).obj U)) s))
    [HasColimit B]
    (m : colimit B ⟶ c.pt.obj.obj (op ((Opens.map (p i)).obj U)))
    (hm : ∀ (j : Set.Ici i)
        (s : (F j.val).obj.obj (op ((Opens.map (f i j.val j.property)).obj U))),
      HEq (m (colimit.ι B j ((eB j).inv s)))
        ((c.ι.app j.val).hom.app
          (op ((Opens.map (p j.val)).obj ((Opens.map (f i j.val j.property)).obj U)))
          ((eG j.val).inv.hom.app
            (op ((Opens.map (p j.val)).obj ((Opens.map (f i j.val j.property)).obj U)))
            (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
              (Opens.map (p j.val)) AddCommGrpCat.{max u v}
              (Opens.grothendieckTopology (S j.val))
              (Opens.grothendieckTopology X)).unit.app (F j.val)).hom.app
                (op ((Opens.map (f i j.val j.property)).obj U)) s)))) :
    IsIso m := by
  classical
  have : Nonempty (Set.Ici i) := ⟨⟨i, le_rfl⟩⟩
  have : IsDirected (Set.Ici i) (· ≤ ·) := ⟨fun j k ↦ by
    obtain ⟨l, hjl, hkl⟩ := exists_ge_ge j.val k.val
    exact ⟨⟨l, j.property.trans hjl⟩, hjl, hkl⟩⟩
  let V := (Opens.map (p i)).obj U
  have hV (j : I) (hij : i ≤ j) :
      (Opens.map (p j)).obj ((Opens.map (f i j hij)).obj U) = V := by
    change (Opens.map (p j ≫ f i j hij)).obj U = V
    rw [hpcomp]
  let n (j : I) (hij : i ≤ j) :=
    (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
      (Opens.map (p j)) AddCommGrpCat.{max u v}
      (Opens.grothendieckTopology (S j)) (Opens.grothendieckTopology X)).unit.app
        (F j)).hom.app (op ((Opens.map (f i j hij)).obj U))) ≫
      (eG j).inv.hom.app
        (op ((Opens.map (p j)).obj ((Opens.map (f i j hij)).obj U))) ≫
      (G.obj j).obj.map (eqToHom (hV j hij).symm).op
  have transport (P : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{max u v})
      {W W' : Opens X} (e : W = W') (t : P.obj (op W)) :
      HEq (P.map (eqToHom e.symm).op t) t := by
    subst W'
    simp
  have hn0 (j : I) (hij : i ≤ j)
      (s : (F j).obj.obj (op ((Opens.map (f i j hij)).obj U))) :
      HEq (n j hij s)
        ((eG j).inv.hom.app
          (op ((Opens.map (p j)).obj ((Opens.map (f i j hij)).obj U)))
            (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
              (Opens.map (p j)) AddCommGrpCat.{max u v}
              (Opens.grothendieckTopology (S j))
              (Opens.grothendieckTopology X)).unit.app (F j)).hom.app
                (op ((Opens.map (f i j hij)).obj U)) s)) :=
    transport (G.obj j).obj (hV j hij) _
  have hn (j : I) (hij : i ≤ j)
      (s : (F j).obj.obj (op ((Opens.map (f i j hij)).obj U))) :
      HEq ((c.ι.app j).hom.app (op V) (n j hij s))
        ((c.ι.app j).hom.app
          (op ((Opens.map (p j)).obj ((Opens.map (f i j hij)).obj U)))
            ((eG j).inv.hom.app
              (op ((Opens.map (p j)).obj ((Opens.map (f i j hij)).obj U)))
                (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
                  (Opens.map (p j)) AddCommGrpCat.{max u v}
                  (Opens.grothendieckTopology (S j))
                  (Opens.grothendieckTopology X)).unit.app (F j)).hom.app
                    (op ((Opens.map (f i j hij)).obj U)) s))) := by
    dsimp [n]
    rw [NatTrans.naturality_apply]
    exact transport c.pt.obj (hV j hij) _
  have hm' (j : Set.Ici i) (s : B.obj j) :
      m (colimit.ι B j s) =
        (c.ι.app j.val).hom.app (op V) (n j.val j.property ((eB j).hom s)) := by
    have h := hm j ((eB j).hom s)
    have h' := hn j.val j.property ((eB j).hom s)
    have hs : (eB j).inv ((eB j).hom s) = s := by simp
    rw [hs] at h
    exact eq_of_heq (h.trans h'.symm)
  have ht := Topology.spectralSpace_directedLimit (fun j ↦ S j)
    (fun j k h ↦ f j k h) hf
    (fun j ↦ congrArg (fun g : S j ⟶ S j ↦ (g : S j → S j)) (hfid j))
    (fun j k l hjk hkl ↦ congrArg (fun g : S l ⟶ S j ↦ (g : S l → S j))
      (hfcomp j k l hjk hkl)) X (fun j ↦ p j) (fun j ↦ (p j).hom.continuous)
    (fun j k h ↦ congrArg (fun g : X ⟶ S j ↦ (g : X → S j)) (hpcomp j k h))
    (by
      intro x y he
      apply (hlimit (fun j ↦ p j x) (by
        intro j k h
        exact ConcreteCategory.congr_hom (hpcomp j k h) x)).unique
      · exact fun j ↦ rfl
      · exact fun j ↦ (congrFun he j).symm)
    (fun a ha ↦ (hlimit a ha).exists) htop
  have : SpectralSpace X := ht.1
  have hcompact : IsCompact (V : Set X) :=
    (ht.2 i).isCompact_preimage_of_isOpen U.isOpen hU
  let E := (sheafSections (Opens.grothendieckTopology X)
    AddCommGrpCat.{max u v}).obj (op V)
  have : HasColimit G := HasColimit.mk ⟨c, hc⟩
  have : PreservesColimit G E :=
    TopCat.abelianCompactOpen_preservesDirectedColimits.{u, v} X
      (fun W hW x hx ↦ by
        obtain ⟨T, ⟨hTo, hTc⟩, hxT, hTW⟩ :=
          PrespectralSpace.isTopologicalBasis.exists_subset_of_mem_open hx hW
        exact ⟨T, hTo, hTc, hxT, hTW⟩)
      (fun W T hW hT hWc hTc ↦ hWc.inter_of_isOpen hTc hW hT) I G V hcompact
  let ec := E.mapCocone c
  have hec : IsColimit ec := isColimitOfPreserves E hc
  have hgen := spectralLimit_unit_generation S f hf hfid hfcomp X p hpcomp hlimit htop
    F alpha halpha_id halpha_comp G eG hGmap i U hU n hn0
  have hzero : ∀ (j : I) (hij : i ≤ j)
      (s : (F j).obj.obj (op ((Opens.map (f i j hij)).obj U))),
      (∃ (k : I) (hjk : j ≤ k), (G.map (homOfLE hjk)).hom.app (op V)
        (n j hij s) = 0) →
      ∃ (k : I) (hjk : j ≤ k), (alpha j k hjk).hom.app
        (op ((Opens.map (f i j hij)).obj U)) s = 0 := by
    classical
    intro j hij s hz
    obtain ⟨k, hjk, hk⟩ := hz
    let V := (Opens.map (p i)).obj U
    let Uj := (Opens.map (f i j hij)).obj U
    let W := (Opens.map (f j k hjk)).obj Uj
    let t := (alpha j k hjk).hom.app (op Uj) s
    have hA : (Opens.map (p j)).obj Uj = V := by
      change (Opens.map (p j ≫ f i j hij)).obj U = V
      rw [hpcomp]
    have heq_zero {Y : TopCat.{u}} (P : (Opens Y)ᵒᵖ ⥤ AddCommGrpCat.{max u v})
        {A B : Opens Y} (h : A = B) {a : P.obj (op A)} {b : P.obj (op B)}
        (hab : HEq a b) (ha : a = 0) : b = 0 := by
      subst B
      exact (eq_of_heq hab).symm.trans ha
    have hmap_zero (P Q : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{max u v}) (φ : P ⟶ Q)
        {A B : Opens X} (h : A = B) {a : P.obj (op A)} {b : P.obj (op B)}
        (hab : HEq a b) (ha : φ.app (op A) a = 0) : φ.app (op B) b = 0 := by
      subst B
      rw [← eq_of_heq hab]
      exact ha
    have hlhs : ((G.map (homOfLE hjk)) ≫ (eG k).hom).hom.app
        (op ((Opens.map (p j)).obj Uj))
          ((eG j).inv.hom.app (op ((Opens.map (p j)).obj Uj))
            (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
              (Opens.map (p j)) AddCommGrpCat.{max u v}
              (Opens.grothendieckTopology (S j))
              (Opens.grothendieckTopology X)).unit.app (F j)).hom.app (op Uj) s)) = 0 := by
      apply hmap_zero (G.obj j).obj _
        ((G.map (homOfLE hjk)) ≫ (eG k).hom).hom hA.symm (hn0 j hij s)
      change (eG k).hom.hom.app (op V)
        ((G.map (homOfLE hjk)).hom.app (op V) (n j hij s)) = 0
      rw [hk, map_zero]
    have ht : (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
        (Opens.map (p k)) AddCommGrpCat.{max u v}
        (Opens.grothendieckTopology (S k))
        (Opens.grothendieckTopology X)).unit.app (F k)).hom.app (op W)) t = 0 := by
      apply heq_zero _ (show (Opens.map (p j)).obj Uj =
          (Opens.map (p k)).obj W from by
        change (Opens.map (p j)).obj Uj = (Opens.map (p k ≫ f j k hjk)).obj Uj
        rw [hpcomp]) (hGmap j k hjk Uj s) hlhs
    have hWc : IsCompact (W : Set (S k)) :=
      (hf j k hjk).isCompact_preimage_of_isOpen Uj.isOpen
        ((hf i j hij).isCompact_preimage_of_isOpen U.isOpen hU)
    obtain ⟨l, hkl, hl⟩ := spectralLimit_unit_eventually_zero S f hf hfid hfcomp
      X p hpcomp hlimit htop F alpha k W hWc t ht
    refine ⟨l, hjk.trans hkl, ?_⟩
    have hcomp : (Opens.map (f k l hkl)).obj W =
        (Opens.map (f j l (hjk.trans hkl))).obj Uj := by
      change (Opens.map (f k l hkl ≫ f j k hjk)).obj Uj = _
      rw [hfcomp]
    exact heq_zero (F l).obj hcomp (halpha_comp j k l hjk hkl Uj s) hl
  apply (ConcreteCategory.isIso_iff_bijective m).mpr
  refine ⟨?_, ?_⟩
  · suffices hz : ∀ a : ↑(colimit B), m a = 0 → a = 0 by
      intro a b hab
      apply sub_eq_zero.mp
      apply hz (a - b)
      rw [map_sub, hab, sub_self]
    intro a ha
    obtain ⟨j, s, rfl⟩ := Concrete.colimit_exists_rep B a
    have hnzero : (c.ι.app j.val).hom.app (op V)
        (n j.val j.property ((eB j).hom s)) = 0 := by
      rw [← hm']
      exact ha
    have hezero : ec.ι.app j.val (n j.val j.property ((eB j).hom s)) =
        ec.ι.app j.val 0 := by
      change (c.ι.app j.val).hom.app (op V)
        (n j.val j.property ((eB j).hom s)) = (c.ι.app j.val).hom.app (op V) 0
      simpa only [map_zero] using hnzero
    obtain ⟨k, a, b, hk⟩ :=
      (Concrete.isColimit_rep_eq_iff_exists (G ⋙ E) hec _ _).mp hezero
    have hk' : (G.map a).hom.app (op V) (n j.val j.property ((eB j).hom s)) = 0 := by
      change (G.map a).hom.app (op V) (n j.val j.property ((eB j).hom s)) =
        (G.map b).hom.app (op V) 0 at hk
      simpa only [map_zero] using hk
    obtain ⟨l, hjl, hl⟩ := hzero j.val j.property ((eB j).hom s) ⟨k, a.le, hk'⟩
    let l' : Set.Ici i := ⟨l, j.property.trans hjl⟩
    have hmap := hBmap j l' hjl ((eB j).hom s)
    have hs : (eB j).inv ((eB j).hom s) = s := by simp
    rw [hs, hl] at hmap
    have hUeq : (Opens.map (f j.val l hjl)).obj
        ((Opens.map (f i j.val j.property)).obj U) =
        (Opens.map (f i l l'.property)).obj U := by
      change (Opens.map (f j.val l hjl ≫ f i j.val j.property)).obj U = _
      rw [hfcomp]
    have zeq (P : (Opens (S l))ᵒᵖ ⥤ AddCommGrpCat.{max u v})
        {A D : Opens (S l)} (h : A = D) :
        HEq (0 : P.obj (op A)) (0 : P.obj (op D)) := by
      subst D
      rfl
    have hmap' : B.map (homOfLE hjl : j ⟶ l') s = 0 := by
      apply (ConcreteCategory.isIso_iff_bijective (eB l').hom).mp inferInstance |>.1
      exact (eq_of_heq (hmap.trans (zeq (F l).obj hUeq))).trans (map_zero _).symm
    have hw := ConcreteCategory.congr_hom (colimit.w B (homOfLE hjl : j ⟶ l')) s
    simpa only [ConcreteCategory.comp_apply, hmap', map_zero] using hw.symm
  · intro t
    obtain ⟨j, s, hs⟩ := Concrete.isColimit_exists_rep (G ⋙ E) hec t
    obtain ⟨k, hik, hjk⟩ := exists_ge_ge i j
    let sk := (G.map (homOfLE hjk)).hom.app (op V) s
    obtain ⟨l, hkl, a, ha⟩ := hgen k hik sk
    let l' : Set.Ici i := ⟨l, hik.trans hkl⟩
    refine ⟨colimit.ι B l' ((eB l').inv a), ?_⟩
    rw [hm']
    have hea : (eB l').hom ((eB l').inv a) = a := by simp
    rw [hea]
    change (c.ι.app l).hom.app (op V) (n l (hik.trans hkl) a) = t
    have hha := congrArg ((c.ι.app l).hom.app (op V)) ha
    have hw₁ := ConcreteCategory.congr_hom
      (congrArg (fun q ↦ q.hom.app (op V)) (c.w (homOfLE hkl))) sk
    have hw₂ := ConcreteCategory.congr_hom
      (congrArg (fun q ↦ q.hom.app (op V)) (c.w (homOfLE hjk))) s
    exact hha.symm.trans (hw₁.trans (hw₂.trans hs))

end TopCat.Sheaf
