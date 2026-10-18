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
import Sheaf.Topology.AbelianPullbackLocalSections
import Sheaf.Topology.SpectralLimitDescendFiniteCover
import Sheaf.Topology.SpectralLimitUnitZero
import Sheaf.Topology.SpectralDirectedLimit
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

/-! # Finite-stage generation of inverse-image sections

Source: Stacks Project, Sheaves, Tag 0A33, proof of lemma-descend-opens,
using Tag 0A32, lemma-compute-pullback-to-limit.
(blueprint: lem-weil-pbc-spectral-limit-unit-generation)
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace


namespace TopCat.Sheaf

set_option backward.isDefEq.respectTransparency false in
/-- Every section of a pulled-back coefficient sheaf on a compact inverse-image open
becomes a unit image at a later coefficient stage.

Proof: Let eta_j be the pullback unit followed by eG_j inverse. Spectrality of
the limit makes Z = p_i⁻¹(U) compact. Represent the given section locally by eta_j
images using the inverse-image fiber isomorphism. Refine the base neighborhoods and
the limit neighborhoods by compact opens, preserving the local section equations
by restriction and naturality. Choose a finite subcover of Z. Descend that cover,
its covering equality and its inclusions in the base neighborhoods to one stage k.
Apply alpha_jk and restrict to obtain coefficient sections on the descended cover.
The transition formula hGmap and naturality identify their eta_k-images with the
restrictions of the transitioned section. On each compact pairwise intersection,
their difference has zero pullback unit. Zero detection makes this difference zero
after a coefficient transition. A common upper bound for the finitely many overlaps
and the alpha cocycle give compatible sections at one stage m. Glue them in F_m.
Naturality of eta and the transition formula identify the glued section's unit
locally, and separation of G_m gives the claimed global equality. The transports
specified by hn identify this unit with n_m. Empty covers and empty overlaps are
allowed: finite upper bounds include k, and the sheaf gluing theorem handles them.
Source: Stacks Project, Sheaves, Tag 0A32, lemma-compute-pullback-to-limit,
surjectivity paragraph, with the coefficient transitions of Tag 0A33.
(blueprint: lem-weil-pbc-spectral-limit-unit-generation) -/
theorem spectralLimit_unit_generation
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
    (_halpha_id : ∀ (j : I) (V : Opens (S j)) (s : (F j).obj.obj (op V)),
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
    (i : I) (U : Opens (S i)) (hU : IsCompact (U : Set (S i)))
    (n : ∀ (j : I) (hij : i ≤ j),
      (F j).obj.obj (op ((Opens.map (f i j hij)).obj U)) ⟶
        (G.obj j).obj.obj (op ((Opens.map (p i)).obj U)))
    (hn : ∀ (j : I) (hij : i ≤ j)
        (s : (F j).obj.obj (op ((Opens.map (f i j hij)).obj U))),
      HEq (n j hij s)
        ((eG j).inv.hom.app
          (op ((Opens.map (p j)).obj ((Opens.map (f i j hij)).obj U)))
            (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
              (Opens.map (p j)) AddCommGrpCat.{max u v}
              (Opens.grothendieckTopology (S j))
              (Opens.grothendieckTopology X)).unit.app (F j)).hom.app
                (op ((Opens.map (f i j hij)).obj U)) s)))
    : ∀ (j : I) (hij : i ≤ j)
        (s : (G.obj j).obj.obj (op ((Opens.map (p i)).obj U))),
      ∃ (k : I) (hjk : j ≤ k)
        (t : (F k).obj.obj (op ((Opens.map (f i k (hij.trans hjk))).obj U))),
        (G.map (homOfLE hjk)).hom.app (op ((Opens.map (p i)).obj U)) s =
          n k (hij.trans hjk) t := by
  classical
  let η (a : I) : F a ⟶ (pushforward AddCommGrpCat.{max u v} (p a)).obj (G.obj a) :=
    (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
      (Opens.map (p a)) AddCommGrpCat.{max u v} (Opens.grothendieckTopology (S a))
        (Opens.grothendieckTopology X)).unit.app (F a) ≫
      (pushforward AddCommGrpCat.{max u v} (p a)).map (eG a).inv
  intro j hij s
  let Z := (Opens.map (p i)).obj U
  have hlocal (V : Opens X) (t : (G.obj j).obj.obj (op V)) (x : X) (hx : x ∈ V) :
      ∃ (A : Opens (S j)) (_ : p j x ∈ A) (a : (F j).obj.obj (op A))
        (W : Opens X) (_ : x ∈ W) (hWV : W ≤ V)
        (hWA : W ≤ (Opens.map (p j)).obj A),
        (G.obj j).obj.map (homOfLE hWV).op t =
          (G.obj j).obj.map (homOfLE hWA).op ((η j).hom.app (op A) a) := by
    obtain ⟨A, hxA, a, W, hxW, hWV, hWA, he⟩ :=
      abelianPullback_localSections (p j) (F j) V ((eG j).hom.hom.app (op V) t) x hx
    refine ⟨A, hxA, a, W, hxW, hWV, hWA, ?_⟩
    have he' := congrArg ((eG j).inv.hom.app (op W)) he
    have h₁ := ConcreteCategory.congr_hom
      ((eG j).inv.hom.naturality (homOfLE hWV).op)
        ((eG j).hom.hom.app (op V) t)
    have hi := ConcreteCategory.congr_hom
      (congrArg (fun q ↦ q.hom.app (op V)) (eG j).hom_inv_id) t
    change (eG j).inv.hom.app (op V) ((eG j).hom.hom.app (op V) t) = t at hi
    change (eG j).inv.hom.app (op W) _ =
      (G.obj j).obj.map (homOfLE hWV).op
        ((eG j).inv.hom.app (op V) ((eG j).hom.hom.app (op V) t)) at h₁
    rw [hi] at h₁
    have h₂ := ConcreteCategory.congr_hom
      ((eG j).inv.hom.naturality (homOfLE hWA).op)
        (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
          (Opens.map (p j)) AddCommGrpCat.{max u v} (Opens.grothendieckTopology (S j))
            (Opens.grothendieckTopology X)).unit.app (F j)).hom.app (op A) a)
    exact h₁.symm.trans (he'.trans h₂)
  have ht := Topology.spectralSpace_directedLimit (fun a ↦ S a)
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
  have : SpectralSpace X := ht.1
  have hZc : IsCompact (Z : Set X) :=
    (ht.2 i).isCompact_preimage_of_isOpen U.isOpen hU
  have hcLocal (x : Z) :
      ∃ (A : Opens (S j)) (a : (F j).obj.obj (op A)) (W : Opens X),
        IsCompact (A : Set (S j)) ∧ IsCompact (W : Set X) ∧ x.val ∈ W ∧
        ∃ (hWZ : W ≤ Z) (hWA : W ≤ (Opens.map (p j)).obj A),
          (G.obj j).obj.map (homOfLE hWZ).op s =
            (G.obj j).obj.map (homOfLE hWA).op ((η j).hom.app (op A) a) := by
    obtain ⟨A, hxA, a, W, hxW, hWZ, hWA, he⟩ := hlocal Z s x x.property
    obtain ⟨B, ⟨hBo, hBc⟩, hxB, hBA⟩ :=
      PrespectralSpace.isTopologicalBasis.exists_subset_of_mem_open hxA A.isOpen
    let B' : Opens (S j) := ⟨B, hBo⟩
    let T := W ⊓ (Opens.map (p j)).obj B'
    have hxT : x.val ∈ T := ⟨hxW, hxB⟩
    obtain ⟨D, ⟨hDo, hDc⟩, hxD, hDT⟩ :=
      PrespectralSpace.isTopologicalBasis.exists_subset_of_mem_open hxT T.isOpen
    let D' : Opens X := ⟨D, hDo⟩
    have hDW : D' ≤ W := hDT.trans inf_le_left
    have hDB : D' ≤ (Opens.map (p j)).obj B' := hDT.trans inf_le_right
    have hBA' : B' ≤ A := hBA
    refine ⟨B', (F j).obj.map (homOfLE hBA').op a, D', hBc, hDc, hxD,
      hDW.trans hWZ, hDB, ?_⟩
    have he' := congrArg ((G.obj j).obj.map (homOfLE hDW).op) he
    have hnat := ConcreteCategory.congr_hom ((η j).hom.naturality (homOfLE hBA').op) a
    change (η j).hom.app (op B') ((F j).obj.map (homOfLE hBA').op a) =
      (G.obj j).obj.map ((Opens.map (p j)).map (homOfLE hBA')).op
        ((η j).hom.app (op A) a) at hnat
    rw [hnat]
    have hh₁ : homOfLE hDW ≫ homOfLE hWZ = homOfLE (hDW.trans hWZ) :=
      Subsingleton.elim _ _
    have hh₂ : homOfLE hDW ≫ homOfLE hWA =
        homOfLE hDB ≫ (Opens.map (p j)).map (homOfLE hBA') := Subsingleton.elim _ _
    simpa only [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp, hh₁, hh₂]
      using he'
  choose A a W hAc hWc hxW hWZ hWA he using hcLocal
  obtain ⟨b, hb⟩ := hZc.elim_finite_subcover (fun x : Z ↦ (W x : Set X))
    (fun x ↦ (W x).isOpen) (by
      intro x hx
      exact Set.mem_iUnion.mpr ⟨⟨x, hx⟩, hxW ⟨x, hx⟩⟩)
  let N := Fintype.card (↥b)
  let idx (t : Fin N) : Z := ((Fintype.equivFin ↥b).symm t).val
  have hcov : p j ⁻¹' (((Opens.map (f i j hij)).obj U) : Set (S j)) =
      ⋃ t : Fin N, (W (idx t) : Set X) := by
    have hz : p j ⁻¹' (((Opens.map (f i j hij)).obj U) : Set (S j)) = (Z : Set X) := by
      ext x
      change f i j hij (p j x) ∈ U ↔ p i x ∈ U
      have e := ConcreteCategory.congr_hom (hpcomp i j hij) x
      change f i j hij (p j x) = p i x at e
      rw [e]
    rw [hz]
    apply Set.Subset.antisymm
    · intro x hx
      obtain ⟨y, hyb, hy⟩ := Set.mem_iUnion₂.mp (hb hx)
      refine Set.mem_iUnion.mpr ⟨(Fintype.equivFin ↥b) ⟨y, hyb⟩, ?_⟩
      simpa only [idx, Equiv.symm_apply_apply] using hy
    · intro x hx
      obtain ⟨t, ht⟩ := Set.mem_iUnion.mp hx
      exact hWZ (idx t) ht
  obtain ⟨k, hjk, D, hDc, hDcover, hpD, hDA⟩ :=
    Topology.spectralLimit_descend_finite_cover (fun t ↦ S t) (fun t r h ↦ f t r h) hf
      (fun t x ↦ ConcreteCategory.congr_hom (hfid t) x)
      (fun t r l htr hrl x ↦ ConcreteCategory.congr_hom (hfcomp t r l htr hrl) x)
      X (fun t ↦ p t) (fun t ↦ (p t).hom.continuous)
      (fun t r h x ↦ ConcreteCategory.congr_hom (hpcomp t r h) x) hlimit htop
      j (((Opens.map (f i j hij)).obj U) : Set (S j))
      ((Opens.map (f i j hij)).obj U).isOpen
      ((hf i j hij).isCompact_preimage_of_isOpen U.isOpen hU)
      N (fun t ↦ (A (idx t) : Set (S j))) (fun t ↦ (W (idx t) : Set X))
      (fun t ↦ ⟨(A (idx t)).isOpen, hAc (idx t)⟩)
      (fun t ↦ ⟨(W (idx t)).isOpen, hWc (idx t)⟩) hcov (fun t ↦ hWA (idx t))
  let D' (t : Fin N) : Opens (S k) := ⟨D t, (hDc t).1⟩
  have hDA' (t : Fin N) : D' t ≤ (Opens.map (f j k hjk)).obj (A (idx t)) := hDA t
  let r (t : Fin N) := (F k).obj.map (homOfLE (hDA' t)).op
    ((alpha j k hjk).hom.app (op (A (idx t))) (a (idx t)))
  have hmapHEq (P Q : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{max u v}) (φ : P ⟶ Q)
      {A B : Opens X} (e : A = B) {a : P.obj (op A)} {b : P.obj (op B)}
      (h : HEq a b) : HEq (φ.app (op A) a) (φ.app (op B) b) := by
    subst B
    exact heq_of_eq (congrArg (φ.app (op A)) (eq_of_heq h))
  have hrestrictHEq (P : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{max u v})
      {A B C : Opens X} (e : A = B) (hCA : C ≤ A) (hCB : C ≤ B)
      {a : P.obj (op A)} {b : P.obj (op B)} (h : HEq a b) :
      P.map (homOfLE hCA).op a = P.map (homOfLE hCB).op b := by
    subst B
    rw [eq_of_heq h]
  have hηmap (j k : I) (hjk : j ≤ k) (A : Opens (S j)) (a : (F j).obj.obj (op A)) :
      HEq ((G.map (homOfLE hjk)).hom.app (op ((Opens.map (p j)).obj A))
        ((η j).hom.app (op A) a))
        ((η k).hom.app (op ((Opens.map (f j k hjk)).obj A))
          ((alpha j k hjk).hom.app (op A) a)) := by
    have e : (Opens.map (p j)).obj A =
        (Opens.map (p k)).obj ((Opens.map (f j k hjk)).obj A) := by
      change _ = (Opens.map (p k ≫ f j k hjk)).obj A
      rw [hpcomp]
    have hh := hmapHEq _ _ (eG k).inv.hom e (hGmap j k hjk A a)
    have hi := ConcreteCategory.congr_hom
      (congrArg (fun q ↦ q.hom.app (op ((Opens.map (p j)).obj A)))
        (eG k).hom_inv_id)
      ((G.map (homOfLE hjk)).hom.app (op ((Opens.map (p j)).obj A))
        ((η j).hom.app (op A) a))
    change (eG k).inv.hom.app _ ((eG k).hom.hom.app _
      ((G.map (homOfLE hjk)).hom.app _ ((η j).hom.app (op A) a))) = _ at hi
    change HEq ((eG k).inv.hom.app _ ((eG k).hom.hom.app _
      ((G.map (homOfLE hjk)).hom.app _ ((η j).hom.app (op A) a))))
      ((η k).hom.app (op ((Opens.map (f j k hjk)).obj A))
        ((alpha j k hjk).hom.app (op A) a)) at hh
    rw [hi] at hh
    exact hh
  let PkD (t : Fin N) := (Opens.map (p k)).obj (D' t)
  have hDW (t : Fin N) : PkD t ≤ W (idx t) := by
    intro x hx
    exact (Set.ext_iff.mp (hpD t) x).mp hx
  have hDZ (t : Fin N) : PkD t ≤ Z := (hDW t).trans (hWZ (idx t))
  have hDAj (t : Fin N) : PkD t ≤ (Opens.map (p j)).obj (A (idx t)) :=
    (hDW t).trans (hWA (idx t))
  have hDAk (t : Fin N) : PkD t ≤
      (Opens.map (p k)).obj ((Opens.map (f j k hjk)).obj (A (idx t))) :=
    fun x hx ↦ hDA' t hx
  have hlocalD (t : Fin N) : (G.obj j).obj.map (homOfLE (hDZ t)).op s =
      (G.obj j).obj.map (homOfLE (hDAj t)).op
        ((η j).hom.app (op (A (idx t))) (a (idx t))) := by
    have h := congrArg ((G.obj j).obj.map (homOfLE (hDW t)).op) (he (idx t))
    simpa only [← ConcreteCategory.comp_apply, ← Functor.map_comp,
      ← op_comp, homOfLE_comp] using h
  let sk := (G.map (homOfLE hjk)).hom.app (op Z) s
  have hrep (t : Fin N) : (G.obj k).obj.map (homOfLE (hDZ t)).op sk =
      (η k).hom.app (op (D' t)) (r t) := by
    have h₁ := ConcreteCategory.congr_hom
      ((G.map (homOfLE hjk)).hom.naturality (homOfLE (hDZ t)).op) s
    have h₂ := ConcreteCategory.congr_hom
      ((G.map (homOfLE hjk)).hom.naturality (homOfLE (hDAj t)).op)
        ((η j).hom.app (op (A (idx t))) (a (idx t)))
    have h₃ := hrestrictHEq (G.obj k).obj
      (show (Opens.map (p j)).obj (A (idx t)) =
        (Opens.map (p k)).obj ((Opens.map (f j k hjk)).obj (A (idx t))) from by
        change _ = (Opens.map (p k ≫ f j k hjk)).obj (A (idx t))
        rw [hpcomp]) (hDAj t) (hDAk t) (hηmap j k hjk (A (idx t)) (a (idx t)))
    have h₄ := ConcreteCategory.congr_hom ((η k).hom.naturality
      (homOfLE (hDA' t)).op) ((alpha j k hjk).hom.app
        (op (A (idx t))) (a (idx t)))
    change (η k).hom.app (op (D' t)) (r t) =
      (G.obj k).obj.map (homOfLE (hDAk t)).op
        ((η k).hom.app (op ((Opens.map (f j k hjk)).obj (A (idx t))))
          ((alpha j k hjk).hom.app (op (A (idx t))) (a (idx t)))) at h₄
    exact h₁.symm.trans ((congrArg ((G.map (homOfLE hjk)).hom.app (op (PkD t)))
      (hlocalD t)).trans (h₂.trans (h₃.trans h₄.symm)))
  let Q (t : Fin N × Fin N) := D' t.1 ⊓ D' t.2
  let d (t : Fin N × Fin N) :=
    (F k).obj.map (homOfLE (show Q t ≤ D' t.1 from inf_le_left)).op (r t.1) -
      (F k).obj.map (homOfLE (show Q t ≤ D' t.2 from inf_le_right)).op (r t.2)
  have hQzero (t : Fin N × Fin N) : (η k).hom.app (op (Q t)) (d t) = 0 := by
    have h₁ := ConcreteCategory.congr_hom ((η k).hom.naturality
      (homOfLE (show Q t ≤ D' t.1 from inf_le_left)).op) (r t.1)
    have h₂ := ConcreteCategory.congr_hom ((η k).hom.naturality
      (homOfLE (show Q t ≤ D' t.2 from inf_le_right)).op) (r t.2)
    change (η k).hom.app (op (Q t)) (d t) = 0
    dsimp only [d]
    rw [map_sub]
    change _ - _ = 0
    change (η k).hom.app (op (Q t)) ((F k).obj.map (homOfLE inf_le_left).op (r t.1)) =
      (G.obj k).obj.map ((Opens.map (p k)).map (homOfLE inf_le_left)).op
        ((η k).hom.app (op (D' t.1)) (r t.1)) at h₁
    change (η k).hom.app (op (Q t)) ((F k).obj.map (homOfLE inf_le_right).op (r t.2)) =
      (G.obj k).obj.map ((Opens.map (p k)).map (homOfLE inf_le_right)).op
        ((η k).hom.app (op (D' t.2)) (r t.2)) at h₂
    have hQZ : (Opens.map (p k)).obj (Q t) ≤ Z :=
      fun x hx ↦ hDZ t.1 hx.1
    have hcomp₁ : (Opens.map (p k)).map
        (homOfLE (show Q t ≤ D' t.1 from inf_le_left)) ≫ homOfLE (hDZ t.1) =
        homOfLE hQZ := Subsingleton.elim _ _
    have hcomp₂ : (Opens.map (p k)).map
        (homOfLE (show Q t ≤ D' t.2 from inf_le_right)) ≫ homOfLE (hDZ t.2) =
        homOfLE hQZ := Subsingleton.elim _ _
    have hr₁ := congrArg ((G.obj k).obj.map ((Opens.map (p k)).map
      (homOfLE (show Q t ≤ D' t.1 from inf_le_left))).op) (hrep t.1)
    have hr₂ := congrArg ((G.obj k).obj.map ((Opens.map (p k)).map
      (homOfLE (show Q t ≤ D' t.2 from inf_le_right))).op) (hrep t.2)
    have hc₁ : (G.obj k).obj.map (homOfLE (hDZ t.1)).op ≫
        (G.obj k).obj.map ((Opens.map (p k)).map
          (homOfLE (show Q t ≤ D' t.1 from inf_le_left))).op =
        (G.obj k).obj.map (homOfLE hQZ).op := by
      rw [← Functor.map_comp, ← op_comp, hcomp₁]
    have hc₂ : (G.obj k).obj.map (homOfLE (hDZ t.2)).op ≫
        (G.obj k).obj.map ((Opens.map (p k)).map
          (homOfLE (show Q t ≤ D' t.2 from inf_le_right))).op =
        (G.obj k).obj.map (homOfLE hQZ).op := by
      rw [← Functor.map_comp, ← op_comp, hcomp₂]
    have he₁ := hr₁.symm.trans (ConcreteCategory.congr_hom hc₁ sk)
    have he₂ := hr₂.symm.trans (ConcreteCategory.congr_hom hc₂ sk)
    exact sub_eq_zero.mpr ((h₁.trans he₁).trans (h₂.trans he₂).symm)
  have hevent (t : Fin N × Fin N) :
      ∃ (l : I) (hkl : k ≤ l), (alpha k l hkl).hom.app (op (Q t)) (d t) = 0 := by
    have hunit : (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
        (Opens.map (p k)) AddCommGrpCat.{max u v} (Opens.grothendieckTopology (S k))
          (Opens.grothendieckTopology X)).unit.app (F k)).hom.app (op (Q t))) (d t) = 0 := by
      apply (ConcreteCategory.isIso_iff_bijective
        ((eG k).inv.hom.app (op ((Opens.map (p k)).obj (Q t))))).mp inferInstance |>.1
      change (η k).hom.app (op (Q t)) (d t) = _
      rw [map_zero]
      exact hQzero t
    exact spectralLimit_unit_eventually_zero S f hf hfid hfcomp X p hpcomp hlimit htop
      F alpha k (Q t)
        ((hDc t.1).2.inter_of_isOpen (hDc t.2).2 (hDc t.1).1 (hDc t.2).1)
          (d t) hunit
  choose l hkl hl using hevent
  obtain ⟨m, hm⟩ := ((Set.finite_range l).insert k).bddAbove
  have hkm : k ≤ m := hm (by simp)
  have hlm (t : Fin N × Fin N) : l t ≤ m :=
    hm (Set.mem_insert_of_mem _ (Set.mem_range_self t))
  have hzeroLate (t : Fin N × Fin N) :
      (alpha k m hkm).hom.app (op (Q t)) (d t) = 0 := by
    have hc := halpha_comp k (l t) m (hkl t) (hlm t) (Q t) (d t)
    rw [hl, map_zero] at hc
    have e : (Opens.map (f (l t) m (hlm t))).obj
        ((Opens.map (f k (l t) (hkl t))).obj (Q t)) =
        (Opens.map (f k m hkm)).obj (Q t) := by
      change (Opens.map (f (l t) m (hlm t) ≫ f k (l t) (hkl t))).obj (Q t) = _
      rw [hfcomp]
    have hzeroHEq (P : (Opens (S m))ᵒᵖ ⥤ AddCommGrpCat.{max u v})
        {A B : Opens (S m)} (h : A = B) :
        HEq (0 : P.obj (op A)) (0 : P.obj (op B)) := by subst B; rfl
    exact eq_of_heq (hc.symm.trans (hzeroHEq (F m).obj e))
  let Dm (t : Fin N) := (Opens.map (f k m hkm)).obj (D' t)
  let rm (t : Fin N) := (alpha k m hkm).hom.app (op (D' t)) (r t)
  have hcompat : Presheaf.IsCompatible (F m).obj Dm rm := by
    intro a b
    have hz := hzeroLate (a, b)
    change (alpha k m hkm).hom.app (op (D' a ⊓ D' b))
      ((F k).obj.map (homOfLE inf_le_left).op (r a) -
        (F k).obj.map (homOfLE inf_le_right).op (r b)) = 0 at hz
    rw [map_sub] at hz
    have h₁ := ConcreteCategory.congr_hom ((alpha k m hkm).hom.naturality
      (homOfLE (show D' a ⊓ D' b ≤ D' a from inf_le_left)).op) (r a)
    have h₂ := ConcreteCategory.congr_hom ((alpha k m hkm).hom.naturality
      (homOfLE (show D' a ⊓ D' b ≤ D' b from inf_le_right)).op) (r b)
    change (alpha k m hkm).hom.app (op (D' a ⊓ D' b))
        ((F k).obj.map (homOfLE inf_le_left).op (r a)) =
      (F m).obj.map (homOfLE (show Dm a ⊓ Dm b ≤ Dm a from inf_le_left)).op
        (rm a) at h₁
    change (alpha k m hkm).hom.app (op (D' a ⊓ D' b))
        ((F k).obj.map (homOfLE inf_le_right).op (r b)) =
      (F m).obj.map (homOfLE (show Dm a ⊓ Dm b ≤ Dm b from inf_le_right)).op
        (rm b) at h₂
    rw [h₁, h₂] at hz
    exact sub_eq_zero.mp hz
  let Um := (Opens.map (f i m ((hij.trans hjk).trans hkm))).obj U
  have hDk (t : Fin N) : D' t ≤
      (Opens.map (f j k hjk)).obj ((Opens.map (f i j hij)).obj U) := by
    intro x hx
    exact (Set.ext_iff.mp hDcover x).mpr (Set.mem_iUnion.mpr ⟨t, hx⟩)
  have hDmU (t : Fin N) : Dm t ≤ Um := by
    intro x hx
    have hu := hDk t hx
    change f i j hij (f j k hjk (f k m hkm x)) ∈ U at hu
    change f i m ((hij.trans hjk).trans hkm) x ∈ U
    have e₁ := ConcreteCategory.congr_hom (hfcomp j k m hjk hkm) x
    have e₂ := ConcreteCategory.congr_hom (hfcomp i j m hij (hjk.trans hkm)) x
    change f j k hjk (f k m hkm x) = f j m (hjk.trans hkm) x at e₁
    change f i j hij (f j m (hjk.trans hkm) x) = f i m ((hij.trans hjk).trans hkm) x at e₂
    rwa [e₁, e₂] at hu
  have hcoverm : Um ≤ ⨆ t, Dm t := by
    intro x hx
    change f i m ((hij.trans hjk).trans hkm) x ∈ U at hx
    have e : f i j hij (f j k hjk (f k m hkm x)) = f i m ((hij.trans hjk).trans hkm) x := by
      exact (congrArg (fun z ↦ f i j hij z)
        (ConcreteCategory.congr_hom (hfcomp j k m hjk hkm) x)).trans
          (ConcreteCategory.congr_hom (hfcomp i j m hij (hjk.trans hkm)) x)
    have hu : f k m hkm x ∈ f j k hjk ⁻¹'
        (((Opens.map (f i j hij)).obj U) : Set (S j)) := by
      change f i j hij (f j k hjk (f k m hkm x)) ∈ U
      rwa [e]
    obtain ⟨t, ht⟩ := Set.mem_iUnion.mp ((Set.ext_iff.mp hDcover (f k m hkm x)).mp hu)
    exact Opens.mem_iSup.mpr ⟨t, ht⟩
  obtain ⟨a, ha, _⟩ := (F m).existsUnique_gluing' Dm Um
    (fun t ↦ homOfLE (hDmU t)) hcoverm rm hcompat
  have hZeq : Z = (Opens.map (p m)).obj Um := by
    change _ = (Opens.map (p m ≫ f i m _)).obj U
    rw [hpcomp]
  have hpDm (t : Fin N) : (Opens.map (p m)).obj (Dm t) = PkD t := by
    change (Opens.map (p m ≫ f k m hkm)).obj (D' t) = _
    rw [hpcomp]
  have hPkDm (t : Fin N) : PkD t ≤ (Opens.map (p m)).obj (Dm t) := (hpDm t).symm.le
  have hPkU (t : Fin N) : PkD t ≤ (Opens.map (p m)).obj Um := by
    rw [← hZeq]
    exact hDZ t
  refine ⟨m, hjk.trans hkm, a, ?_⟩
  have hGcomp : (G.map (homOfLE (hjk.trans hkm))).hom.app (op Z) s =
      (G.map (homOfLE hkm)).hom.app (op Z) sk := by
    change (G.map (homOfLE hjk ≫ homOfLE hkm)).hom.app (op Z) s = _
    rw [G.map_comp]
    rfl
  rw [hGcomp]
  apply (G.obj m).eq_of_locally_eq' PkD Z (fun t ↦ homOfLE (hDZ t))
  · intro x hx
    obtain ⟨y, hyb, hy⟩ := Set.mem_iUnion₂.mp (hb hx)
    let t := (Fintype.equivFin ↥b) ⟨y, hyb⟩
    have ht : x ∈ W (idx t) := by
      change x ∈ (W (idx t) : Set X)
      have hi : idx t = y := by simp only [idx, t, Equiv.symm_apply_apply]
      rw [hi]
      exact hy
    exact Opens.mem_iSup.mpr ⟨t, (Set.ext_iff.mp (hpD t) x).mpr ht⟩
  · intro t
    have hn' := hn m ((hij.trans hjk).trans hkm) a
    change HEq (n m ((hij.trans hjk).trans hkm) a) ((η m).hom.app (op Um) a) at hn'
    have hnres := hrestrictHEq (G.obj m).obj hZeq (hDZ t) (hPkU t) hn'
    have hnatur := ConcreteCategory.congr_hom ((η m).hom.naturality
      (homOfLE (hDmU t)).op) a
    change (η m).hom.app (op (Dm t)) ((F m).obj.map (homOfLE (hDmU t)).op a) =
      (G.obj m).obj.map ((Opens.map (p m)).map (homOfLE (hDmU t))).op
        ((η m).hom.app (op Um) a) at hnatur
    rw [ha] at hnatur
    have hright : (G.obj m).obj.map (homOfLE (hDZ t)).op
        (n m ((hij.trans hjk).trans hkm) a) =
        (G.obj m).obj.map (homOfLE (hPkDm t)).op
          ((η m).hom.app (op (Dm t)) (rm t)) := by
      rw [hnres]
      have h := congrArg ((G.obj m).obj.map (homOfLE (hPkDm t)).op) hnatur
      have hh : homOfLE (hPkDm t) ≫
          (Opens.map (p m)).map (homOfLE (hDmU t)) = homOfLE (hPkU t) :=
        Subsingleton.elim _ _
      simpa only [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp, hh]
        using h.symm
    have hself (P : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{max u v})
        {A B : Opens X} (e : A = B) {a : P.obj (op A)} {b : P.obj (op B)}
        (h : HEq a b) : a = P.map (homOfLE e.le).op b := by
      subst B
      change a = P.map (𝟙 (op A)) b
      rw [P.map_id]
      exact eq_of_heq h
    have hres' := hself (G.obj m).obj (hpDm t).symm (hηmap k m hkm (D' t) (r t))
    have hnat := ConcreteCategory.congr_hom ((G.map (homOfLE hkm)).hom.naturality
      (homOfLE (hDZ t)).op) sk
    exact hnat.symm.trans ((congrArg ((G.map (homOfLE hkm)).hom.app (op (PkD t)))
      (hrep t)).trans (hres'.trans hright.symm))

end TopCat.Sheaf
