module

public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.Order.Directed

/-!
# Transitivity of colimits over directed pairs

Source: Stacks Project, Properties, Tag 0817, proof of
`lemma-integral-algebra-directed-colimit-finite`, final displayed colimit equality;
Categories, Tag 002F, supplies the universal property used in its expansion
(blueprint: lem-weil-pbc-directed-pairs-colimit-transitivity).
-/

@[expose] public section

universe v u wI wK

open CategoryTheory

namespace CategoryTheory.Limits

/-- Colimits over a preorder of pairs are computed from the given fiber colimits
and the base colimit, without choosing transition functors between the fibers.
The natural transformation `b i` packages the maps from the `i`th fiber to `B.obj i`.
The resulting `a` has exactly the composite legs, and its universal property also
makes the canonical map from any chosen colimit of `D` an isomorphism.

Source: Stacks Project, Properties, Tag 0817, proof of
`lemma-integral-algebra-directed-colimit-finite`, final displayed equality,
expanded using Categories, Tag 002F
(blueprint: lem-weil-pbc-directed-pairs-colimit-transitivity).

Proof:
1. The hypotheses `hproj` and `hinc` give the projection and fiber inclusion functors.
   Compatibility and the cocone identity for `c` show that the composite legs form
   a natural transformation `a : D ⟶ (Functor.const _).obj c.pt`.
2. Given any cocone on `D`, restrict it along each fiber inclusion. The assumed
   fiber colimit gives a unique map `u_i : B.obj i ⟶ M` factoring those legs.
3. For `i ≤ j` and `k : K i`, use `hlift` to find an upper pair in the `j`th fiber.
   Compatibility and the given cocone equation show that `u_i` and
   `B.map (homOfLE hij) ≫ u_j` agree after every leg of the `i`th fiber.
   Fiber-colimit uniqueness makes these maps equal, so the `u_i` form a cocone on `B`.
4. The colimit property of `c` gives a map `c.pt ⟶ M` factoring every composite leg.
5. Any other such map agrees with this one after each base leg, first by fiber
   uniqueness, and then equals it by base-colimit uniqueness. Thus the composite
   cocone is colimiting. Steps 1--5 use def-weil-pbc-category-colimit.
6. For any chosen colimit `d` of `D`, its canonical map to this composite cocone
   and the reverse universal map have identity composites: check their legs and
   use colimit uniqueness (def-weil-pbc-category-colimit). Hence the map is invertible. -/
theorem directedPairs_colimit_transitivity
    {C : Type u} [Category.{v} C]
    {I : Type wI} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    {K : I → Type wK} [∀ i, Preorder (K i)] [∀ i, Nonempty (K i)]
    [∀ i, IsDirected (K i) (· ≤ ·)] [Preorder (Σ i, K i)]
    (hproj : Monotone (fun p : Σ i, K i ↦ p.1))
    (hinc : ∀ i, Monotone (Sigma.mk i : K i → Σ j, K j))
    (hlift : ∀ (i j : I), i ≤ j → ∀ k : K i,
      ∃ l : K j, (⟨i, k⟩ : Σ r, K r) ≤ ⟨j, l⟩)
    (D : (Σ i, K i) ⥤ C) (B : I ⥤ C)
    (b : ∀ i, (hinc i).functor ⋙ D ⟶ (Functor.const (K i)).obj (B.obj i))
    (hcompat : ∀ (p q : Σ i, K i) (h : p ≤ q),
      D.map (homOfLE h) ≫ (b q.1).app q.2 =
        (b p.1).app p.2 ≫ B.map (homOfLE (hproj h)))
    (hfiber : ∀ i, IsColimit (Cocone.mk (B.obj i) (b i)))
    (c : Cocone B) (hc : IsColimit c) :
    ∃ a : D ⟶ (Functor.const (Σ i, K i)).obj c.pt,
      (∀ p : Σ i, K i, a.app p = (b p.1).app p.2 ≫ c.ι.app p.1) ∧
      Nonempty (IsColimit (Cocone.mk c.pt a)) ∧
      ∀ (d : Cocone D) (hd : IsColimit d), IsIso (hd.desc (Cocone.mk c.pt a)) := by
  let a : D ⟶ (Functor.const (Σ i, K i)).obj c.pt :=
    { app := fun p ↦ (b p.1).app p.2 ≫ c.ι.app p.1
      naturality := by
        rintro ⟨i, k⟩ ⟨j, l⟩ ⟨⟨hij⟩⟩
        change D.map (homOfLE hij) ≫ ((b j).app l ≫ c.ι.app j) =
          ((b i).app k ≫ c.ι.app i) ≫ 𝟙 _
        rw [Category.comp_id, ← Category.assoc, hcompat ⟨i, k⟩ ⟨j, l⟩ hij,
          Category.assoc, c.w] }
  let base (s : Cocone D) : Cocone B :=
    { pt := s.pt
      ι :=
        { app := fun i ↦ (hfiber i).desc (s.whisker (hinc i).functor)
          naturality := by
            intro i j f
            change B.map f ≫ (hfiber j).desc (s.whisker (hinc j).functor) =
              (hfiber i).desc (s.whisker (hinc i).functor) ≫ 𝟙 _
            rw [Category.comp_id]
            apply (hfiber i).hom_ext
            intro k
            obtain ⟨l, hkl⟩ := hlift i j (leOfHom f) k
            change (b i).app k ≫
                (B.map f ≫ (hfiber j).desc (s.whisker (hinc j).functor)) =
              (b i).app k ≫ (hfiber i).desc (s.whisker (hinc i).functor)
            calc
              _ = (D.map (homOfLE hkl) ≫ (b j).app l) ≫
                  (hfiber j).desc (s.whisker (hinc j).functor) := by
                have hf : homOfLE (hproj hkl) = f := Subsingleton.elim _ _
                rw [hcompat ⟨i, k⟩ ⟨j, l⟩ hkl, hf, Category.assoc]
              _ = s.ι.app ⟨i, k⟩ := by
                rw [Category.assoc, (hfiber j).fac]
                exact s.w (homOfLE hkl)
              _ = (b i).app k ≫ (hfiber i).desc (s.whisker (hinc i).functor) :=
                ((hfiber i).fac (s.whisker (hinc i).functor) k).symm } }
  have ha : IsColimit (Cocone.mk c.pt a) :=
    { desc := fun s ↦ hc.desc (base s)
      fac := by
        intro s p
        change ((b p.1).app p.2 ≫ c.ι.app p.1) ≫ hc.desc (base s) = s.ι.app p
        rw [Category.assoc, hc.fac]
        exact (hfiber p.1).fac (s.whisker (hinc p.1).functor) p.2
      uniq := by
        intro s m hm
        apply hc.uniq (base s) m
        intro i
        apply (hfiber i).hom_ext
        intro k
        change (b i).app k ≫ (c.ι.app i ≫ m) =
          (b i).app k ≫ (hfiber i).desc (s.whisker (hinc i).functor)
        rw [(hfiber i).fac]
        change (b i).app k ≫ (c.ι.app i ≫ m) = s.ι.app ⟨i, k⟩
        exact (Category.assoc _ _ _).symm.trans (hm ⟨i, k⟩) }
  refine ⟨a, fun _ ↦ rfl, ⟨ha⟩, ?_⟩
  intro d hd
  exact hd.nonempty_isColimit_iff_isIso_desc.mp ⟨ha⟩

end CategoryTheory.Limits
