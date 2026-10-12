module

public import Mathlib.Topology.Sheaves.Sheaf
import Mathlib.Topology.Sheaves.Skyscraper
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
import Mathlib.CategoryTheory.Limits.Types.Filtered

/-!
# Sections of directed colimits of sheaves over quasi-compact opens

Source: Stacks Project, Sheaves, Lemma 009F (parts (2) and (4));
(blueprint: lem-weil-pbc-sheaves-directed-colimit-sections).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace TopCat

/-- The canonical section maps of Stacks 009F.
Evaluate the sheaf colimit cocone at each open, and use the universal property
of the colimit of sets. The coprojection equation is `colimit.ι_desc`.
(blueprint: aux-directed-colimit-map) -/
theorem directedColimit_sections_map
    (X : TopCat.{u}) (I : Type u) [Preorder I] [Nonempty I]
    [IsDirected I (· ≤ ·)]
    (D : I ⥤ TopCat.Sheaf (Type u) X) [HasColimit D] :
    ∃ Ψ : ∀ (U : Opens X),
        colimit (D ⋙ (TopCat.Sheaf.forget (Type u) X) ⋙
          (evaluation (Opens X)ᵒᵖ (Type u)).obj (op U)) ⟶
          (colimit D).obj.obj (op U),
      ∀ (U : Opens X) (i : I) (s : (D.obj i).obj.obj (op U)),
        Ψ U (colimit.ι (D ⋙ (TopCat.Sheaf.forget (Type u) X) ⋙
          (evaluation (Opens X)ᵒᵖ (Type u)).obj (op U)) i s) =
          (colimit.ι D i).1.app (op U) s := by
  let E := fun U : Opens X ↦
    (TopCat.Sheaf.forget (Type u) X) ⋙
      (evaluation (Opens X)ᵒᵖ (Type u)).obj (op U)
  refine ⟨fun U ↦ colimit.desc (D ⋙ E U) ((E U).mapCocone (colimit.cocone D)), ?_⟩
  intro U i s
  exact congrArg (fun f ↦ f s) (colimit.ι_desc ((E U).mapCocone (colimit.cocone D)) i)

-- Equality of colimit sections becomes equality at one stage on a neighborhood.
private theorem colimit_sections_locally_eventually_equal
    (X : TopCat.{u}) (I : Type u) [Preorder I] [Nonempty I]
    [IsDirected I (· ≤ ·)]
    (D : I ⥤ TopCat.Sheaf (Type u) X) [HasColimit D]
    (U : Opens X) (i i' : I) (s : (D.obj i).obj.obj (op U))
    (s' : (D.obj i').obj.obj (op U))
    (h : (colimit.ι D i).1.app (op U) s = (colimit.ι D i').1.app (op U) s')
    (x : X) (hx : x ∈ U) :
    ∃ (V : Opens X) (_ : x ∈ V) (hVU : V ≤ U)
      (k : I) (hi : i ≤ k) (hi' : i' ≤ k),
      (D.obj k).obj.map (homOfLE hVU).op ((D.map (homOfLE hi)).1.app (op U) s) =
        (D.obj k).obj.map (homOfLE hVU).op ((D.map (homOfLE hi')).1.app (op U) s') := by
  let S := TopCat.Sheaf.forget (Type u) X ⋙ Presheaf.stalkFunctor (Type u) x
  have he : (S.map (colimit.ι D i)) ((Presheaf.germ (D.obj i).obj) U x hx s) =
      (S.map (colimit.ι D i')) ((Presheaf.germ (D.obj i').obj) U x hx s') := by
    change (Presheaf.stalkFunctor (Type u) x).map (colimit.ι D i).1
        ((Presheaf.germ (D.obj i).obj) U x hx s) =
      (Presheaf.stalkFunctor (Type u) x).map (colimit.ι D i').1
        ((Presheaf.germ (D.obj i').obj) U x hx s')
    rw [Presheaf.stalkFunctor_map_germ_apply, Presheaf.stalkFunctor_map_germ_apply]
    exact congrArg ((Presheaf.germ (colimit D).obj) U x hx) h
  obtain ⟨k, f, g, hk⟩ :=
    (Types.FilteredColimit.isColimit_eq_iff (D ⋙ S)
      (isColimitOfPreserves S (colimit.isColimit D))).mp he
  have hk' : (Presheaf.germ (D.obj k).obj) U x hx ((D.map f).1.app (op U) s) =
      (Presheaf.germ (D.obj k).obj) U x hx ((D.map g).1.app (op U) s') := by
    change (Presheaf.stalkFunctor (Type u) x).map (D.map f).1
        ((Presheaf.germ (D.obj i).obj) U x hx s) =
      (Presheaf.stalkFunctor (Type u) x).map (D.map g).1
        ((Presheaf.germ (D.obj i').obj) U x hx s') at hk
    rw [Presheaf.stalkFunctor_map_germ_apply, Presheaf.stalkFunctor_map_germ_apply] at hk
    exact hk
  obtain ⟨V, hxV, a, b, hab⟩ := Presheaf.germ_eq (D.obj k).obj x hx hx _ _ hk'
  exact ⟨V, hxV, a.le, k, f.le, g.le, hab⟩

-- A finite subcover lets us choose one upper bound for the local stages.
private theorem colimit_sections_eventually_equal
    (X : TopCat.{u}) (I : Type u) [Preorder I] [Nonempty I]
    [IsDirected I (· ≤ ·)]
    (D : I ⥤ TopCat.Sheaf (Type u) X) [HasColimit D]
    (U : Opens X) (hU : IsCompact (U : Set X))
    (i i' : I) (s : (D.obj i).obj.obj (op U))
    (s' : (D.obj i').obj.obj (op U))
    (h : (colimit.ι D i).1.app (op U) s = (colimit.ι D i').1.app (op U) s') :
    ∃ (k : I) (hi : i ≤ k) (hi' : i' ≤ k),
      (D.map (homOfLE hi)).1.app (op U) s =
        (D.map (homOfLE hi')).1.app (op U) s' := by
  classical
  have hlocal := fun x : U ↦
    colimit_sections_locally_eventually_equal X I D U i i' s s' h x x.property
  choose V hxV hVU k hi hi' he using hlocal
  obtain ⟨t, ht⟩ := hU.elim_finite_subcover (fun x : U ↦ (V x : Set X))
    (fun x ↦ (V x).isOpen) (by
      intro x hx
      exact Set.mem_iUnion.mpr ⟨⟨x, hx⟩, hxV ⟨x, hx⟩⟩)
  obtain ⟨l, hl⟩ := (((t.finite_toSet.image k).insert i).insert i').bddAbove
  have hil : i ≤ l := hl (by simp)
  have hi'l : i' ≤ l := hl (by simp)
  have hkl (x : t) : k x ≤ l := hl (by
    apply Set.mem_insert_of_mem
    apply Set.mem_insert_of_mem
    exact ⟨x, x.property, rfl⟩)
  refine ⟨l, hil, hi'l, ?_⟩
  apply (D.obj l).eq_of_locally_eq' (fun x : t ↦ V x) U
    (fun x ↦ homOfLE (hVU x))
  · intro x hx
    obtain ⟨y, hyt, hy⟩ := Set.mem_iUnion₂.mp (ht hx)
    exact Opens.mem_iSup.mpr ⟨⟨y, hyt⟩, hy⟩
  · intro x
    have e := congrArg ((D.map (homOfLE (hkl x))).1.app (op (V x))) (he x)
    simpa only [← NatTrans.naturality_apply, ← types_comp_apply, Category.assoc,
      ← NatTrans.comp_app, ← ObjectProperty.FullSubcategory.comp_hom,
      ← Functor.map_comp, homOfLE_comp] using e

/-- Compact-open injectivity, from Stacks 009F(2), using 009E(5).
Equality of images gives equality of germs. Stalks preserve sheaf colimits,
so filtered-colimit equality gives a common stage at each point. Equality
of germs gives a neighborhood of agreement. A finite subcover and a common
upper bound give global equality by sheaf separation. Finally represent
arbitrary colimit elements by sections to prove injectivity of the map.
(blueprint: aux-directed-colimit-injective) -/
theorem directedColimit_sections_injective
    (X : TopCat.{u}) (I : Type u) [Preorder I] [Nonempty I]
    [IsDirected I (· ≤ ·)]
    (D : I ⥤ TopCat.Sheaf (Type u) X) [HasColimit D]
    (Ψ : ∀ (U : Opens X),
      colimit (D ⋙ (TopCat.Sheaf.forget (Type u) X) ⋙
        (evaluation (Opens X)ᵒᵖ (Type u)).obj (op U)) ⟶
        (colimit D).obj.obj (op U))
    (hΨ : ∀ (U : Opens X) (i : I) (s : (D.obj i).obj.obj (op U)),
      Ψ U (colimit.ι (D ⋙ (TopCat.Sheaf.forget (Type u) X) ⋙
        (evaluation (Opens X)ᵒᵖ (Type u)).obj (op U)) i s) =
        (colimit.ι D i).1.app (op U) s) :
    ∀ (U : Opens X), IsCompact (U : Set X) →
      Function.Injective (Ψ U) ∧
      (∀ (i i' : I) (s : (D.obj i).obj.obj (op U))
          (s' : (D.obj i').obj.obj (op U)),
        (colimit.ι D i).1.app (op U) s =
            (colimit.ι D i').1.app (op U) s' →
          ∃ (i'' : I) (hi : i ≤ i'') (hi' : i' ≤ i''),
            (D.map (homOfLE hi)).1.app (op U) s =
              (D.map (homOfLE hi')).1.app (op U) s') := by
  intro U hU
  have he := colimit_sections_eventually_equal X I D U hU
  refine ⟨?_, he⟩
  intro a b hab
  let E := D ⋙ TopCat.Sheaf.forget (Type u) X ⋙
    (evaluation (Opens X)ᵒᵖ (Type u)).obj (op U)
  obtain ⟨i, s, rfl⟩ := Types.jointly_surjective E (colimit.isColimit E) a
  obtain ⟨i', s', rfl⟩ := Types.jointly_surjective E (colimit.isColimit E) b
  have hab' : (colimit.ι D i).1.app (op U) s =
      (colimit.ι D i').1.app (op U) s' :=
    (hΨ U i s).symm.trans (hab.trans (hΨ U i' s'))
  obtain ⟨k, hi, hi', hk⟩ := he i i' s s' hab'
  exact (Types.FilteredColimit.colimit_eq_iff E).mpr
    ⟨k, homOfLE hi, homOfLE hi', hk⟩

-- Stalks preserve the sheaf colimit, so sections lift at one stage locally.
private theorem colimit_sections_locally_lift
    (X : TopCat.{u}) (I : Type u) [Preorder I] [Nonempty I]
    [IsDirected I (· ≤ ·)]
    (D : I ⥤ TopCat.Sheaf (Type u) X) [HasColimit D]
    (U : Opens X) (t : (colimit D).obj.obj (op U)) (x : X) (hx : x ∈ U) :
    ∃ (V : Opens X) (_ : x ∈ V) (hVU : V ≤ U)
      (i : I) (s : (D.obj i).obj.obj (op V)),
      (colimit.ι D i).1.app (op V) s =
        (colimit D).obj.map (homOfLE hVU).op t := by
  let S := TopCat.Sheaf.forget (Type u) X ⋙ Presheaf.stalkFunctor (Type u) x
  obtain ⟨i, a, ha⟩ := Types.jointly_surjective (D ⋙ S)
    (isColimitOfPreserves S (colimit.isColimit D))
    ((Presheaf.germ (colimit D).obj) U x hx t)
  obtain ⟨V, hxV, s, hs⟩ := Presheaf.exists_germ_eq (D.obj i).obj a
  have he : (Presheaf.germ (colimit D).obj) V x hxV
      ((colimit.ι D i).1.app (op V) s) =
      (Presheaf.germ (colimit D).obj) U x hx t := by
    rw [← Presheaf.stalkFunctor_map_germ_apply, hs]
    exact ha
  obtain ⟨W, hxW, f, g, he⟩ :=
    Presheaf.germ_eq (colimit D).obj x hxV hx _ _ he
  refine ⟨W, hxW, g.le, i, (D.obj i).obj.map f.op s, ?_⟩
  rw [NatTrans.naturality_apply]
  exact he

/-- Finite-cover bijectivity, from Stacks 009F(4), using 009E(5).
The finite-refinement hypothesis implies compactness, hence injectivity.
Stalk-colimit representability and equality of germs give local section lifts.
Refine their cover to the finite cover with compact overlaps. On each overlap,
compact-open eventual equality supplies a stage of agreement. Choose an upper
bound for all local stages and overlap stages, then glue in that sheaf. The
image of the glued section equals the original section by sheaf separation.
(blueprint: aux-directed-colimit-surjective) -/
theorem directedColimit_sections_surjective
    (X : TopCat.{u}) (I : Type u) [Preorder I] [Nonempty I]
    [IsDirected I (· ≤ ·)]
    (D : I ⥤ TopCat.Sheaf (Type u) X) [HasColimit D]
    (Ψ : ∀ (U : Opens X),
      colimit (D ⋙ (TopCat.Sheaf.forget (Type u) X) ⋙
        (evaluation (Opens X)ᵒᵖ (Type u)).obj (op U)) ⟶
        (colimit D).obj.obj (op U))
    (hΨ : ∀ (U : Opens X) (i : I) (s : (D.obj i).obj.obj (op U)),
      Ψ U (colimit.ι (D ⋙ (TopCat.Sheaf.forget (Type u) X) ⋙
        (evaluation (Opens X)ᵒᵖ (Type u)).obj (op U)) i s) =
        (colimit.ι D i).1.app (op U) s) :
    ∀ (U : Opens X),
      (∀ (K : Type u) (V : K → Opens X),
        (∀ x : X, x ∈ U → ∃ k, x ∈ V k) →
        ∃ (J : Type u) (_ : Fintype J) (W : J → Opens X),
          (∀ x : X, x ∈ U → ∃ j, x ∈ W j) ∧
          (∀ j, ∃ k, W j ≤ V k) ∧
          (∀ j j', IsCompact (((W j ⊓ W j') : Opens X) : Set X))) →
      Function.Bijective (Ψ U) ∧
        (∀ t, ∃ (i : I) (s : (D.obj i).obj.obj (op U)),
          Ψ U (colimit.ι (D ⋙ (TopCat.Sheaf.forget (Type u) X) ⋙
            (evaluation (Opens X)ᵒᵖ (Type u)).obj (op U)) i s) = t) := by
  classical
  intro U hU
  have hcompact : IsCompact (U : Set X) := by
    apply isCompact_of_finite_subcover
    intro K V hV hcover
    obtain ⟨J, hJ, W, hWcover, hWV, _⟩ :=
      hU K (fun k ↦ ⟨V k, hV k⟩) (fun x hx ↦ Set.mem_iUnion.mp (hcover hx))
    choose q hq using hWV
    refine ⟨Finset.univ.image q, ?_⟩
    intro x hx
    obtain ⟨j, hj⟩ := hWcover x hx
    exact Set.mem_iUnion₂.mpr ⟨q j, Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩,
      hq j hj⟩
  have hinj := (directedColimit_sections_injective X I D Ψ hΨ U hcompact).1
  have hrep : ∀ t : (colimit D).obj.obj (op U),
      ∃ (i : I) (s : (D.obj i).obj.obj (op U)), (colimit.ι D i).1.app (op U) s = t := by
    intro t
    have hlocal := fun x : U ↦ colimit_sections_locally_lift X I D U t x x.property
    choose V hxV hVU i s hs using hlocal
    obtain ⟨J, hJ, W, hWcover, hWV, hWcompact⟩ :=
      hU U V (fun x hx ↦ ⟨⟨x, hx⟩, hxV ⟨x, hx⟩⟩)
    choose q hq using hWV
    let ij : J → I := fun j ↦ i (q j)
    have hWU (j : J) : W j ≤ U := (hq j).trans (hVU (q j))
    let sj (j : J) : (D.obj (ij j)).obj.obj (op (W j)) :=
      (D.obj (ij j)).obj.map (homOfLE (hq j)).op (s (q j))
    have hc (j : J) : (colimit.ι D (ij j)).1.app (op (W j)) (sj j) =
        (colimit D).obj.map (homOfLE (hWU j)).op t := by
      dsimp [sj, ij]
      rw [NatTrans.naturality_apply, hs]
      simp only [← types_comp_apply, ← Functor.map_comp, ← op_comp, homOfLE_comp]
    have hoverlap (j j' : J) :
        (colimit.ι D (ij j)).1.app (op (W j ⊓ W j'))
            ((D.obj (ij j)).obj.map (Opens.infLELeft (W j) (W j')).op (sj j)) =
          (colimit.ι D (ij j')).1.app (op (W j ⊓ W j'))
            ((D.obj (ij j')).obj.map (Opens.infLERight (W j) (W j')).op (sj j')) := by
      rw [NatTrans.naturality_apply (colimit.ι D (ij j)).1
        (Opens.infLELeft (W j) (W j')).op (sj j), hc j,
        NatTrans.naturality_apply (colimit.ι D (ij j')).1
        (Opens.infLERight (W j) (W j')).op (sj j'), hc j']
      simp only [← types_comp_apply, ← Functor.map_comp, ← op_comp]
      rfl
    have hevent (j j' : J) := colimit_sections_eventually_equal X I D
      (W j ⊓ W j') (hWcompact j j') (ij j) (ij j') _ _ (hoverlap j j')
    choose k hik hi'k he using hevent
    obtain ⟨l, hl⟩ := ((Set.finite_range ij).union
      (Set.finite_range (fun p : J × J ↦ k p.1 p.2))).bddAbove
    have hil (j : J) : ij j ≤ l := hl (Or.inl ⟨j, rfl⟩)
    have hkl (j j' : J) : k j j' ≤ l := hl (Or.inr ⟨(j, j'), rfl⟩)
    let sl (j : J) : (D.obj l).obj.obj (op (W j)) :=
      (D.map (homOfLE (hil j))).1.app (op (W j)) (sj j)
    have hcompat : Presheaf.IsCompatible (D.obj l).obj W sl := by
      intro j j'
      have e := congrArg ((D.map (homOfLE (hkl j j'))).1.app (op (W j ⊓ W j')))
        (he j j')
      simpa only [sl, ← NatTrans.naturality_apply, ← types_comp_apply, Category.assoc,
        ← NatTrans.comp_app, ← ObjectProperty.FullSubcategory.comp_hom,
        ← Functor.map_comp, homOfLE_comp] using e
    obtain ⟨a, ha, _⟩ := (D.obj l).existsUnique_gluing' W U
      (fun j ↦ homOfLE (hWU j)) (by
        intro x hx
        obtain ⟨j, hj⟩ := hWcover x hx
        exact Opens.mem_iSup.mpr ⟨j, hj⟩) sl hcompat
    refine ⟨l, a, ?_⟩
    apply (colimit D).eq_of_locally_eq' W U (fun j ↦ homOfLE (hWU j)) (by
      intro x hx
      obtain ⟨j, hj⟩ := hWcover x hx
      exact Opens.mem_iSup.mpr ⟨j, hj⟩)
    intro j
    rw [← NatTrans.naturality_apply, ha]
    dsimp [sl]
    have hw := congrArg (fun f ↦ f.1.app (op (W j)) (sj j))
      (colimit.w D (homOfLE (hil j)))
    exact hw.trans (hc j)
  refine ⟨⟨hinj, ?_⟩, ?_⟩
  · intro t
    obtain ⟨i, s, hs⟩ := hrep t
    exact ⟨colimit.ι (D ⋙ TopCat.Sheaf.forget (Type u) X ⋙
      (evaluation (Opens X)ᵒᵖ (Type u)).obj (op U)) i s, (hΨ U i s).trans hs⟩
  · intro t
    obtain ⟨i, s, hs⟩ := hrep t
    exact ⟨i, s, (hΨ U i s).trans hs⟩

/-- Source: Stacks Project, Sheaves, Lemma 009F, parts (2) and (4)
(blueprint: lem-weil-pbc-sheaves-directed-colimit-sections).
Evaluate the colimit cocone to obtain the canonical maps. Stalks preserve
sheaf colimits (Stacks 009E(5)); equality and lifting of germs therefore give
local eventual equality and local lifts. Compactness makes the equality
uniform in one stage. For surjectivity, refine local lifts by the stated
finite coverings, use eventual equality on compact pairwise intersections,
and glue in one stage. The three auxiliary theorems establish these clauses.
-/
theorem sheaves_directedColimit_sections
    (X : TopCat.{u}) (I : Type u) [Preorder I] [Nonempty I]
    [IsDirected I (· ≤ ·)]
    (D : I ⥤ TopCat.Sheaf (Type u) X) [HasColimit D] :
    ∃ Ψ : ∀ (U : Opens X),
        colimit (D ⋙ (TopCat.Sheaf.forget (Type u) X) ⋙
          (evaluation (Opens X)ᵒᵖ (Type u)).obj (op U)) ⟶
          (colimit D).obj.obj (op U),
      (∀ (U : Opens X) (i : I) (s : (D.obj i).obj.obj (op U)),
        Ψ U (colimit.ι (D ⋙ (TopCat.Sheaf.forget (Type u) X) ⋙
          (evaluation (Opens X)ᵒᵖ (Type u)).obj (op U)) i s) =
          (colimit.ι D i).1.app (op U) s) ∧
      (∀ (U : Opens X), IsCompact (U : Set X) →
        Function.Injective (Ψ U) ∧
        (∀ (i i' : I) (s : (D.obj i).obj.obj (op U))
            (s' : (D.obj i').obj.obj (op U)),
          (colimit.ι D i).1.app (op U) s =
              (colimit.ι D i').1.app (op U) s' →
            ∃ (i'' : I) (hi : i ≤ i'') (hi' : i' ≤ i''),
              (D.map (homOfLE hi)).1.app (op U) s =
                (D.map (homOfLE hi')).1.app (op U) s')) ∧
      (∀ (U : Opens X),
        (∀ (K : Type u) (V : K → Opens X),
          (∀ x : X, x ∈ U → ∃ k, x ∈ V k) →
          ∃ (J : Type u) (_ : Fintype J) (W : J → Opens X),
            (∀ x : X, x ∈ U → ∃ j, x ∈ W j) ∧
            (∀ j, ∃ k, W j ≤ V k) ∧
            (∀ j j', IsCompact (((W j ⊓ W j') : Opens X) : Set X))) →
        Function.Bijective (Ψ U) ∧
          (∀ t, ∃ (i : I) (s : (D.obj i).obj.obj (op U)),
            Ψ U (colimit.ι (D ⋙ (TopCat.Sheaf.forget (Type u) X) ⋙
              (evaluation (Opens X)ᵒᵖ (Type u)).obj (op U)) i s) = t)) := by
  obtain ⟨Ψ, hΨ⟩ := directedColimit_sections_map X I D
  refine ⟨Ψ, hΨ, ?_, ?_⟩
  · intro U hU
    exact directedColimit_sections_injective X I D Ψ hΨ U hU
  · intro U hU
    exact directedColimit_sections_surjective X I D Ψ hΨ U hU

end TopCat
