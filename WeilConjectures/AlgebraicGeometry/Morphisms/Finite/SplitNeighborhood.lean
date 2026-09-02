/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import WeilConjectures.AlgebraicGeometry.Morphisms.Finite.GeometricFiber
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint

/-!
# Split étale neighbourhoods of a geometric point, for a finite morphism

Let `f : X ⟶ Y` be a finite morphism and `y : Spec Ω ⟶ Y` a geometric point with `Ω`
algebraically closed. A pointed étale neighbourhood `(U, u)` of `y` is *split* if the base
change `U ×_Y X` decomposes as a disjoint union of open and closed subschemes `piece t` indexed
by the geometric points `t` of `X` over `y`, with `piece t` containing the point `(u, t)`.
The split neighbourhoods form a category `AlgebraicGeometry.Scheme.Hom.SplitNeighborhood f y`,
whose morphisms are the morphisms of pointed étale neighbourhoods carrying each piece into the
corresponding piece. It comes with the forgetful functor to the pointed étale neighbourhoods
of `y` and, for every `t`, with the functor `SplitNeighborhood.pieceFunctor t` to the pointed
étale neighbourhoods of `t` in `X` sending a split neighbourhood to its `t`-th piece.

This file sets up these categories and functors, shows that decompositions pull back along
morphisms of neighbourhoods (`SplitNeighborhood.pullbackDec`) and proves the shrinking lemma:
an open and closed subscheme of `U ×_Y X` containing none of the points `(u, t)` becomes empty
after shrinking `U` (`AlgebraicGeometry.Scheme.Hom.exists_hom_preimage_eq_bot`).

## Main definitions

- `AlgebraicGeometry.Scheme.Hom.basePt`: the point `(u, t)` of `U ×_Y X`.
- `AlgebraicGeometry.Scheme.Hom.SplitNeighborhood`: the category of split neighbourhoods.
- `AlgebraicGeometry.Scheme.Hom.SplitNeighborhood.forget`: the forgetful functor.
- `AlgebraicGeometry.Scheme.Hom.SplitNeighborhood.pieceFunctor`: the `t`-th piece, as a functor
  to the pointed étale neighbourhoods of `t`.

-/

@[expose] public section

universe u

noncomputable section

open CategoryTheory Limits Opposite TopologicalSpace

namespace AlgebraicGeometry.Scheme.Hom

variable {X Y : Scheme.{u}} (f : X ⟶ Y) {Ω : Type u} [Field Ω]

section SepClosed

variable [IsSepClosed Ω] {y : Spec (.of Ω) ⟶ Y}

/-- The point `(u, t)` of `U ×_Y X`, for a pointed étale neighbourhood `(U, u)` of `y` and a
geometric point `t` of `X` over `y`: the morphism into the fibre product induced by the
commutative square
```
Spec Ω ------t.1------→ X
   |                    |
   u = c.2.left         f
   ↓                    ↓
   U -----c.1.hom-----→ Y
```
-/
def basePt (c : EtaleNeighborhood y) (t : GeometricFiber f y) :
    Spec (.of Ω) ⟶ pullback c.1.hom f :=
  pullback.lift c.2.left t.1 ((CategoryTheory.Over.w c.2).trans t.2.symm)

@[reassoc (attr := simp)]
lemma basePt_fst (c : EtaleNeighborhood y) (t : GeometricFiber f y) :
    basePt f c t ≫ pullback.fst c.1.hom f = c.2.left :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma basePt_snd (c : EtaleNeighborhood y) (t : GeometricFiber f y) :
    basePt f c t ≫ pullback.snd c.1.hom f = t.1 :=
  pullback.lift_snd _ _ _

/-- The points `(u, t)` are compatible with morphisms of pointed étale neighbourhoods: the
triangle
```
                       Spec Ω
                     ╱        ╲
  basePt f c t     ╱            ╲    basePt f c' t
                 ↙                ↘
      U ×_Y X ──(f.Etale.map g.val).left──→ U' ×_Y X
```
commutes. -/
@[reassoc (attr := simp)]
lemma basePt_comp_etale_map_left {c c' : EtaleNeighborhood y} (g : c ⟶ c')
    (t : GeometricFiber f y) : basePt f c t ≫ (f.Etale.map g.val).left = basePt f c' t := by
  apply pullback.hom_ext
  · rw [Category.assoc, Hom.etale_map_left_comp_fst, basePt_fst_assoc, basePt_fst]
    exact congrArg CategoryTheory.Over.Hom.left g.property
  · rw [Category.assoc, Hom.etale_map_left_comp_snd, basePt_snd, basePt_snd]

variable (y) in
/-- A pointed étale neighbourhood `(U, u)` of `y` together with a decomposition of `U ×_Y X`
into pairwise disjoint opens indexed by the geometric points `t` of `X` over `y`, the `t`-th
piece containing the point `(u, t)`. The pieces are automatically closed as well, see
`AlgebraicGeometry.Scheme.Hom.SplitNeighborhood.isClopen`. -/
structure SplitNeighborhood where
  /-- The underlying pointed étale neighbourhood of `y`. -/
  obj : EtaleNeighborhood y
  /-- The pieces of the decomposition of `U ×_Y X`. -/
  piece : GeometricFiber f y → (pullback obj.1.hom f).Opens
  /-- Distinct pieces are disjoint. -/
  disjoint (t t' : GeometricFiber f y) (h : t ≠ t') : Disjoint (piece t) (piece t')
  /-- The pieces cover `U ×_Y X`. -/
  iSup_eq : ⨆ t, piece t = ⊤
  /-- The `t`-th piece contains the point `(u, t)`. -/
  mem (t : GeometricFiber f y) : basePt f obj t default ∈ piece t

namespace SplitNeighborhood

variable {f}

/-- **The pieces of a split neighbourhood are closed**, since the complement of the `t`-th
piece is the union of the other pieces. -/
lemma isClopen (c : SplitNeighborhood f y) (t : GeometricFiber f y) :
    IsClopen (↑(c.piece t) : Set (pullback c.obj.1.hom f : Scheme.{u})) := by
  refine ⟨isOpen_compl_iff.mp ?_, (c.piece t).isOpen⟩
  have hcompl : (↑(c.piece t) : Set (pullback c.obj.1.hom f : Scheme.{u}))ᶜ =
      ⋃ t' ∈ {t' | t' ≠ t}, (↑(c.piece t') : Set (pullback c.obj.1.hom f : Scheme.{u})) := by
    ext x
    simp only [Set.mem_compl_iff, Set.mem_iUnion, Set.mem_ofPred_eq, exists_prop]
    refine ⟨fun hx ↦ ?_, ?_⟩
    · have hx' : x ∈ ⨆ t', c.piece t' := by
        rw [c.iSup_eq]
        trivial
      obtain ⟨t', ht'⟩ := Opens.mem_iSup.mp hx'
      exact ⟨t', fun h ↦ hx (h ▸ ht'), ht'⟩
    · rintro ⟨t', hne, ht'⟩ hx
      have hmem : x ∈ c.piece t' ⊓ c.piece t := ⟨ht', hx⟩
      rw [(c.disjoint t' t hne).eq_bot] at hmem
      exact hmem
  rw [hcompl]
  exact isOpen_biUnion fun t' _ ↦ (c.piece t').isOpen

/-- A morphism of split neighbourhoods: a morphism of pointed étale neighbourhoods carrying each
piece into the corresponding piece. -/
@[ext]
structure Morphism (c c' : SplitNeighborhood f y) where
  /-- The underlying morphism of pointed étale neighbourhoods. -/
  val : c.obj ⟶ c'.obj
  /-- Each piece is carried into the corresponding piece. -/
  le (t : GeometricFiber f y) : c.piece t ≤ (f.Etale.map val.val).left ⁻¹ᵁ c'.piece t

instance : Category (SplitNeighborhood f y) where
  Hom := Morphism
  id c := ⟨𝟙 _, fun t ↦ by
    rw [CategoryOfElements.id_val, CategoryTheory.Functor.map_id]
    exact le_rfl⟩
  comp g g' := ⟨g.val ≫ g'.val, fun t ↦ by
    refine (g.le t).trans ?_
    rw [CategoryOfElements.comp_val, CategoryTheory.Functor.map_comp]
    exact Scheme.Hom.preimage_mono _ (g'.le t)⟩

@[simp]
lemma id_val (c : SplitNeighborhood f y) : Morphism.val (𝟙 c) = 𝟙 c.obj := rfl

@[simp]
lemma comp_val {c c' c'' : SplitNeighborhood f y} (g : c ⟶ c') (g' : c' ⟶ c'') :
    (g ≫ g').val = g.val ≫ g'.val := rfl

@[ext]
lemma hom_ext {c c' : SplitNeighborhood f y} {g g' : c ⟶ c'} (h : g.val = g'.val) : g = g' :=
  Morphism.ext h

variable (f y) in
/-- The forgetful functor from split neighbourhoods to pointed étale neighbourhoods of `y`. -/
@[simps]
def forget : SplitNeighborhood f y ⥤ EtaleNeighborhood y where
  obj c := c.obj
  map g := g.val

instance : (forget f y).Faithful where
  map_injective h := hom_ext h

/-- The decomposition of a split neighbourhood pulled back along a morphism of pointed étale
neighbourhoods. -/
@[simps obj piece]
def pullbackDec (c : SplitNeighborhood f y) {c₀ : EtaleNeighborhood y} (g : c₀ ⟶ c.obj) :
    SplitNeighborhood f y where
  obj := c₀
  piece t := (f.Etale.map g.val).left ⁻¹ᵁ c.piece t
  disjoint t t' h := by
    rw [disjoint_iff, ← Scheme.Hom.preimage_inf, (c.disjoint t t' h).eq_bot,
      Scheme.Hom.preimage_bot]
  iSup_eq := by
    rw [← Scheme.Hom.preimage_iSup, c.iSup_eq, Scheme.Hom.preimage_top]
  mem t := by
    have := c.mem t
    rwa [← basePt_comp_etale_map_left f g t, Scheme.Hom.comp_apply] at this

/-- The morphism from a pulled back decomposition. -/
@[simps]
def pullbackDecHom (c : SplitNeighborhood f y) {c₀ : EtaleNeighborhood y} (g : c₀ ⟶ c.obj) :
    c.pullbackDec g ⟶ c where
  val := g
  le _ := le_rfl

/-- The point `(u, t)` lands in the `t`-th piece. -/
lemma range_basePt_subset (c : SplitNeighborhood f y) (t : GeometricFiber f y) :
    Set.range (basePt f c.obj t).base ⊆ Set.range (c.piece t).ι.base := by
  rw [Scheme.Opens.range_ι]
  rintro _ ⟨p, rfl⟩
  rw [Subsingleton.elim (α := Spec (.of Ω)) p default]
  exact c.mem t

/-- The `t`-th piece of a split neighbourhood, as an étale `X`-scheme. -/
def pieceObj (c : SplitNeighborhood f y) (t : GeometricFiber f y) : X.Etale :=
  Scheme.Etale.mk ((c.piece t).ι ≫ pullback.snd c.obj.1.hom f)

/-- The point `(u, t)` of the `t`-th piece. -/
def piecePt (c : SplitNeighborhood f y) (t : GeometricFiber f y) :
    (pointSmallEtale t.1).fiber.obj (c.pieceObj t) :=
  CategoryTheory.Over.homMk (IsOpenImmersion.lift (c.piece t).ι (basePt f c.obj t)
    (c.range_basePt_subset t)) (by
      change IsOpenImmersion.lift _ _ _ ≫ (c.piece t).ι ≫ pullback.snd c.obj.1.hom f = t.1
      rw [← Category.assoc, IsOpenImmersion.lift_fac, basePt_snd])

/-- The point `(u, t)` of the `t`-th piece is the point `(u, t)` of `U ×_Y X`: the triangle
```
Spec Ω ──(c.piecePt t).left──→ piece t
      ╲                          │
        ╲  basePt f c.obj t      │ (c.piece t).ι
          ↘                      ↓
                             U ×_Y X
```
commutes. -/
@[reassoc (attr := simp)]
lemma piecePt_left_ι (c : SplitNeighborhood f y) (t : GeometricFiber f y) :
    (c.piecePt t).left ≫ (c.piece t).ι = basePt f c.obj t :=
  IsOpenImmersion.lift_fac _ _ _

/-- The morphism between the `t`-th pieces induced by a morphism of split neighbourhoods. -/
def pieceMap {c c' : SplitNeighborhood f y} (g : c ⟶ c') (t : GeometricFiber f y) :
    c.pieceObj t ⟶ c'.pieceObj t :=
  MorphismProperty.Over.homMk ((f.Etale.map g.val.val).left.resLE (c'.piece t) (c.piece t)
    (Morphism.le g t)) (by
      change _ ≫ (c'.piece t).ι ≫ pullback.snd c'.obj.1.hom f =
        (c.piece t).ι ≫ pullback.snd c.obj.1.hom f
      rw [← Category.assoc, Scheme.Hom.resLE_comp_ι, Category.assoc]
      congr 1
      exact pullback.lift_snd _ _ _)

@[simp]
lemma pieceMap_left {c c' : SplitNeighborhood f y} (g : c ⟶ c') (t : GeometricFiber f y) :
    (pieceMap g t).left = (f.Etale.map g.val.val).left.resLE (c'.piece t) (c.piece t)
      (Morphism.le g t) :=
  rfl

/-- The morphism between the `t`-th pieces lies over the base change morphism: the square
```
    piece t ──(pieceMap g t).left──→ piece' t
       │                                │
       │ (c.piece t).ι                  │ (c'.piece t).ι
       ↓                                ↓
    U ×_Y X ──(f.Etale.map g.val.val).left──→ U' ×_Y X
```
commutes. -/
@[reassoc (attr := simp)]
lemma pieceMap_left_ι {c c' : SplitNeighborhood f y} (g : c ⟶ c') (t : GeometricFiber f y) :
    (pieceMap g t).left ≫ (c'.piece t).ι = (c.piece t).ι ≫ (f.Etale.map g.val.val).left := by
  rw [pieceMap_left, Scheme.Hom.resLE_comp_ι]

/-- The `t`-th piece of a split neighbourhood, with its point `(u, t)`, as a functor to the
pointed étale neighbourhoods of the geometric point `t` in `X`. -/
@[simps]
def pieceFunctor (t : GeometricFiber f y) :
    SplitNeighborhood f y ⥤ EtaleNeighborhood t.1 where
  obj c := ⟨c.pieceObj t, c.piecePt t⟩
  map {c c'} g := CategoryOfElements.homMk _ _ (pieceMap g t) (by
    apply CategoryTheory.Over.OverMorphism.ext
    apply (cancel_mono (c'.piece t).ι).mp
    change (c.piecePt t).left ≫ (pieceMap g t).left ≫ (c'.piece t).ι = _
    rw [pieceMap_left_ι, piecePt_left_ι_assoc, basePt_comp_etale_map_left, piecePt_left_ι])
  map_id c := by
    apply CategoryOfElements.ext
    apply MorphismProperty.Over.Hom.ext
    apply (cancel_mono (c.piece t).ι).mp
    change (pieceMap (𝟙 c) t).left ≫ (c.piece t).ι = 𝟙 _ ≫ _
    rw [pieceMap_left_ι, id_val, CategoryOfElements.id_val, CategoryTheory.Functor.map_id,
      Category.id_comp]
    rfl
  map_comp {c c' c''} g g' := by
    apply CategoryOfElements.ext
    apply MorphismProperty.Over.Hom.ext
    apply (cancel_mono (c''.piece t).ι).mp
    change (pieceMap (g ≫ g') t).left ≫ (c''.piece t).ι =
      ((pieceMap g t).left ≫ (pieceMap g' t).left) ≫ (c''.piece t).ι
    rw [pieceMap_left_ι, comp_val, CategoryOfElements.comp_val, CategoryTheory.Functor.map_comp,
      Category.assoc, pieceMap_left_ι, pieceMap_left_ι_assoc]
    rfl

end SplitNeighborhood

/-- A geometric point `z` of `U ×_Y X` over the point `u` of a pointed étale neighbourhood
`(U, u)` of `y` is of the form `(u, t)` for the geometric point `t = z ≫ snd` of `X` over `y`. -/
lemma basePt_eq_of_comp_fst_eq (c : EtaleNeighborhood y) (z : Spec (.of Ω) ⟶ pullback c.1.hom f)
    (hz : z ≫ pullback.fst c.1.hom f = c.2.left) :
    basePt f c ⟨z ≫ pullback.snd c.1.hom f, by
      rw [Category.assoc, ← pullback.condition, ← Category.assoc, hz]
      exact CategoryTheory.Over.w c.2⟩ = z := by
  apply pullback.hom_ext
  · rw [basePt_fst, hz]
  · rw [basePt_snd]

end SepClosed

section Shrink

variable [IsFinite f] [IsAlgClosed Ω] {y : Spec (.of Ω) ⟶ Y}

/-- **Shrinking away from a closed subset without geometric points.** Let `(U, u)` be a pointed
étale neighbourhood of `y` and `C` a closed subset of `U ×_Y X` containing none of the points
`(u, t)`. Then there is a pointed étale neighbourhood `(U', u') ⟶ (U, u)` such that the preimage
of `C` in `U' ×_Y X` is empty. -/
theorem exists_hom_preimage_eq_bot (c : EtaleNeighborhood y)
    (C : Set (pullback c.1.hom f : Scheme.{u})) (hC : IsClosed C)
    (h : ∀ t : GeometricFiber f y, basePt f c t default ∉ C) :
    ∃ (c' : EtaleNeighborhood y) (g : c' ⟶ c), (f.Etale.map g.val).left.base ⁻¹' C = ∅ := by
  obtain ⟨U, u⟩ := c
  -- the image `Z` of `C` in `U` is closed, since `U ×_Y X ⟶ U` is finite hence closed, and it
  -- does not contain the marked point, since every point of `U ×_Y X` over `u` is some `(u, t)`
  set Z : Set U.left := (pullback.fst U.hom f).base '' C
  have hZc : IsClosed Z := (pullback.fst U.hom f).isClosedMap C hC
  have hu : u.left (default : Spec (.of Ω)) ∉ Z := by
    rintro ⟨z, hzC, hz⟩
    obtain ⟨z', hz'⟩ := GeometricFiber.exists_apply_default_eq (pullback.fst U.hom f) u.left z hz
    refine h ⟨z'.1 ≫ pullback.snd U.hom f, ?_⟩ ?_
    · rw [Category.assoc, ← pullback.condition, ← Category.assoc, z'.2]
      exact CategoryTheory.Over.w u
    · rw [basePt_eq_of_comp_fst_eq f ⟨U, u⟩ z'.1 z'.2, hz']
      exact hzC
  -- the open neighbourhood `U' := U \ Z` of the marked point
  let U' : U.left.Opens := ⟨Zᶜ, hZc.isOpen_compl⟩
  have hrange : Set.range u.left.base ⊆ Set.range U'.ι.base := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨p, rfl⟩
    rw [Subsingleton.elim (α := Spec (.of Ω)) p default]
    exact hu
  set u' := IsOpenImmersion.lift U'.ι u.left hrange
  have hu'ι : u' ≫ U'.ι = u.left := IsOpenImmersion.lift_fac _ _ _
  let θ : Scheme.Etale.mk (U'.ι ≫ U.hom) ⟶ U := MorphismProperty.Over.homMk U'.ι rfl
  refine ⟨⟨Scheme.Etale.mk (U'.ι ≫ U.hom), CategoryTheory.Over.homMk u' ?_⟩,
    CategoryOfElements.homMk _ _ θ ?_, ?_⟩
  · change u' ≫ U'.ι ≫ U.hom = y
    rw [← Category.assoc, hu'ι]
    exact CategoryTheory.Over.w u
  · exact CategoryTheory.Over.OverMorphism.ext hu'ι
  · -- a point of `U' ×_Y X` over `C` would map to a point of `U' ∩ Z = ∅`
    rw [Set.eq_empty_iff_forall_notMem]
    intro w hw
    have h₁ : (pullback.fst U.hom f) ((f.Etale.map θ).left w) =
        U'.ι ((pullback.fst (Scheme.Etale.mk (U'.ι ≫ U.hom)).hom f) w) :=
      congrArg (fun m ↦ m.base w) (Hom.etale_map_left_comp_fst f θ)
    have h₂ : (pullback.fst U.hom f) ((f.Etale.map θ).left w) ∈ Z := ⟨_, hw, rfl⟩
    rw [h₁] at h₂
    exact ((Scheme.Opens.range_ι U').subset (Set.mem_range_self _)) h₂

end Shrink

end AlgebraicGeometry.Scheme.Hom

end
