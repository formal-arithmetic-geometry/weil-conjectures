/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group O2
-/
module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.CategoryTheory.MorphismProperty.OverAdjunction
public import WeilConjectures.CategoryTheory.Comma.Over.DescentDatum
public import Sheaf.CategoryTheory.SiteCoveringAxioms

import WeilConjectures.AlgebraicGeometry.IsSeparatedOfFlatSurjectiveBaseChange
import WeilConjectures.AlgebraicGeometry.FpqcDescentEtale

/-! # A descended coproduct represents a pro-étale sheaf

Source: blueprint, sec-six-functors-basics, sk-lem-stratified-lattice,
sk-lem-stratified-lattice-scheme.proof.md (2)--(3); Stacks Tags 02KU, 02VN and 023Q
(blueprint: lem-sfb-coproduct-model-represents-sheaf).
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite

private theorem localEquivalences
    {C : Type*} [Category C] {J : GrothendieckTopology C}
    {E : Cᵒᵖ ⥤ Type w} {G : Cᵒᵖ ⥤ Type u}
    (hE : Presieve.IsSheaf J E) (hG : Presieve.IsSheaf J G) (V : C)
    (hc : J.CoversTop (fun _ : PUnit.{1} ↦ V))
    (l : ∀ W : C, (W ⟶ V) → (E.obj (op W) ≃ G.obj (op W)))
    (hn : ∀ (W Z : C) (g : Z ⟶ W) (f : W ⟶ V) (f' : Z ⟶ V)
      (s : E.obj (op W)), l Z f' (E.map g.op s) = G.map g.op (l W f s)) :
    ∃ b : ∀ W : C, E.obj (op W) ≃ G.obj (op W),
      (∀ (W Z : C) (g : Z ⟶ W) (s : E.obj (op W)),
        b Z (E.map g.op s) = G.map g.op (b W s)) ∧
      (∀ (W : C) (f : W ⟶ V) (s : E.obj (op W)), b W s = l W f s) := by
  classical
  let R (W : C) := Sieve.ofObjects (fun _ : PUnit.{1} ↦ V) W
  have hR (W : C) : R W ∈ J W := hc W
  let lift (W : C) {Z : C} {g : Z ⟶ W} (hg : R W g) : Z ⟶ V :=
    hg.choose_spec.some
  let x (W : C) (s : E.obj (op W)) : (R W).arrows.FamilyOfElements G :=
    fun Z g hg ↦ l Z (lift W hg) (E.map g.op s)
  have hx (W : C) (s : E.obj (op W)) : (x W s).Compatible := by
    intro Z₁ Z₂ T g₁ g₂ f₁ f₂ hf₁ hf₂ h
    dsimp [x]
    rw [← hn Z₁ T g₁ (lift W hf₁) (g₁ ≫ lift W hf₁),
      ← hn Z₂ T g₂ (lift W hf₂) (g₁ ≫ lift W hf₁)]
    simp only [← Functor.map_comp_apply, ← op_comp, h]
  let b (W : C) (s : E.obj (op W)) := (hG (R W) (hR W)).amalgamate (x W s) (hx W s)
  have hb (W Z : C) (g : Z ⟶ W) (f : Z ⟶ V) (s : E.obj (op W)) :
      G.map g.op (b W s) = l Z f (E.map g.op s) := by
    have h := (hG (R W) (hR W)).valid_glue (hx W s)
      g (show R W g from ⟨PUnit.unit, ⟨f⟩⟩)
    exact h.trans (by
      dsimp [x]
      simpa using (hn Z Z (𝟙 Z) (lift W (g := g) ⟨PUnit.unit, ⟨f⟩⟩) f (E.map g.op s)).symm)
  have hn' (W Z : C) (g : Z ⟶ W) (f : W ⟶ V) (f' : Z ⟶ V)
      (s : G.obj (op W)) :
      (l Z f').symm (G.map g.op s) = E.map g.op ((l W f).symm s) := by
    apply (l Z f').injective
    rw [Equiv.apply_symm_apply, hn, Equiv.apply_symm_apply]
  let y (W : C) (s : G.obj (op W)) : (R W).arrows.FamilyOfElements E :=
    fun Z g hg ↦ (l Z (lift W hg)).symm (G.map g.op s)
  have hy (W : C) (s : G.obj (op W)) : (y W s).Compatible := by
    intro Z₁ Z₂ T g₁ g₂ f₁ f₂ hf₁ hf₂ h
    dsimp [y]
    rw [← hn' Z₁ T g₁ (lift W hf₁) (g₁ ≫ lift W hf₁),
      ← hn' Z₂ T g₂ (lift W hf₂) (g₁ ≫ lift W hf₁)]
    simp only [← Functor.map_comp_apply, ← op_comp, h]
  let c (W : C) (s : G.obj (op W)) := (hE (R W) (hR W)).amalgamate (y W s) (hy W s)
  have hcl (W Z : C) (g : Z ⟶ W) (f : Z ⟶ V) (s : G.obj (op W)) :
      E.map g.op (c W s) = (l Z f).symm (G.map g.op s) := by
    have h := (hE (R W) (hR W)).valid_glue (hy W s)
      g (show R W g from ⟨PUnit.unit, ⟨f⟩⟩)
    exact h.trans (by
      dsimp [y]
      simpa using (hn' Z Z (𝟙 Z) (lift W (g := g) ⟨PUnit.unit, ⟨f⟩⟩) f (G.map g.op s)).symm)
  let e (W : C) : E.obj (op W) ≃ G.obj (op W) :=
    { toFun := b W
      invFun := c W
      left_inv := by
        intro s
        apply (hE (R W) (hR W)).isSeparatedFor.ext
        intro Z g hg
        rw [hcl W Z g (lift W hg), hb W Z g (lift W hg), Equiv.symm_apply_apply]
      right_inv := by
        intro s
        apply (hG (R W) (hR W)).isSeparatedFor.ext
        intro Z g hg
        rw [hb W Z g (lift W hg), hcl W Z g (lift W hg), Equiv.apply_symm_apply] }
  refine ⟨e, ?_, ?_⟩
  · intro W Z g s
    apply (hG (R Z) (hR Z)).isSeparatedFor.ext
    intro T f hf
    change G.map f.op (b Z (E.map g.op s)) = G.map f.op (G.map g.op (b W s))
    rw [hb Z T f (lift Z hf)]
    simpa only [Functor.map_comp, op_comp, ConcreteCategory.comp_apply] using
      (hb W T (f ≫ g) (lift Z hf) s).symm
  · intro W f s
    simpa [e] using hb W W (𝟙 W) f s

namespace AlgebraicGeometry

/-- The structure map of the coproduct of copies of `V`.
Source: blueprint, stratified-lattice scheme proof (2), the schemes `T_k`.
(blueprint: lem-sfb-coproduct-model-represents-sheaf) -/
noncomputable abbrev coproductModelProjection (V : Scheme.{u}) (S : Type v) [Small.{u} S] :
    (∐ fun _ : S ↦ V) ⟶ V :=
  Sigma.desc fun _ ↦ 𝟙 V

private theorem coproductProjection_separated (V : Scheme.{u}) (S : Type v) [Small.{u} S] :
    IsSeparated (coproductModelProjection V S) := by
  classical
  let T : Scheme.{u} := ∐ fun _ : S ↦ V
  let t : T ⟶ V := coproductModelProjection V S
  let j (i : S) : V ⟶ T := Sigma.ι (fun _ : S ↦ V) i
  have hj (i : S) : j i ≫ t = 𝟙 V := by simp [j, t, coproductModelProjection]
  have : Etale t := IsZariskiLocalAtSource.sigmaDesc fun _ ↦ inferInstance
  let block (i k : S) : V ⟶ pullback t t := pullback.lift (j i) (j k) (by rw [hj, hj])
  have hr (i k : S) : Set.range (block i k) =
      pullback.fst t t ⁻¹' Set.range (j i) ∩ pullback.snd t t ⁻¹' Set.range (j k) := by
    let m := pullback.map (𝟙 V) (𝟙 V) t t (j i) (j k) (𝟙 V)
      (by simp [hj]) (by simp [hj])
    have hm : m = pullback.fst (𝟙 V) (𝟙 V) ≫ block i k := by
      apply pullback.hom_ext
      · simp [m, block]
      · simp only [m, block, pullback.map, Category.assoc, pullback.lift_snd]
        have h : pullback.snd (𝟙 V) (𝟙 V) = pullback.fst (𝟙 V) (𝟙 V) := by
          simpa using (pullback.condition (f := 𝟙 V) (g := 𝟙 V)).symm
        rw [h]
    have hrm := Scheme.Pullback.range_map (𝟙 V) (𝟙 V) t t (j i) (j k) (𝟙 V)
      (by simp [hj]) (by simp [hj])
    change Set.range (fun x ↦ m x) = _ at hrm
    simp only [hm, Scheme.Hom.comp_apply] at hrm
    have heq : Set.range (pullback.fst (𝟙 V) (𝟙 V) ≫ block i k) =
        Set.range (block i k) := by
      change Set.range ((fun x : V ↦ block i k x) ∘
        (fun x ↦ pullback.fst (𝟙 V) (𝟙 V) x)) = _
      rw [Set.range_comp, (pullback.fst (𝟙 V) (𝟙 V)).surjective.range_eq, Set.image_univ]
    exact heq.symm.trans hrm
  let O : Set (pullback t t : Scheme.{u}) :=
    ⋃ (i : S) (k : S), if i = k then ∅ else Set.range (fun x : V ↦ block i k x)
  have ho : IsOpen O := by
    apply isOpen_iUnion
    intro i
    apply isOpen_iUnion
    intro k
    split_ifs
    · exact isOpen_empty
    rw [hr]
    exact ((j i).isOpenEmbedding.isOpen_range.preimage (pullback.fst t t).continuous).inter
      ((j k).isOpenEmbedding.isOpen_range.preimage (pullback.snd t t).continuous)
  have he : (Set.range (pullback.diagonal t))ᶜ = O := by
    ext z
    constructor
    · intro hz
      obtain ⟨i, x, hx⟩ := (sigmaOpenCover (fun _ : S ↦ V)).exists_eq (pullback.fst t t z)
      obtain ⟨k, y, hy⟩ := (sigmaOpenCover (fun _ : S ↦ V)).exists_eq (pullback.snd t t z)
      have hmem : z ∈ Set.range (block i k) := (hr i k).symm ▸ ⟨⟨x, hx⟩, ⟨y, hy⟩⟩
      have hik : i ≠ k := by
        intro h
        subst k
        obtain ⟨w, rfl⟩ := hmem
        apply hz
        have hd : block i i = j i ≫ pullback.diagonal t := by
          apply pullback.hom_ext <;> simp [block]
        exact ⟨j i w, by rw [← Scheme.Hom.comp_apply, ← hd]⟩
      exact Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr
        ⟨k, by simpa [hik] using hmem⟩⟩
    · intro hz
      obtain ⟨i, hz⟩ := Set.mem_iUnion.mp hz
      obtain ⟨k, hz⟩ := Set.mem_iUnion.mp hz
      by_cases hik : i = k
      · simp [hik] at hz
      simp only [if_neg hik] at hz
      rw [hr] at hz
      rintro ⟨w, rfl⟩
      obtain ⟨x, hx⟩ := hz.1
      obtain ⟨y, hy⟩ := hz.2
      have hxy : j i x = j k y := by
        rw [hx, hy]
        simp [← Scheme.Hom.comp_apply]
      exact hik (congrArg Sigma.fst ((sigmaι_eq_iff _ _ _ _ _).mp hxy))
  exact ⟨IsClosedImmersion.of_isPreimmersion _ (isOpen_compl_iff.mp (he ▸ ho))⟩

/-- A coproduct model, compatibly descended along a weakly étale fpqc morphism, represents
its original sheaf, with unique normalized natural bijections and the universal section.

Source: blueprint, sec-six-functors-basics, sk-lem-stratified-lattice,
sk-lem-stratified-lattice-scheme.proof.md (2)--(3); Stacks Tags 02KU, 02VN and 023Q.
(blueprint: lem-sfb-coproduct-model-represents-sheaf)

The local representation is the family `a`, with naturality `ha`. The transport equation
`hδ` expresses its compatibility with the canonical comparison of the two restrictions of
`F`. The equation `hη` says that the specified isomorphism `η` induces that descent datum.
The `Over.DescentDatum` interface is the Yoneda-equivalent transport form of Stacks 023V.

Proof:
1. The coprojections are disjoint open immersions covering the coproduct, by
   lem-weil-pbc-scheme-coproduct-family. On each component the structure map is the identity,
   hence étale. Apply lem-weil-pbc-etale-local-on-source, including the empty cover.
2. The product of the coproduct with itself over `V` is covered by disjoint blocks indexed
   by pairs in `S`. Its diagonal consists exactly of the diagonal blocks. This is open and
   closed, and extension by zero on the complementary blocks makes the structure-sheaf
   map surjective. Thus the diagonal is a closed immersion and the map is separated.
   This uses lem-weil-pbc-open-immersion-base-change and def-weil-closed-immersion.
3. Transfer these properties through `η` and use lem-weil-pbc-fpqc-descend-separated and
   lem-galois-fpqc-descend-etale. If `S` is nonempty, one coprojection gives a section of
   the local model, so surjectivity of `p` implies surjectivity of `q`. Étale implies weakly
   étale by det-pe-morphisms-etale-comparison.
4. For a site object `U`, the base change `C = U ×_X V` covers `U`. Its double overlap is
   again a site object by lem-weil-pbc-weakly-etale-composition-base-change. The covering
   follows from lem-galois-fpqc-covering-base-change. The sheaf condition identifies
   `F(U)` with
   the equalizer of the two restriction maps from `F(C)` to its double overlap.
5. Apply `a` to a restricted section. Equations `hδ` and `hη` say the resulting map from
   `C` to `Y` agrees on the overlap. By lem-weil-pbc-fpqc-representable-descent it descends
   uniquely to a map `U → Y`; uniqueness applied to its composite with `q` makes it over X.
6. Conversely pull back a map `U → Y`, compose with `η`, and apply the inverse of `a`.
   The same compatibility equations give matching sections on the overlap, so the sheaf
   condition glues them uniquely. The two operations are inverse by their local restrictions.
7. Naturality of `a` and uniqueness of morphism descent give naturality and uniqueness of
   the normalized family `b`. Pulling normalization back along the graph of any `W → V`
   gives its version directly on `W`.
8. Define the universal section as the inverse image of the identity of `Y` under `b`.
   Naturality gives its pullback formula. Apply the graph version of normalization with
   `W = T` to see that its restriction corresponds to the identity of `T`. Empty `S` uses
   the same equalizers; only surjectivity used a chosen index. For empty `X`, all schemes
   involved are empty, and the empty-cover sheaf condition gives singleton section sets.
-/
theorem coproductModel_represents_sheaf
    {X V Y : Scheme.{u}} (p : V ⟶ X) [WeaklyEtale p] [Flat p]
    [Surjective p] [QuasiCompact p]
    (hp : Presieve.singleton p ∈ Scheme.fpqcPrecoverage X)
    (S : Type v) [Small.{u} S]
    (F : Sheaf (Scheme.ProEt.topology X) (Type w))
    (a : ∀ W : V.ProEt,
      F.obj.obj (op ((MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale p)).obj W)) ≃
        (Over.mk W.hom ⟶ Over.mk (coproductModelProjection V S)))
    (ha : ∀ (W W' : V.ProEt) (g : W' ⟶ W)
      (s : F.obj.obj
        (op ((MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale p)).obj W))),
      a W' (F.obj.map
        ((MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale p)).map g).op s) =
      (Over.homMk g.left (MorphismProperty.Over.w g)) ≫ a W s)
    (δ : Over.DescentDatum p (Over.mk (coproductModelProjection V S)))
    (hδ : ∀ (W : Scheme.{u}) (f₁ f₂ : W ⟶ V)
      (hf₁ : WeaklyEtale f₁) (hf₂ : WeaklyEtale f₂) (h : f₁ ≫ p = f₂ ≫ p)
      (s : F.obj.obj (op ((MorphismProperty.Over.map ⊤
        (inferInstance : WeaklyEtale p)).obj (@Scheme.ProEt.mk _ _ f₁ hf₁)))),
      δ.transport f₁ f₂ h (a (@Scheme.ProEt.mk _ _ f₁ hf₁) s) =
        a (@Scheme.ProEt.mk _ _ f₂ hf₂)
          (F.obj.map (MorphismProperty.Over.homMk (𝟙 W) (by
            change 𝟙 W ≫ (f₁ ≫ p) = f₂ ≫ p
            exact (Category.id_comp _).trans h)).op s))
    (q : Y ⟶ X)
    (η : (Over.pullback p).obj (Over.mk q) ≅ Over.mk (coproductModelProjection V S))
    (hη : ∀ (W : Scheme.{u}) (f₁ f₂ : W ⟶ V) (h : f₁ ≫ p = f₂ ≫ p)
      (c : Over.mk f₁ ⟶ Over.mk (coproductModelProjection V S)),
      (δ.transport f₁ f₂ h c).left ≫ η.inv.left ≫ pullback.fst q p =
        c.left ≫ η.inv.left ≫ pullback.fst q p) :
    IsSeparated q ∧ Etale q ∧ (Nonempty S → Surjective q) ∧
      ∃ (hY : WeaklyEtale q) (hT : WeaklyEtale (coproductModelProjection V S)),
        ∃! b : ∀ U : X.ProEt, F.obj.obj (op U) ≃
            ((Scheme.ProEt.forget X).obj U ⟶ Over.mk q),
          (∀ (U U' : X.ProEt) (g : U' ⟶ U) (s : F.obj.obj (op U)),
            b U' (F.obj.map g.op s) = (Scheme.ProEt.forget X).map g ≫ b U s) ∧
          (∀ (U : X.ProEt) (s : F.obj.obj (op U)),
            (a ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ p).obj U)
              (F.obj.map (MorphismProperty.Over.homMk (pullback.fst U.hom p)
                (pullback.condition)).op s)).left =
              pullback.lift (pullback.fst U.hom p ≫ (b U s).left)
                (pullback.snd U.hom p)
                (by
                  change (pullback.fst U.hom p ≫ (b U s).left) ≫ q = _
                  exact (Category.assoc _ _ _).trans
                    ((congrArg (fun f : U.left ⟶ X ↦ pullback.fst U.hom p ≫ f)
                      (Over.w (b U s))).trans pullback.condition)) ≫ η.hom.left) ∧
          (∀ (U : X.ProEt) (f : U ⟶ @Scheme.ProEt.mk _ _ q hY),
            b U (F.obj.map f.op
              ((b (@Scheme.ProEt.mk _ _ q hY)).symm (𝟙 (Over.mk q)))) =
              (Scheme.ProEt.forget X).map f) ∧
          a (@Scheme.ProEt.mk _ _ (coproductModelProjection V S) hT)
            (F.obj.map (MorphismProperty.Over.homMk
              (η.inv.left ≫ pullback.fst q p)
              (by
                change (η.inv.left ≫ pullback.fst q p) ≫ q =
                  coproductModelProjection V S ≫ p
                rw [Category.assoc, pullback.condition, ← Category.assoc]
                exact congrArg (fun f ↦ f ≫ p) (Over.w η.inv))).op
              ((b (@Scheme.ProEt.mk _ _ q hY)).symm (𝟙 (Over.mk q)))) =
            𝟙 (Over.mk (coproductModelProjection V S)) := by
  classical
  let t := coproductModelProjection V S
  have ht : Etale t := IsZariskiLocalAtSource.sigmaDesc fun _ ↦ inferInstance
  have hst : IsSeparated t := coproductProjection_separated V S
  have he : η.hom.left ≫ t = pullback.snd q p := Over.w η.hom
  have : Etale (pullback.snd q p) := by
    rw [← he]
    infer_instance
  have : IsSeparated (pullback.snd q p) := by
    rw [← he]
    infer_instance
  have hq : Etale q := etale_of_fpqc_cover q (fun _ : PUnit.{1} ↦ V) (fun _ ↦ p)
    (by simpa only [Presieve.ofArrows_pUnit] using hp) (fun _ ↦ inferInstance)
  have hsq : IsSeparated q := isSeparated_of_flat_surjective_baseChange q p
  refine ⟨hsq, hq, ?_, inferInstance, inferInstance, ?_⟩
  · intro hS
    obtain ⟨i⟩ := hS
    let r : V ⟶ Y := Sigma.ι (fun _ : S ↦ V) i ≫ η.inv.left ≫ pullback.fst q p
    have hr : r ≫ q = p := by
      dsimp [r]
      rw [Category.assoc, Category.assoc, pullback.condition,
        ← Category.assoc η.inv.left]
      change Sigma.ι (fun _ : S ↦ V) i ≫ (η.inv.left ≫ pullback.snd q p) ≫ p = p
      rw [show η.inv.left ≫ pullback.snd q p = t from Over.w η.inv, ← Category.assoc]
      simp [t, coproductModelProjection]
    have : Surjective (r ≫ q) := hr ▸ inferInstance
    exact Surjective.of_comp r q
  let Q : X.ProEt := Scheme.ProEt.mk q
  let P : X.ProEt := Scheme.ProEt.mk p
  let G := (Scheme.ProEt.forget X).op ⋙ yoneda.obj (Over.mk q)
  have hG : Presieve.IsSheaf (Scheme.ProEt.topology X) G :=
    (Scheme.ProEt.forget X).op_comp_isSheaf_of_types _ _
      ((Scheme.proetaleTopology.over X).yoneda.obj (Over.mk q))
  have hc : (Scheme.ProEt.topology X).CoversTop (fun _ : PUnit.{1} ↦ P) := by
    intro U
    let C := (MorphismProperty.Over.pullback @WeaklyEtale ⊤ p).obj U
    let c : ((MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale p)).obj C) ⟶ U :=
      MorphismProperty.Over.homMk (pullback.fst U.hom p) pullback.condition
    have hmem : Presieve.singleton c ∈ Scheme.ProEt.precoverage X U := by
      rw [Scheme.ProEt.precoverage, Precoverage.mem_comap_iff, Presieve.map_singleton]
      change Presieve.singleton (pullback.fst U.hom p) ∈ Scheme.proetalePrecoverage _
      exact Scheme.Hom.singleton_mem_propQCPrecoverage (inferInstance : WeaklyEtale
        (pullback.fst U.hom p))
    apply (Scheme.ProEt.topology X).superset_covering _
      (Precoverage.generate_mem_toGrothendieck hmem)
    rw [Sieve.generate_le_iff]
    intro W f hf
    cases hf
    exact ⟨PUnit.unit, ⟨MorphismProperty.Over.homMk (pullback.snd U.hom p)
      (by change pullback.snd U.hom p ≫ p = pullback.snd U.hom p ≫ p; rfl)⟩⟩
  let localObj (W : X.ProEt) (f : W ⟶ P) : V.ProEt :=
    @Scheme.ProEt.mk _ _ f.left (by
      have : WeaklyEtale (f.left ≫ p) := by
        rw [show f.left ≫ p = W.hom from MorphismProperty.Over.w f]
        infer_instance
      exact WeaklyEtale.of_comp f.left p)
  let baseIso (W : X.ProEt) (f : W ⟶ P) :
      W ≅ (MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale p)).obj (localObj W f) :=
    MorphismProperty.Over.isoMk (Iso.refl _) (by
      change 𝟙 W.left ≫ (f.left ≫ p) = W.hom
      exact (Category.id_comp _).trans (MorphismProperty.Over.w f))
  let loc (W : X.ProEt) (f : W ⟶ P) : F.obj.obj (op W) ≃ G.obj (op W) :=
    ((F.obj.mapIso (baseIso W f).op.symm).toEquiv.trans (a (localObj W f))).trans
      (((Equiv.ofBijective
        (fun c : Over.mk f.left ⟶ Over.mk t ↦ c ≫ η.inv)
        (by exact ⟨fun c d h ↦ (cancel_mono η.inv).mp h,
          fun d ↦ ⟨d ≫ η.hom, by simp⟩⟩)).trans
        ((Over.mapPullbackAdj p).homEquiv (Over.mk f.left) (Over.mk q)).symm).trans
        (Equiv.ofBijective
          (fun c ↦ Over.homMk c.left (by
            exact (Over.w c).trans (MorphismProperty.Over.w f)))
          (by
            constructor
            · intro c d h
              exact Over.OverMorphism.ext (congrArg (fun k ↦ k.left) h)
            · intro d
              exact ⟨Over.homMk d.left (by
                exact (Over.w d).trans (MorphismProperty.Over.w f).symm),
                Over.OverMorphism.ext rfl⟩)))
  have hloc (W : X.ProEt) (f : W ⟶ P) (s : F.obj.obj (op W)) :
      (loc W f s).left =
        (a (localObj W f) (F.obj.map (baseIso W f).inv.op s)).left ≫
          η.inv.left ≫ pullback.fst q p := rfl
  have hind (W : X.ProEt) (f f' : W ⟶ P) (s : F.obj.obj (op W)) :
      loc W f s = loc W f' s := by
    apply Over.OverMorphism.ext
    rw [hloc, hloc]
    let s₀ := F.obj.map (baseIso W f).inv.op s
    have hh : f.left ≫ p = f'.left ≫ p :=
      (MorphismProperty.Over.w f).trans (MorphismProperty.Over.w f').symm
    have hd := hδ W.left f.left f'.left (localObj W f).prop (localObj W f').prop hh s₀
    have h := hη W.left f.left f'.left hh (a (localObj W f) s₀)
    rw [hd] at h
    let k : (MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale p)).obj
        (localObj W f') ⟶
        (MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale p)).obj (localObj W f) :=
      MorphismProperty.Over.homMk (𝟙 W.left) (by
        change 𝟙 W.left ≫ (f.left ≫ p) = f'.left ≫ p
        simpa using hh)
    have hs : F.obj.map k.op s₀ = F.obj.map (baseIso W f').inv.op s := by
      dsimp [s₀]
      rw [← Functor.map_comp_apply, ← op_comp]
      congr 2
    change (a (localObj W f') (F.obj.map k.op s₀)).left ≫ _ ≫ _ = _ at h
    rw [hs] at h
    exact h.symm
  have hln (W Z : X.ProEt) (g : Z ⟶ W) (f : W ⟶ P) (f' : Z ⟶ P)
      (s : F.obj.obj (op W)) :
      loc Z f' (F.obj.map g.op s) = G.map g.op (loc W f s) := by
    rw [← hind Z (g ≫ f) f']
    apply Over.OverMorphism.ext
    change (loc Z (g ≫ f) (F.obj.map g.op s)).left = g.left ≫ (loc W f s).left
    rw [hloc, hloc]
    let j : localObj Z (g ≫ f) ⟶ localObj W f :=
      MorphismProperty.Over.homMk g.left rfl
    have hs : F.obj.map (baseIso Z (g ≫ f)).inv.op (F.obj.map g.op s) =
        F.obj.map ((MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale p)).map j).op
          (F.obj.map (baseIso W f).inv.op s) := by
      simp only [← Functor.map_comp_apply, ← op_comp]
      congr 2
    rw [hs, ha (localObj W f) (localObj Z (g ≫ f)) j]
    change (g.left ≫ _) ≫ _ ≫ _ = g.left ≫ (_ ≫ _ ≫ _)
    simp only [Category.assoc]
  obtain ⟨b, hbn, hbl⟩ := localEquivalences
    ((isSheaf_iff_isSheaf_of_type _ _).mp F.property) hG P hc loc hln
  have hb (W : X.ProEt) (f : W ⟶ P) (s : F.obj.obj (op W)) :
      (b W s).left =
        (a (localObj W f) (F.obj.map (baseIso W f).inv.op s)).left ≫
          η.inv.left ≫ pullback.fst q p := by rw [hbl W f s]; rfl
  have hnorm (U : X.ProEt) (s : F.obj.obj (op U)) :
      (a ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ p).obj U)
        (F.obj.map (MorphismProperty.Over.homMk (pullback.fst U.hom p)
          pullback.condition).op s)).left =
        pullback.lift (pullback.fst U.hom p ≫ (b U s).left) (pullback.snd U.hom p)
          (by
            change (pullback.fst U.hom p ≫ (b U s).left) ≫ q = _
            exact (Category.assoc _ _ _).trans
              ((congrArg (fun k : U.left ⟶ X ↦ pullback.fst U.hom p ≫ k)
                (Over.w (b U s))).trans pullback.condition)) ≫ η.hom.left := by
    let C := (MorphismProperty.Over.pullback @WeaklyEtale ⊤ p).obj U
    let W := (MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale p)).obj C
    let c : W ⟶ U := MorphismProperty.Over.homMk (pullback.fst U.hom p) pullback.condition
    let f : W ⟶ P := MorphismProperty.Over.homMk (pullback.snd U.hom p) rfl
    have hh := hb W f (F.obj.map c.op s)
    have hn := congrArg (fun k ↦ k.left) (hbn U W c s)
    change (b W (F.obj.map c.op s)).left = pullback.fst U.hom p ≫ (b U s).left at hn
    have hlocal := hh
    rw [show F.obj.map (baseIso W f).inv.op (F.obj.map c.op s) = F.obj.map c.op s by
      change F.obj.map (𝟙 (op W)) _ = _
      exact F.obj.map_id_apply _ _] at hlocal
    let L : C.left ⟶ pullback q p :=
      pullback.lift (pullback.fst U.hom p ≫ (b U s).left) (pullback.snd U.hom p) (by
        exact (Category.assoc _ _ _).trans
          ((congrArg (fun k : U.left ⟶ X ↦ pullback.fst U.hom p ≫ k)
            (Over.w (b U s))).trans pullback.condition))
    have hL : (a C (F.obj.map c.op s)).left ≫ η.inv.left = L := by
      apply pullback.hom_ext
      · change ((a C (F.obj.map c.op s)).left ≫ η.inv.left) ≫ pullback.fst q p =
          L ≫ pullback.fst q p
        have hfL : L ≫ pullback.fst q p = pullback.fst U.hom p ≫ (b U s).left :=
          pullback.lift_fst _ _ _
        exact (Category.assoc _ _ _).trans ((hlocal.symm.trans hn).trans hfL.symm)
      · change ((a C (F.obj.map c.op s)).left ≫ η.inv.left) ≫ pullback.snd q p =
          L ≫ pullback.snd q p
        have hsL : L ≫ pullback.snd q p = pullback.snd U.hom p :=
          pullback.lift_snd _ _ _
        have hi : η.inv.left ≫ pullback.snd q p = t := Over.w η.inv
        exact (Category.assoc _ _ _).trans
          ((congrArg (fun k ↦ (a C (F.obj.map c.op s)).left ≫ k) hi).trans
            ((Over.w (a C (F.obj.map c.op s))).trans hsL.symm))
    change (a C (F.obj.map c.op s)).left = L ≫ η.hom.left
    rw [← hL, Category.assoc]
    have hei : η.inv.left ≫ η.hom.left = 𝟙 _ :=
      congrArg (fun k ↦ k.left) η.inv_hom_id
    rw [hei, Category.comp_id]
  refine ⟨b, ⟨hbn, hnorm, ?_, ?_⟩, ?_⟩
  · intro U f
    have h := hbn Q U f ((b Q).symm (𝟙 (Over.mk q)))
    rw [Equiv.apply_symm_apply] at h
    change b U _ = (Scheme.ProEt.forget X).map f ≫ 𝟙 (Over.mk q) at h
    exact h.trans (Category.comp_id _)
  · let W : X.ProEt := Scheme.ProEt.mk (t ≫ p)
    let f : W ⟶ P := MorphismProperty.Over.homMk t rfl
    let r : W ⟶ Q := MorphismProperty.Over.homMk (η.inv.left ≫ pullback.fst q p)
      (by
        change (η.inv.left ≫ pullback.fst q p) ≫ q = t ≫ p
        rw [Category.assoc, pullback.condition, ← Category.assoc]
        exact congrArg (fun k ↦ k ≫ p) (Over.w η.inv))
    let u := (b Q).symm (𝟙 (Over.mk q))
    have hn := congrArg (fun k ↦ k.left) (hbn Q W r u)
    rw [Equiv.apply_symm_apply] at hn
    change (b W (F.obj.map r.op u)).left =
      (η.inv.left ≫ pullback.fst q p) ≫ 𝟙 Y at hn
    rw [Category.comp_id] at hn
    have h := hb W f (F.obj.map r.op u)
    have hs : F.obj.map (baseIso W f).inv.op (F.obj.map r.op u) = F.obj.map r.op u := by
      have he : (baseIso W f).inv = 𝟙 W := MorphismProperty.Over.Hom.ext rfl
      rw [he]
      change F.obj.map (𝟙 (op W)) _ = _
      exact F.obj.map_id_apply _ _
    rw [hs, hn] at h
    apply Over.OverMorphism.ext
    change (a (Scheme.ProEt.mk t) (F.obj.map r.op u)).left = 𝟙 _
    apply (cancel_mono η.inv.left).mp
    rw [Category.id_comp]
    apply pullback.hom_ext
    · change (a (localObj W f) (F.obj.map r.op u)).left ≫
        η.inv.left ≫ pullback.fst q p = η.inv.left ≫ pullback.fst q p
      exact h.symm
    · change ((a (localObj W f) (F.obj.map r.op u)).left ≫ η.inv.left) ≫
        pullback.snd q p = η.inv.left ≫ pullback.snd q p
      rw [Category.assoc,
        show η.inv.left ≫ pullback.snd q p = t from Over.w η.inv]
      exact Over.w (a (localObj W f) (F.obj.map r.op u))
  · intro b' hb'
    funext U
    apply Equiv.ext
    intro s
    apply Over.OverMorphism.ext
    apply (cancel_epi (pullback.fst U.hom p)).mp
    have h := (hb'.2.1 U s).symm.trans (hnorm U s)
    have h' := congrArg (fun k ↦ k ≫ η.inv.left ≫ pullback.fst q p) h
    have hei : η.hom.left ≫ η.inv.left = 𝟙 _ :=
      congrArg (fun k ↦ k.left) η.hom_inv_id
    simp only [Category.assoc, reassoc_of% hei] at h'
    change pullback.fst U.hom p ≫ (b' U s).left =
      pullback.fst U.hom p ≫ (b U s).left
    change pullback.lift (f := q) (g := p) _ _ _ ≫ pullback.fst q p =
      pullback.lift (f := q) (g := p) _ _ _ ≫ pullback.fst q p at h'
    simpa only [pullback.lift_fst] using h'

end AlgebraicGeometry

