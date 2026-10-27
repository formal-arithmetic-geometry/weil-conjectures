/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q99
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Limits.Types.Colimits
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Over
public import WeilConjectures.AlgebraicGeometry.QuasiFiniteMorphism
public import Sheaf.CategoryTheory.SiteCoveringAxioms
import Mathlib.CategoryTheory.Sites.LocallySurjective
import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
import Sheaf.AlgebraicGeometry.EtaleRelationKernelPair
import WeilConjectures.AlgebraicGeometry.QuasiFiniteMorphismComparison

/-! # Fppf local models of a quotient diagonal

Source: Stacks Project, Spaces, Tag 0265, third representability step
(blueprint: lem-trf-quotient-diagonal-fppf-local-models).

## Main definitions and statements

- `quotientDiagonalFibre`: the canonical relative equality fibre.
- `quotient_diagonal_fppf_local_models`: its common cover and prescribed local models.

The relative diagonal fibre is realized as the type of witnesses of equality of the two
sections. Proof irrelevance makes it subterminal; restriction is induced by naturality.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

/-- The diagonal fibre over the specified map to `T`, on the big site over `T`.
Its elements are witnesses that the two restricted sections agree. This is the
sectionwise realization of `h_T ×_(F × F) F`, with its map to `h_T` fixed by the slice.
Source: Stacks Project, Spaces, Tag 0265, third step, diagonal fibre product
(blueprint: lem-trf-quotient-diagonal-fppf-local-models). -/
def quotientDiagonalFibre {S : Scheme.{u}} (T : Over S)
    (F : Sheaf (Scheme.fppfTopology.over S) (Type u))
    (a₁ a₂ : yoneda.obj T ⟶ F.obj) : (Over T.left)ᵒᵖ ⥤ Type u where
  obj W := { _x : PUnit.{u + 1} //
    a₁.app (op ((Over.map T.hom).obj W.unop)) (Over.homMk W.unop.hom) =
    a₂.app (op ((Over.map T.hom).obj W.unop)) (Over.homMk W.unop.hom) }
  map {W V} f := ↾fun h ↦ ⟨h.val, by
    have h₁ := a₁.naturality_apply ((Over.map T.hom).map f.unop).op
      (Over.homMk W.unop.hom)
    have h₂ := a₂.naturality_apply ((Over.map T.hom).map f.unop).op
      (Over.homMk W.unop.hom)
    have hw : ((Over.map T.hom).map f.unop) ≫ Over.homMk W.unop.hom =
        (Over.homMk V.unop.hom : (Over.map T.hom).obj V.unop ⟶ T) := by
      ext
      exact Over.w f.unop
    have he := h₁.trans ((congrArg
      (F.obj.map ((Over.map T.hom).map f.unop).op) h.property).trans h₂.symm)
    change a₁.app (op ((Over.map T.hom).obj V.unop))
        (((Over.map T.hom).map f.unop) ≫ Over.homMk W.unop.hom) =
      a₂.app (op ((Over.map T.hom).obj V.unop))
        (((Over.map T.hom).map f.unop) ≫ Over.homMk W.unop.hom) at he
    rw [hw] at he
    exact he⟩
  map_id _ := by ext x
  map_comp _ _ := by ext x

private theorem diagonal_fibre_isSheaf {S : Scheme.{u}} (T : Over S)
    (F : Sheaf (Scheme.fppfTopology.over S) (Type u))
    (a₁ a₂ : yoneda.obj T ⟶ F.obj) :
    Presheaf.IsSheaf (Scheme.fppfTopology.over T.left)
      (quotientDiagonalFibre T F a₁ a₂) := by
  let G := (Over.map T.hom).op ⋙ F.obj
  have hG : Presieve.IsSheaf (Scheme.fppfTopology.over T.left) G :=
    (Over.map T.hom).op_comp_isSheaf_of_types _ _ F
  rw [isSheaf_iff_isSheaf_of_type]
  intro W K hK x _hx
  have he : a₁.app (op ((Over.map T.hom).obj W)) (Over.homMk W.hom) =
      a₂.app (op ((Over.map T.hom).obj W)) (Over.homMk W.hom) := by
    apply (hG K hK).isSeparatedFor.ext
    intro V f hf
    have h₁ := a₁.naturality_apply ((Over.map T.hom).map f).op (Over.homMk W.hom)
    have h₂ := a₂.naturality_apply ((Over.map T.hom).map f).op (Over.homMk W.hom)
    dsimp only [G, Functor.comp_map, Functor.op_map, Quiver.Hom.unop_op]
    rw [← h₁, ← h₂]
    have hw : (Over.map T.hom).map f ≫ Over.homMk W.hom =
        (Over.homMk V.hom : (Over.map T.hom).obj V ⟶ T) := by
      ext
      exact Over.w f
    change a₁.app _ ((Over.map T.hom).map f ≫ Over.homMk W.hom) =
      a₂.app _ ((Over.map T.hom).map f ≫ Over.homMk W.hom)
    rw [hw]
    exact (x f hf).property
  refine ⟨⟨PUnit.unit, he⟩, ?_, ?_⟩
  · intro V f hf
    exact Subtype.ext (Subsingleton.elim _ _)
  · intro y _hy
    exact Subtype.ext (Subsingleton.elim _ _)

-- The locally generated image is a subsheaf even when general small-valued
-- sheafification on the site is unavailable. Its inclusion splits by universality.
private theorem universal_locally_surjective
    {C : Type*} [Category* C] (J : GrothendieckTopology C)
    {P : Cᵒᵖ ⥤ Type u} (F : Sheaf J (Type u)) (η : P ⟶ F.obj)
    (hη : ∀ G : Sheaf J (Type u),
      Function.Bijective (fun g : F.obj ⟶ G.obj ↦ η ≫ g)) :
    Presheaf.IsLocallySurjective J η := by
  let R := (Subfunctor.range η).sheafify J
  have hR : Presheaf.IsSheaf J R.toFunctor :=
    (isSheaf_iff_isSheaf_of_type J _).mpr
      ((Subfunctor.range η).sheafify_isSheaf
        ((isSheaf_iff_isSheaf_of_type J _).mp F.property))
  obtain ⟨l, hl⟩ := (hη ⟨R.toFunctor, hR⟩).surjective (Subfunctor.toRangeSheafify J η)
  have hli : l ≫ R.ι = 𝟙 F.obj := by
    apply (hη F).injective
    change η ≫ l ≫ R.ι = η ≫ 𝟙 F.obj
    change η ≫ l = _ at hl
    rw [← Category.assoc, hl]
    simp [R, Subfunctor.toRangeSheafify]
  rw [Presheaf.isLocallySurjective_iff_range_sheafify_eq_top']
  apply le_antisymm le_top
  intro V x _
  have e : (l.app V x).val = x := by
    exact congrArg (fun t ↦ t.app V x) hli
  exact e ▸ (l.app V x).property

private theorem simultaneous_lifts {S : Scheme.{u}} {R U : Over S}
    (s t : R ⟶ U) (F : Sheaf (Scheme.fppfTopology.over S) (Type u))
    (η : coequalizer (yoneda.map s) (yoneda.map t) ⟶ F.obj)
    (hη : ∀ G : Sheaf (Scheme.fppfTopology.over S) (Type u),
      Function.Bijective (fun g : F.obj ⟶ G.obj ↦ η ≫ g))
    (T : Over S) (a₁ a₂ : yoneda.obj T ⟶ F.obj) :
    ∃ (I : Type (u + 1)) (Tᵢ : I → Over S) (f : ∀ i, Tᵢ i ⟶ T)
      (uᵢ vᵢ : ∀ i, Tᵢ i ⟶ U),
      Presieve.ofArrows (fun i ↦ (Tᵢ i).left) (fun i ↦ (f i).left) ∈
        Scheme.fppfPrecoverage T.left ∧
      (∀ i, yoneda.map (uᵢ i) ≫ (coequalizer.π (yoneda.map s) (yoneda.map t) ≫ η) =
        yoneda.map (f i) ≫ a₁) ∧
      (∀ i, yoneda.map (vᵢ i) ≫ (coequalizer.π (yoneda.map s) (yoneda.map t) ≫ η) =
        yoneda.map (f i) ≫ a₂) := by
  classical
  let π := coequalizer.π (yoneda.map s) (yoneda.map t)
  let q := π ≫ η
  have hπ : Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) π :=
    Presheaf.isLocallySurjective_of_surjective _ π fun W ↦
      (epi_iff_surjective (π.app W)).mp inferInstance
  have hη' := universal_locally_surjective _ F η hη
  have hq : Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) q := by
    dsimp [q]
    infer_instance
  let : Scheme.fppfPrecoverage.HasIsos :=
    ⟨fun f _ ↦ Scheme.Hom.singleton_mem_fppfPrecoverage f⟩
  -- Intersect the two covering image sieves before extracting a single fppf family.
  let K := Scheme.fppfPrecoverage.comap (Over.forget S)
  have hc : Presheaf.imageSieve q (yonedaEquiv a₁) ⊓
      Presheaf.imageSieve q (yonedaEquiv a₂) ∈ K.toGrothendieck T := by
    rw [← over_toGrothendieck_eq_toGrothendieck_comap_forget]
    exact (Scheme.fppfTopology.over S).intersection_covering
      (Presheaf.imageSieve_mem _ q _) (Presheaf.imageSieve_mem _ q _)
  obtain ⟨D, hD, hle⟩ := K.mem_toGrothendieck_iff_of_isStableUnderComposition.mp hc
  obtain ⟨I, V, f, rfl⟩ := D.exists_eq_ofArrows
  have lifts : ∀ i, ∃ (b c : V i ⟶ U),
      yoneda.map b ≫ q = yoneda.map (f i) ≫ a₁ ∧
      yoneda.map c ≫ q = yoneda.map (f i) ≫ a₂ := by
    intro i
    obtain ⟨b, hb⟩ := (hle _ _ (Presieve.ofArrows.mk i)).1
    obtain ⟨c, hc⟩ := (hle _ _ (Presieve.ofArrows.mk i)).2
    refine ⟨b, c, ?_, ?_⟩
    · apply yonedaEquiv.injective
      rw [yonedaEquiv_comp, yonedaEquiv_yoneda_map, ← yonedaEquiv_naturality]
      exact hb
    · apply yonedaEquiv.injective
      rw [yonedaEquiv_comp, yonedaEquiv_yoneda_map, ← yonedaEquiv_naturality]
      exact hc
  choose b c hb hc using lifts
  refine ⟨I, V, f, b, c, ?_, hb, hc⟩
  simpa only [K, Precoverage.mem_comap_iff, Presieve.map_ofArrows,
    Over.forget_obj, Over.forget_map] using hD

private theorem kernel_pair_witness {S : Scheme.{u}} {R U B : Over S}
    (s t : R ⟶ U) {F : (Over S)ᵒᵖ ⥤ Type u} (q : yoneda.obj U ⟶ F)
    (hk : IsPullback (yoneda.map s) (yoneda.map t) q q) (b c : B ⟶ U) :
    yoneda.map b ≫ q = yoneda.map c ≫ q ↔
      ∃ r : B ⟶ R, r ≫ s = b ∧ r ≫ t = c := by
  constructor
  · intro h
    let r := yoneda.preimage (hk.lift (yoneda.map b) (yoneda.map c) h)
    refine ⟨r, ?_, ?_⟩
    · apply yoneda.map_injective
      simp [r, Functor.map_comp]
    · apply yoneda.map_injective
      simp [r, Functor.map_comp]
  · rintro ⟨r, rfl, rfl⟩
    simp only [Functor.map_comp, Category.assoc, hk.w]

private theorem local_model_nonempty {S : Scheme.{u}} {R U T A : Over S}
    (s t : R ⟶ U) {F : Sheaf (Scheme.fppfTopology.over S) (Type u)}
    (q : yoneda.obj U ⟶ F.obj)
    (hk : IsPullback (yoneda.map s) (yoneda.map t) q q)
    (a₁ a₂ : yoneda.obj T ⟶ F.obj) (f : A ⟶ T) (b c : A ⟶ U)
    (hb : yoneda.map b ≫ q = yoneda.map f ≫ a₁)
    (hc : yoneda.map c ≫ q = yoneda.map f ≫ a₂) (W : Over A.left) :
    Nonempty ((quotientDiagonalFibre T F a₁ a₂).obj (op ((Over.map f.left).obj W))) ↔
      Nonempty (W ⟶ Over.mk (pullback.fst (prod.lift b c).left (prod.lift s t).left)) := by
  let B := (Over.map T.hom).obj ((Over.map f.left).obj W)
  let w : B ⟶ A := Over.homMk W.hom (by simp [B, Category.assoc])
  let p := (prod.lift b c).left
  let j := (prod.lift s t).left
  have hw : w ≫ f = (Over.homMk ((Over.map f.left).obj W).hom : B ⟶ T) := by
    ext
    rfl
  have he : Nonempty
      ((quotientDiagonalFibre T F a₁ a₂).obj (op ((Over.map f.left).obj W))) ↔
      yoneda.map (w ≫ b) ≫ q = yoneda.map (w ≫ c) ≫ q := by
    have h₁ := congrArg (fun k ↦ yoneda.map w ≫ k) hb
    have h₂ := congrArg (fun k ↦ yoneda.map w ≫ k) hc
    rw [Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc, h₁, h₂]
    rw [← Category.assoc, ← Category.assoc, ← yoneda.map_comp, hw]
    constructor
    · rintro ⟨h⟩
      apply yonedaEquiv.injective
      exact h.property
    · intro h
      exact ⟨⟨PUnit.unit, congrArg yonedaEquiv h⟩⟩
  rw [he, kernel_pair_witness s t q hk]
  have hp₁ : pullback.snd p j ≫ s.left = pullback.fst p j ≫ b.left := by
    have h := (pullback.condition (f := p) (g := j)) =≫ (prod.fst : U ⨯ U ⟶ U).left
    simpa only [p, j, Category.assoc, ← Over.comp_left, prod.lift_fst] using h.symm
  have hp₂ : pullback.snd p j ≫ t.left = pullback.fst p j ≫ c.left := by
    have h := (pullback.condition (f := p) (g := j)) =≫ (prod.snd : U ⨯ U ⟶ U).left
    simpa only [p, j, Category.assoc, ← Over.comp_left, prod.lift_snd] using h.symm
  constructor
  · rintro ⟨r, hr₁, hr₂⟩
    have e : W.hom ≫ p = r.left ≫ j := by
      change (w ≫ prod.lift b c).left = (r ≫ prod.lift s t).left
      congr 1
      apply prod.hom_ext <;> simp [hr₁, hr₂]
    exact ⟨Over.homMk (pullback.lift W.hom r.left e) (by simp)⟩
  · rintro ⟨h⟩
    have hh : h.left ≫ pullback.fst p j = W.hom := Over.w h
    let r : B ⟶ R := Over.homMk (h.left ≫ pullback.snd p j) (by
      calc
        (h.left ≫ pullback.snd p j) ≫ R.hom =
            h.left ≫ (pullback.snd p j ≫ s.left) ≫ U.hom := by
          simp only [Category.assoc, Over.w s]
        _ = h.left ≫ (pullback.fst p j ≫ b.left) ≫ U.hom := by rw [hp₁]
        _ = W.hom ≫ A.hom := by
          calc
            _ = (h.left ≫ pullback.fst p j) ≫ (b.left ≫ U.hom) := by
              simp only [Category.assoc]
            _ = _ := by rw [hh, Over.w b]
        _ = B.hom := by simp [B, Category.assoc, Over.w f])
    refine ⟨r, ?_, ?_⟩
    · ext
      change (h.left ≫ pullback.snd p j) ≫ s.left = W.hom ≫ b.left
      rw [Category.assoc, hp₁, ← Category.assoc, hh]
    · ext
      change (h.left ≫ pullback.snd p j) ≫ t.left = W.hom ≫ c.left
      rw [Category.assoc, hp₂, ← Category.assoc, hh]

private theorem local_model_iso {S : Scheme.{u}} {R U T A : Over S}
    (s t : R ⟶ U) [Mono (prod.lift s t)]
    {F : Sheaf (Scheme.fppfTopology.over S) (Type u)}
    (q : yoneda.obj U ⟶ F.obj)
    (hk : IsPullback (yoneda.map s) (yoneda.map t) q q)
    (a₁ a₂ : yoneda.obj T ⟶ F.obj) (f : A ⟶ T) (b c : A ⟶ U)
    (hb : yoneda.map b ≫ q = yoneda.map f ≫ a₁)
    (hc : yoneda.map c ≫ q = yoneda.map f ≫ a₂) :
    Nonempty ((Over.map f.left).op ⋙ quotientDiagonalFibre T F a₁ a₂ ≅
      yoneda.obj (Over.mk (pullback.fst (prod.lift b c).left (prod.lift s t).left))) := by
  classical
  let H := (Over.map f.left).op ⋙ quotientDiagonalFibre T F a₁ a₂
  let Y := Over.mk (pullback.fst (prod.lift b c).left (prod.lift s t).left)
  have (W : (Over A.left)ᵒᵖ) : Subsingleton (H.obj W) := by
    dsimp [H, quotientDiagonalFibre]
    infer_instance
  have : Mono Y.hom := by
    dsimp [Y]
    infer_instance
  have (W : Over A.left) : Subsingleton (W ⟶ Y) := by
    refine ⟨fun x y ↦ ?_⟩
    ext
    apply (cancel_mono Y.hom).mp
    exact (Over.w x).trans (Over.w y).symm
  -- Monicity makes the relation witness unique, hence every component subterminal.
  let e (W : (Over A.left)ᵒᵖ) : H.obj W ≃ (yoneda.obj Y).obj W :=
    { toFun := fun x ↦ Classical.choice
        ((local_model_nonempty s t q hk a₁ a₂ f b c hb hc W.unop).mp ⟨x⟩)
      invFun := fun y ↦ Classical.choice
        ((local_model_nonempty s t q hk a₁ a₂ f b c hb hc W.unop).mpr ⟨y⟩)
      left_inv := fun _ ↦ Subsingleton.elim _ _
      right_inv := fun _ ↦ Subsingleton.elim _ _ }
  exact ⟨NatIso.ofComponents (fun W ↦ (e W).toIso) (by
    intro W V g
    ext x
    exact Subsingleton.elim _ _)⟩

/-- The diagonal fibre of the fppf sheaf quotient has a common cover of simultaneous
lifts, on which it is represented by the base change of the relation monomorphism.
The quotient is specified by its sheafification universal property `hη`, as in
`etale_relation_kernel_pair`; the presheaf coequalizer is the pointwise quotient.
Source: Stacks Project, Spaces, Tag 0265, third representability step, cartesian square
and cube; Sites, Tags 00WK and 00VH; Groupoids, Tag 045Y
(blueprint: lem-trf-quotient-diagonal-fppf-local-models).

Proof:
1. On `W → T`, the diagonal fibre consists of a section equal to both prescribed
   sections, hence has one element precisely when those sections agree and none
   otherwise. Equality is local since `F` is a sheaf, so the fibre is a sheaf,
   including on objects admitting the empty cover.
2. Apply lem-weil-pbc-site-sheafification-sections-local to the first section and
   choose representatives in `U` of its local quotient classes. Apply it again to
   the second section on each member. Compose the covers using the covering axioms
   of def-weil-pbc-sites-and-cohomology, restricting the first lifts to this common
   refinement. Yoneda identifies the section equalities with the displayed equalities
   of natural transformations.
3. Lem-trf-etale-relation-kernel-pair identifies equality of two quotient images
   with a unique relation witness, by evaluating its canonical kernel-pair square.
4. By def-pc-fibre-product, maps into the specified pullback are precisely relation
   witnesses with endpoints the two local lifts. Step 3 gives mutually inverse maps
   with the equality fibre. Precomposition preserves endpoints; uniqueness makes
   the inverse commute with restrictions, giving the displayed natural isomorphism.
5. The projection of this pullback is the base change of `j`. Both conclusions of
   lem-weil-pbc-separated-lqf-base-change give its separatedness and local
   quasi-finiteness. No affine or finite-type hypothesis on the test scheme is used. -/
theorem quotient_diagonal_fppf_local_models {S : Scheme.{u}} {R U : Over S}
    (s t : R ⟶ U) [Mono (prod.lift s t)]
    (hrel : ∀ W : Over S, Equivalence (fun b c : W ⟶ U ↦
      ∃ r : W ⟶ R, r ≫ s = b ∧ r ≫ t = c))
    [Etale s.left] [Etale t.left]
    (F : Sheaf (Scheme.fppfTopology.over S) (Type u))
    (η : coequalizer (yoneda.map s) (yoneda.map t) ⟶ F.obj)
    (hη : ∀ G : Sheaf (Scheme.fppfTopology.over S) (Type u),
      Function.Bijective (fun g : F.obj ⟶ G.obj ↦ η ≫ g))
    [IsSeparated (prod.lift s t).left]
    (hj : Scheme.Hom.IsLocallyQuasiFinite (prod.lift s t).left)
    (T : Over S) (a₁ a₂ : yoneda.obj T ⟶ F.obj) :
    Presheaf.IsSheaf (Scheme.fppfTopology.over T.left) (quotientDiagonalFibre T F a₁ a₂) ∧
    (∀ W : Over T.left,
      Subsingleton ((quotientDiagonalFibre T F a₁ a₂).obj (op W)) ∧
        (Nonempty ((quotientDiagonalFibre T F a₁ a₂).obj (op W)) ↔
          a₁.app (op ((Over.map T.hom).obj W)) (Over.homMk W.hom) =
            a₂.app (op ((Over.map T.hom).obj W)) (Over.homMk W.hom))) ∧
    ∃ (I : Type (u + 1)) (Tᵢ : I → Over S) (f : ∀ i, Tᵢ i ⟶ T)
      (uᵢ vᵢ : ∀ i, Tᵢ i ⟶ U),
      Presieve.ofArrows (fun i ↦ (Tᵢ i).left) (fun i ↦ (f i).left) ∈
        Scheme.fppfPrecoverage T.left ∧
      (∀ i, yoneda.map (uᵢ i) ≫ (coequalizer.π (yoneda.map s) (yoneda.map t) ≫ η) =
        yoneda.map (f i) ≫ a₁) ∧
      (∀ i, yoneda.map (vᵢ i) ≫ (coequalizer.π (yoneda.map s) (yoneda.map t) ≫ η) =
        yoneda.map (f i) ≫ a₂) ∧
      (∀ i, Nonempty
        ((Over.map (f i).left).op ⋙ quotientDiagonalFibre T F a₁ a₂ ≅
          yoneda.obj (Over.mk
            (pullback.fst (prod.lift (uᵢ i) (vᵢ i)).left (prod.lift s t).left)))) ∧
      (∀ i, IsSeparated
        (pullback.fst (prod.lift (uᵢ i) (vᵢ i)).left (prod.lift s t).left) ∧
        Scheme.Hom.IsLocallyQuasiFinite
          (pullback.fst (prod.lift (uᵢ i) (vᵢ i)).left (prod.lift s t).left)) := by
  classical
  refine ⟨diagonal_fibre_isSheaf T F a₁ a₂, ?_, ?_⟩
  · intro W
    refine ⟨?_, ?_⟩
    · dsimp [quotientDiagonalFibre]
      infer_instance
    · exact ⟨fun ⟨h⟩ ↦ h.property, fun h ↦ ⟨⟨PUnit.unit, h⟩⟩⟩
  · obtain ⟨I, A, f, b, c, hcover, hb, hc⟩ := simultaneous_lifts s t F η hη T a₁ a₂
    refine ⟨I, A, f, b, c, hcover, hb, hc, ?_, ?_⟩
    · intro i
      exact local_model_iso s t _ (etale_relation_kernel_pair s t hrel F η hη)
        a₁ a₂ (f i) (b i) (c i) (hb i) (hc i)
    · intro i
      obtain ⟨hj₁, hj₂⟩ := (Scheme.Hom.isLocallyQuasiFinite_iff _).mp hj
      let := hj₁
      let := hj₂
      exact ⟨inferInstance, (Scheme.Hom.isLocallyQuasiFinite_iff _).mpr
        ⟨inferInstance, inferInstance⟩⟩

end AlgebraicGeometry.Scheme
