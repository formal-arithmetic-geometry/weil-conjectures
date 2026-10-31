/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import WeilConjectures.CategoryTheory.Comma.Over.DescentDatum
public import WeilConjectures.AlgebraicGeometry.QuasiFiniteMorphism
public import WeilConjectures.Mathlib.AlgebraicGeometry.QuasiAffine
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import WeilConjectures.AlgebraicGeometry.QuasiFiniteMorphismComparison

/-!
# Quasi-affine covering by saturations of affine opens

Source: Stacks Project, More on Morphisms, Tag 02W8, second paragraph of the proof.
(blueprint: lem-trf-affine-descent-saturation-quasi-affine-cover).

The canonical relation map is `D.toHom : V ×_B A ⟶ V`. The pullback map below includes
`C ×_B A` into `V ×_B A`; its composite with `D.toHom` is the map called `r_C` in the source.
-/

@[expose] public section

set_option autoImplicit false

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Over.DescentDatum

private lemma toHom_isOpenMap
    {A B : Scheme.{u}} (p : A ⟶ B) [Flat p] [LocallyOfFinitePresentation p]
    {V : Over A} (D : Over.DescentDatum p V) : IsOpenMap D.toHom := by
  let s := pullback.fst (V.hom ≫ p) p
  let q := pullback.snd (V.hom ≫ p) p
  have hp : (s ≫ V.hom) ≫ p = q ≫ p := by
    simp only [s, q, Category.assoc, pullback.condition]
  have htq : D.toHom ≫ V.hom = q :=
    Over.w (D.transport (s ≫ V.hom) q hp universalPoint)
  let i := pullback.lift D.toHom (s ≫ V.hom) (by
    rw [← Category.assoc, htq]
    exact hp.symm)
  have his : i ≫ s = D.toHom := pullback.lift_fst _ _ _
  have hiq : i ≫ q = s ≫ V.hom := pullback.lift_snd _ _ _
  have hit : i ≫ D.toHom = s := by
    let b : Over.mk q ⟶ V := Over.homMk D.toHom htq
    have hb : D.transport (s ≫ V.hom) q hp universalPoint = b := by
      ext
      rfl
    have hn : (D.transport q (s ≫ V.hom) hp.symm b).left = i ≫ D.toHom :=
      D.transport_left_eq_lift_toHom q (s ≫ V.hom) hp.symm b
    rw [← hn, ← hb, D.transport_transport, D.transport_self]
    rfl
  have hii : i ≫ i = 𝟙 _ := by
    apply pullback.hom_ext
    · change (i ≫ i) ≫ s = (𝟙 _) ≫ s
      rw [Category.assoc, his, hit, Category.id_comp]
    · change (i ≫ i) ≫ q = (𝟙 _) ≫ q
      rw [Category.assoc, hiq, ← Category.assoc, his, htq, Category.id_comp]
  have : IsIso i := ⟨⟨i, hii, hii⟩⟩
  rw [← his]
  exact (s.isOpenMap).comp i.isOpenEmbedding.isOpenMap

/-- Saturations of all affine opens give a quasi-compact quasi-affine open covering.

Source: Stacks Project, More on Morphisms, Tag 02W8, second paragraph of the proof.
(blueprint: lem-trf-affine-descent-saturation-quasi-affine-cover).

Proof:
1. By lem-weil-pbc-flat-lfp-open, the base change A ×_B V → V is open. The inclusion
   C ×_B A → V ×_B A is an open immersion by lem-weil-pbc-open-immersion-base-change.
   The descent isomorphism preserves opens, so its image under the projection is open.
2. By lem-weil-pbc-affine-scheme-qcqs, C is quasi-compact. The base change of p to C
   is quasi-compact by lem-weil-pbc-qcqs-morphism-permanence, so C ×_B A is quasi-compact.
   Its continuous image W_C is quasi-compact: pull back any open cover, take a finite
   subcover, and descend that subcover using surjectivity onto the image.
3. Pull the cocycle of def-pd-descent-datum back along the small diagonal. Its restriction
   e satisfies e = e ∘ e, and cancelling the invertible e gives e = 1. Thus the composite
   C → C ×_B A → V is C.ι, proving C ⊆ W_C. In the transport interface this is
   D.transport_self; the fibre-product maps are those of def-pc-fibre-product.
4. The diagonal of W_C → A is the restriction of the closed diagonal of V → A to the
   open W_C ×_A W_C. A closed immersion remains closed after this restriction, using
   def-weil-proper-morphism, def-weil-closed-immersion and def-weil-open-immersion.
5. By lem-weil-pbc-lqf-restriction-to-opens, W_C → A is locally quasi-finite, hence
   locally of finite type by lem-weil-pbc-lqf-locally-finite-type. Since A is affine and
   W_C is quasi-compact, lem-weil-pbc-affine-scheme-qcqs and
   lem-weil-pbc-qcqs-morphism-permanence make W_C → A quasi-compact. Apply
   lemma-nagata-quasi-affine-morphism-of-quasi-finite to obtain quasi-affineness.
6. Every point of V belongs to an affine open C by lem-weil-pbc-affine-opens-basis,
   and hence to W_C by step 3. Therefore the supremum of the W_C is the whole space.
   This also holds for the empty scheme, with no nonemptiness hypothesis.
-/
theorem affine_descent_saturation_quasi_affine_cover
    {A B : Scheme.{u}} [IsAffine A] [IsAffine B]
    (p : A ⟶ B) [Flat p] [Surjective p] [LocallyOfFinitePresentation p]
    [QuasiCompact p] [QuasiSeparated p] {V : Over A}
    (D : Over.DescentDatum p V) [IsSeparated V.hom]
    (_hπ : V.hom.IsLocallyQuasiFinite) :
    ∃ W : V.left.affineOpens → V.left.Opens,
      (∀ C : V.left.affineOpens,
        (W C : Set V.left) = Set.range
          (pullback.map (C.1.ι ≫ V.hom ≫ p) p (V.hom ≫ p) p C.1.ι (𝟙 A) (𝟙 B)
            (by simp) (by simp) ≫ D.toHom) ∧
        IsCompact (W C : Set V.left) ∧ C.1 ≤ W C ∧
        IsQuasiAffineHom ((W C).ι ≫ V.hom)) ∧
      (⨆ C : V.left.affineOpens, W C) = ⊤ := by
  classical
  let j (C : V.left.affineOpens) :=
    pullback.map (C.1.ι ≫ V.hom ≫ p) p (V.hom ≫ p) p C.1.ι (𝟙 A) (𝟙 B)
      (by simp) (by simp)
  let r (C : V.left.affineOpens) := j C ≫ D.toHom
  have hj (C : V.left.affineOpens) : IsOpenImmersion (j C) :=
    MorphismProperty.of_isPullback
      (isPullback_pullback_map_left C.1.ι (V.hom ≫ p) p) inferInstance
  have hopen (C : V.left.affineOpens) : IsOpen (Set.range (r C)) := by
    have := hj C
    exact ((toHom_isOpenMap p D).comp (j C).isOpenEmbedding.isOpenMap).isOpen_range
  let W : V.left.affineOpens → V.left.Opens := fun C ↦ ⟨Set.range (r C), hopen C⟩
  have hcpt (C : V.left.affineOpens) : IsCompact (W C : Set V.left) := by
    have : IsAffine C.1.toScheme := C.2
    have : CompactSpace (Limits.pullback (C.1.ι ≫ V.hom ≫ p) p : Scheme.{u}) :=
      QuasiCompact.compactSpace_of_compactSpace (pullback.fst _ _)
    exact isCompact_range (r C).continuous
  have hle (C : V.left.affineOpens) : C.1 ≤ W C := by
    let k : C.1.toScheme ⟶ Limits.pullback (C.1.ι ≫ V.hom ≫ p) p :=
      pullback.lift (𝟙 C.1.toScheme) (C.1.ι ≫ V.hom) (by simp)
    have hk : k ≫ j C = pullback.lift (f := V.hom ≫ p) (g := p)
        C.1.ι (C.1.ι ≫ V.hom) (by simp) := by
      apply pullback.hom_ext
      · dsimp only [j]
        rw [Category.assoc, pullback.lift_fst, pullback.lift_fst]
        dsimp only [k]
        rw [pullback.lift_fst_assoc, Category.id_comp]
      · dsimp only [j]
        rw [Category.assoc, pullback.lift_snd, pullback.lift_snd]
        dsimp only [k]
        rw [pullback.lift_snd_assoc, Category.comp_id]
    have hr : k ≫ r C = C.1.ι := by
      dsimp only [r]
      rw [← Category.assoc, hk]
      have he := D.transport_left_eq_lift_toHom (C.1.ι ≫ V.hom) (C.1.ι ≫ V.hom)
        rfl (Over.homMk C.1.ι)
      rw [D.transport_self] at he
      exact he.symm
    intro x hx
    refine ⟨k ⟨x, hx⟩, ?_⟩
    exact congrArg (fun f ↦ f ⟨x, hx⟩) hr
  have hqf := (V.hom.isLocallyQuasiFinite_iff).mp _hπ
  have : LocallyQuasiFinite V.hom := hqf.1
  have : LocallyOfFiniteType V.hom := hqf.2
  refine ⟨W, ?_, ?_⟩
  · intro C
    have : CompactSpace (W C).toScheme := isCompact_iff_compactSpace.mp (hcpt C)
    exact ⟨rfl, hcpt C, hle C,
      IsQuasiAffineHom.of_locallyQuasiFinite ((W C).ι ≫ V.hom)⟩
  · apply top_unique
    rw [← iSup_affineOpens_eq_top V.left]
    exact iSup_mono hle

end CategoryTheory.Over.DescentDatum
