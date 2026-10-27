/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q75
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Mathlib.AlgebraicGeometry.Morphisms.IsIso
import Sheaf.Compactification.NagataSketchClosure

/-!
# Schematic closure gives a Cartesian refining triangle

Source: blueprint main-20261015, sec-nagata-compactification,
`sk-lem-nagata-sketch-closure/_section.md`; schematic closure followed by the relative
properness and clopen-complement argument (blueprint: lem-sf-cartesian-closure-refinement).

The closure is the actual scheme-theoretic image `(j ≫ b).image`, with its canonical
inclusion and factor map. The new open part is its pullback along `i`.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

/-- Schematic closure removes the extra clopen part over the open base and gives a Cartesian
refining triangle, without a separatedness assumption on the structure maps to the field.

Source: blueprint main-20261015, sec-nagata-compactification,
`sk-lem-nagata-sketch-closure/_section.md`; Stacks Tags 01R8, 01RG, 01W4, 01W6 and 01JY
(blueprint: lem-sf-cartesian-closure-refinement).

Proof, following the six steps of the node:
1. The spectrum of the field is Noetherian. By lem-weil-pbc-finite-type-over-noetherian,
X and Xbar are Noetherian. By lem-weil-pbc-noetherian-open-subscheme-noetherian all opens
of X are quasi-compact, so the immersion h = j ≫ b is quasi-compact. By
lem-weil-pbc-locally-noetherian-quasi-separated, Xbar is quasi-separated.
2. Apply sk-lem-nagata-sketch-closure to h. Its canonical image W is the smallest closed
subscheme containing h, and u = h.toImage is open and schematically dense. The node
lemma-nagata-immersion-open-in-scheme-image also gives quasi-compactness and topological
density. The full scheme structure is retained, including nilpotents.
3. Form T = Xbar ×_Ybar Y. The projection to Xbar is open by
lem-weil-pbc-open-immersion-base-change. The given square induces an open immersion
e : V → T. The projection T → Y is proper by lem-weil-pbc-proper-base-change, hence
separated. Since q is proper, lemma-nagata-proper-to-separated-target makes e proper.
Its image is therefore both open and closed. No separatedness over the field is used.
4. The complement of e(V) is open in Xbar and disjoint from h(X). Its inverse image in
W is open and misses the topologically dense u(X), hence is empty. Consequently the
map W ×_Ybar Y → T factors uniquely through the open subscheme e(V), giving v.
This gives v ≫ b = b' ≫ a and v ≫ q = q'.
5. The universal property identifies W ×_Ybar Y with W ×_Xbar T. Its map to T factors
through V, so it is also W ×_Xbar V. Thus v is closed by lem-pc-closed-imm-base-change.
Factor u through W ×_Ybar Y to obtain j'. The projection b' is open, so j' is open;
its inverse images of affine opens are quasi-compact opens of X, so j' is quasi-compact.
The identity j' ≫ v = j follows after composing with the monomorphism b.
6. By lem-weil-pbc-closed-immersion-proper, a and v are proper. Their composites with
p and q are proper as well. The defining pullback square is Cartesian and b' is open.
The displayed identities and proper comparison maps give the refinement triangles of
def-weil-compactifications-refinements, with identity on X and Y. If X is empty, its
scheme-theoretic image is empty because the empty closed subscheme already contains it;
its pullback is empty too.
-/
theorem cartesian_closure_refinement
    (k : Type u) [Field k] (X V Xbar Y Ybar : Scheme.{u})
    (sX : X ⟶ Spec (.of k)) (sV : V ⟶ Spec (.of k))
    (sXbar : Xbar ⟶ Spec (.of k)) (sY : Y ⟶ Spec (.of k))
    (sYbar : Ybar ⟶ Spec (.of k))
    [LocallyOfFiniteType sX] [QuasiCompact sX]
    [LocallyOfFiniteType sV] [QuasiCompact sV]
    [LocallyOfFiniteType sXbar] [QuasiCompact sXbar]
    [LocallyOfFiniteType sY] [QuasiCompact sY]
    [LocallyOfFiniteType sYbar] [QuasiCompact sYbar]
    (j : X ⟶ V) (b : V ⟶ Xbar) (i : Y ⟶ Ybar)
    [IsOpenImmersion j] [IsOpenImmersion b] [IsOpenImmersion i]
    (q : V ⟶ Y) (p : Xbar ⟶ Ybar) [IsProper q] [IsProper p]
    (_hcomm : b ≫ p = q ≫ i) :
    IsClosedImmersion (j ≫ b).imageι ∧
    IsOpenImmersion (j ≫ b).toImage ∧
    (∀ U : (j ≫ b).image.Opens, Function.Injective ((j ≫ b).toImage.app U)) ∧
    IsProper (j ≫ b).imageι ∧
    IsProper ((j ≫ b).imageι ≫ p) ∧
    IsOpenImmersion (pullback.fst ((j ≫ b).imageι ≫ p) i) ∧
    IsProper (pullback.snd ((j ≫ b).imageι ≫ p) i) ∧
    IsPullback (pullback.fst ((j ≫ b).imageι ≫ p) i)
      (pullback.snd ((j ≫ b).imageι ≫ p) i) ((j ≫ b).imageι ≫ p) i ∧
    (IsEmpty X → IsEmpty (j ≫ b).image ∧
      IsEmpty (pullback ((j ≫ b).imageι ≫ p) i : Scheme.{u})) ∧
    ∃ (j' : X ⟶ pullback ((j ≫ b).imageι ≫ p) i)
      (v : pullback ((j ≫ b).imageι ≫ p) i ⟶ V),
      IsOpenImmersion j' ∧ QuasiCompact j' ∧ IsClosedImmersion v ∧ IsProper v ∧
      j' ≫ v = j ∧
      v ≫ b = pullback.fst ((j ≫ b).imageι ≫ p) i ≫ (j ≫ b).imageι ∧
      v ≫ q = pullback.snd ((j ≫ b).imageι ≫ p) i ∧
      pullback.fst ((j ≫ b).imageι ≫ p) i ≫ ((j ≫ b).imageι ≫ p) =
        pullback.snd ((j ≫ b).imageι ≫ p) i ≫ i ∧
      j' ≫ pullback.fst ((j ≫ b).imageι ≫ p) i = (j ≫ b).toImage ∧
      j' ≫ pullback.snd ((j ≫ b).imageι ≫ p) i = j ≫ q := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  have : IsNoetherian X := ⟨⟩
  have : IsLocallyNoetherian Xbar := LocallyOfFiniteType.isLocallyNoetherian sXbar
  let h := j ≫ b
  let a := h.imageι
  let u := h.toImage
  let f := a ≫ p
  -- First form the closed subscheme over V and the desired open part of the closure.
  let P := pullback a b
  let W := pullback f i
  let m : P ⟶ h.image := pullback.fst a b
  let n : P ⟶ V := pullback.snd a b
  let w : W ⟶ h.image := pullback.fst f i
  let r : W ⟶ Y := pullback.snd f i
  have hu : u ≫ a = h := Scheme.Hom.toImage_imageι h
  have hmn : m ≫ a = n ≫ b := pullback.condition
  have hwr : w ≫ f = r ≫ i := pullback.condition
  have huf : u ≫ f = (j ≫ q) ≫ i := by
    dsimp [f]
    rw [← Category.assoc, hu]
    dsimp [h]
    simp only [Category.assoc, _hcomm]
  let j' : X ⟶ W := pullback.lift u (j ≫ q) huf
  have hjw : j' ≫ w = u := pullback.lift_fst _ _ _
  have hjr : j' ≫ r = j ≫ q := pullback.lift_snd _ _ _
  have : IsOpenImmersion j' := by
    have : IsOpenImmersion (j' ≫ w) := by rw [hjw]; infer_instance
    exact IsOpenImmersion.of_comp j' w
  -- Density descends through the open projection to the closure.
  have : IsDominant j' := by
    have : IsDominant (j' ≫ w) := by rw [hjw]; infer_instance
    exact IsDominant.of_comp_of_isOpenImmersion j' w
  have hecond : m ≫ f = (n ≫ q) ≫ i := by
    dsimp [f]
    rw [← Category.assoc, hmn]
    simp only [Category.assoc, _hcomm]
  let e : P ⟶ W := pullback.lift m (n ≫ q) hecond
  have hew : e ≫ w = m := pullback.lift_fst _ _ _
  have her : e ≫ r = n ≫ q := pullback.lift_snd _ _ _
  have : IsOpenImmersion e := by
    have : IsOpenImmersion (e ≫ w) := by rw [hew]; infer_instance
    exact IsOpenImmersion.of_comp e w
  -- The comparison is proper over Y, using only the relative separatedness of r.
  have : IsProper e := by
    have : IsProper (e ≫ r) := by rw [her]; infer_instance
    exact IsProper.of_comp e r
  let t : X ⟶ P := pullback.lift u j hu
  have hte : t ≫ e = j' := by
    apply pullback.hom_ext
    · simp [Category.assoc, hew, t, m, j', w]
    · simp [Category.assoc, her, t, n, j', r]
  have : IsDominant e := by
    have : IsDominant (t ≫ e) := by rw [hte]; infer_instance
    exact IsDominant.of_comp t e
  -- Its closed image contains the dense image of X, so the open immersion is an iso.
  have : Surjective e := surjective_of_isDominant_of_isClosed_range e
    e.isClosedMap.isClosed_range
  have : IsIso e := (isIso_iff_isOpenImmersion_and_surjective e).mpr
    ⟨inferInstance, inferInstance⟩
  -- Transport the closed immersion P → V across that isomorphism.
  let v : W ⟶ V := inv e ≫ n
  have hvb : v ≫ b = w ≫ a := by
    dsimp [v]
    rw [Category.assoc, ← hmn, ← hew]
    simp
  have hvq : v ≫ q = r := by
    dsimp [v]
    rw [Category.assoc, ← her]
    simp
  have hjv : j' ≫ v = j := by
    apply (cancel_mono b).mp
    rw [Category.assoc, hvb, ← Category.assoc, hjw, hu]
  refine ⟨inferInstance, inferInstance, ?_, inferInstance, inferInstance,
    inferInstance, inferInstance, .of_hasPullback _ _, ?_,
    j', v, inferInstance, inferInstance, inferInstance, inferInstance,
    hjv, hvb, hvq, hwr, hjw, hjr⟩
  · exact (nagata_sketch_closure.1 h).2.2.1
  · intro hX
    have hW : IsEmpty h.image := by
      constructor
      intro x
      have hd := h.toImage.denseRange.closure_range
      have hrange : Set.range h.toImage = ∅ := Set.range_eq_empty_iff.mpr hX
      rw [hrange, closure_empty] at hd
      have hx : x ∈ (∅ : Set h.image) := hd.symm ▸ Set.mem_univ x
      exact hx
    exact ⟨hW, Function.isEmpty w⟩

end AlgebraicGeometry
