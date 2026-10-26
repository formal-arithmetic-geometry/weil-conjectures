/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J1
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.Cover.QuasiCompact
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen

/-! # Cofinal finite affine étale coverings

Source: literature/stacks-project/etale-cohomology.tex, Section 59.51, Tag 03Q4
(label section-colimit), first paragraph
(blueprint: lem-weil-pbc-etale-qcqs-cofinal-finite-coverings).
-/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
/--
For a quasi-compact and quasi-separated scheme, every jointly surjective étale
family admits a finite affine étale refinement with quasi-compact pairwise
fibre products.

Source: literature/stacks-project/etale-cohomology.tex, Section 59.51, Tag 03Q4
(label section-colimit), first paragraph, using Topologies, Lemma Tag 0218 and
Sites, Lemma Tag 0738 (blueprint: lem-weil-pbc-etale-qcqs-cofinal-finite-coverings).
Proof:
1. Choose a finite affine open cover `U_j` of `U` using
   `lem-weil-pbc-qcqs-scheme-cofinal-finite-coverings` (Stacks, Tag 01IT and
   quasi-compactness). Only quasi-compactness is needed for this step.
2. Restrict the given covering to each `U_j` by scheme fibre products
   (`def-pc-fibre-product`). The projections remain étale and jointly surjective by
   `lem-weil-pbc-etale-covering-base-change` (Stacks, Tag 0217 (3)).
3. On each affine `U_j`, apply `lem-weil-pbc-etale-covering-affine-refinement`
   (Stacks, Tag 0218) to obtain finitely many affine opens of the restricted sources.
   Index their union by pairs `(j, k)` and compose their maps with `U_j → U`.
4. The composites are étale, since open immersions are étale and étale morphisms
   compose (`lem-weil-pbc-etale-composition-cancellation`). The fibre square gives
   their factorization through the selected `T_a → U` (`def-pc-fibre-product`).
   Their images cover each `U_j`, hence their union covers `U`.
5. Each affine `V_b` is quasi-compact by
   `lem-weil-pbc-spec-basic-opens-unit-ideal-quasi-compact` (iii). Since `U` is
   quasi-separated, `V_b → U` is quasi-compact by
   `lem-weil-pbc-qcqs-morphism-permanence` (1). Its base change to `V_b'` is
   quasi-compact by (3), and its source is quasi-compact by (2).
6. Thus every covering in the small étale site (`def-weil-pbc-etale-site`) has a
   finite affine refinement with quasi-compact pairwise fibre products. This is
   exactly cofinality under refinement, the condition used in Stacks, Tag 0738 (4).

Lean form: `U` is the object `Scheme.Etale.mk (𝟙 U)` of its small étale site
`U.smallEtaleTopology`; a family `(T_a → U)` of étale morphisms is a family of
objects `T a` of `U.Etale` with their (unique) maps to it, and it is jointly surjective
exactly when its sieve covers (`Scheme.ofArrows_mem_smallEtaleTopology_iff`). A
factorization of `V_b → U` through `T_{a(b)} → U` is a morphism `V b ⟶ T (a b)` of
`U.Etale`, and `V_b ×_U V_b'` is the scheme fibre product of the structure maps.
-/
theorem etale_qcqs_cofinal_finite_affine_coverings
    {U : Scheme.{u}} [CompactSpace U] [QuasiSeparatedSpace U]
    {A : Type v} (T : A → U.Etale) (f : ∀ a, T a ⟶ Scheme.Etale.mk (𝟙 U))
    (hf : Sieve.ofArrows T f ∈ U.smallEtaleTopology (Scheme.Etale.mk (𝟙 U))) :
    ∃ (B : Type w) (_ : Finite B) (a : B → A) (V : B → U.Etale)
      (v : ∀ b, V b ⟶ Scheme.Etale.mk (𝟙 U)),
      (∀ b, IsAffine (V b).left) ∧
      (∀ b, ∃ h : V b ⟶ T (a b), h ≫ f (a b) = v b) ∧
      Sieve.ofArrows V v ∈ U.smallEtaleTopology (Scheme.Etale.mk (𝟙 U)) ∧
      (∀ b b', CompactSpace (pullback (C := Scheme.{u}) (V b).hom (V b').hom)) := by
  classical
  have hf' := (Scheme.ofArrows_mem_smallEtaleTopology_iff f).mp hf
  have hleft (a : A) : (f a).left = (T a).hom := by
    have h := CategoryTheory.MorphismProperty.Over.w (f a)
    change (f a).left ≫ 𝟙 U = (T a).hom at h
    change (f a).left = (T a).hom
    exact (Category.comp_id (f a).left).symm.trans h
  let C : U.Cover (Scheme.precoverage @Etale) :=
    Scheme.Cover.mkOfCovers A (fun a ↦ (T a).left) (fun a ↦ (T a).hom)
      (fun x ↦ by
        have hx : x ∈ ⋃ a, Set.range (f a).left := by rw [hf']; trivial
        obtain ⟨a, y, hy⟩ := Set.mem_iUnion.mp hx
        rw [hleft] at hy
        change (T a).hom y = x at hy
        exact ⟨a, y, hy⟩)
  let : QuasiCompactCover C.toPreZeroHypercover :=
    QuasiCompactCover.of_isOpenMap (fun a ↦ (C.f a).isOpenMap)
  obtain ⟨D, g, hfin, _⟩ := QuasiCompactCover.exists_hom C
  let : Finite D.I₀ := hfin
  let (b : D.I₀) : Etale (D.f b) := D.map_prop b
  let : Fintype D.I₀ := Fintype.ofFinite D.I₀
  let B := ULift.{w} (Fin (Fintype.card D.I₀))
  let e : B ≃ D.I₀ := Equiv.ulift.trans (Fintype.equivFin D.I₀).symm
  let V (b : B) : U.Etale := Scheme.Etale.mk (D.f (e b))
  let v (b : B) : V b ⟶ Scheme.Etale.mk (𝟙 U) :=
    CategoryTheory.MorphismProperty.Over.homMk (D.f (e b))
  refine ⟨B, inferInstance, (fun b ↦ g.s₀ (e b)), V, v, ?_, ?_, ?_, ?_⟩
  · intro b
    exact inferInstanceAs (IsAffine (Spec (D.X (e b))))
  · intro b
    refine ⟨CategoryTheory.MorphismProperty.Over.homMk (g.h₀ (e b)) (g.w₀ (e b)), ?_⟩
    apply CategoryTheory.MorphismProperty.Over.Hom.ext
    change g.h₀ (e b) ≫ (f (g.s₀ (e b))).left = D.f (e b)
    rw [hleft]
    exact g.w₀ (e b)
  · apply (Scheme.ofArrows_mem_smallEtaleTopology_iff v).mpr
    change (⋃ b, Set.range (D.f (e b))) = Set.univ
    exact (e.surjective.iUnion_comp (fun i ↦ Set.range (D.f i))).trans D.cover.iUnion_range
  · intro b b'
    exact inferInstanceAs (CompactSpace (pullback (C := Scheme.{u}) (D.f (e b)) (D.f (e b'))))

end AlgebraicGeometry
