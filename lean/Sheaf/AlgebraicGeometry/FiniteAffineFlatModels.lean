/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P2
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.RingTheory.TensorProduct.Basic
import Sheaf.AlgebraicGeometry.AffineOpenDirectedRingSystem
import Sheaf.AlgebraicGeometry.AffineChartTensorComparison

/-!
# Finite affine algebra models for flatness in an inverse system

Source: Stacks Project, Limits, proof of Tag 04AI, first paragraph; Tag 01YW.
(blueprint: lem-weil-pbc-finite-affine-flat-models).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- A finite family of affine algebra models detects flatness at every stage and at
an inverse limit. This is the geometric reduction of Tag 04AI, without its algebraic
flatness descent step.

Source: Stacks Project, Limits, proof of Tag 04AI, first paragraph; Tag 01YW.
(blueprint: lem-weil-pbc-finite-affine-flat-models).

Proof:
1. For each point of X₀ choose affine opens U ⊆ X₀, V ⊆ Y₀, W ⊆ S₀ with
   f₀(U) ⊆ V and Y₀.hom(V) ⊆ W. Affine opens form a basis, so such triples exist.
   Quasi-compactness of X₀ gives finitely many triples covering X₀. Their section
   rings give A₀ → B₀ → C₀. The map B₀ → C₀ is finitely presented because f₀ is
   locally of finite presentation (01TQ).
2. On the upper tail J, set Wⱼ = tⱼ₀⁻¹(W) and F(j) = Γ(Wⱼ). The transition maps
   on sections form a functor J → CommRingCat. Each Wⱼ is affine. By 01YW the
   inverse image W∞ in the given limit is Spec(colimit F), compatibly with the
   projection to W₀. In particular the ring maps used below are the canonical
   transition maps and colimit coprojection, rather than unrelated choices.
3. Open fibre products identify the inverse images of U and V over Sⱼ with
   U ×_W Wⱼ and V ×_W Wⱼ, and similarly over the limit. The affine pullback
   formula identifies their rings with F(j) ⊗[F(j₀)] C₀ and
   F(j) ⊗[F(j₀)] B₀. Under these identifications the restricted morphism is Spec
   of id ⊗ φ₀: its two projections agree by the pullback equations, which uniquely
   determine the morphism. The same assertion holds with colimit F in place of F(j).
4. These inverse images of U cover the source at every stage and at the limit.
   Flatness is local on source and target, invariant under isomorphisms, and
   Flat(Spec ψ) is equivalent to RingHom.Flat ψ. This gives both equivalences.
   If X₀ is empty take n = 0; both sides are then vacuously true. -/
theorem exists_finite_affine_flat_models
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (D : Iᵒᵖ ⥤ Scheme.{u})
    [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a)]
    (c : Cone D) (hc : IsLimit c) (i₀ : I)
    (X₀ Y₀ : Over (D.obj (op i₀))) (f₀ : X₀ ⟶ Y₀)
    [CompactSpace X₀.left] [LocallyOfFinitePresentation f₀.left] :
    let J := {i : I // i₀ ≤ i}
    let j₀ : J := ⟨i₀, le_rfl⟩
    ∃ (n : ℕ) (F : Fin n → J ⥤ CommRingCat.{u})
      (B C : (b : Fin n) → CommAlgCat.{u} (F b |>.obj j₀))
      (φ : (b : Fin n) → B b ⟶ C b),
      (∀ b, (φ b).hom.toRingHom.FinitePresentation) ∧
      (Flat (((Over.pullback (c.π.app (op i₀))).map f₀).left) ↔
        ∀ b,
          letI := (colimit.ι (F b) j₀).hom.toAlgebra
          (Algebra.TensorProduct.map
            (R := ((F b).obj j₀ : Type u))
            (S := (colimit (F b) : CommRingCat.{u}))
            (A := (colimit (F b) : CommRingCat.{u})) (B := B b)
            (C := (colimit (F b) : CommRingCat.{u})) (D := C b)
            (Algebra.ofId (colimit (F b) : CommRingCat.{u})
              (colimit (F b) : CommRingCat.{u})) (φ b).hom).toRingHom.Flat) ∧
      (∀ j : J,
        Flat (((Over.pullback (D.map (homOfLE j.property).op)).map f₀).left) ↔
          ∀ b,
            letI := ((F b).map (homOfLE (show j₀ ≤ j from j.property))).hom.toAlgebra
            (Algebra.TensorProduct.map
              (R := ((F b).obj j₀ : Type u)) (S := ((F b).obj j : Type u))
              (A := ((F b).obj j : Type u)) (B := B b)
              (C := ((F b).obj j : Type u)) (D := C b)
              (Algebra.ofId ((F b).obj j) ((F b).obj j)) (φ b).hom).toRingHom.Flat) := by
  classical
  dsimp only
  let J := {i : I // i₀ ≤ i}
  let j₀ : J := ⟨i₀, le_rfl⟩
  have triples (x : X₀.left) :
      ∃ (W : (D.obj (op i₀)).Opens) (V : Y₀.left.Opens) (U : X₀.left.Opens),
        IsAffineOpen W ∧ IsAffineOpen V ∧ IsAffineOpen U ∧
        V ≤ Y₀.hom ⁻¹ᵁ W ∧ U ≤ f₀.left ⁻¹ᵁ V ∧ x ∈ U := by
    obtain ⟨W, hW, hxW, _⟩ := exists_isAffineOpen_mem_and_subset
      (X := D.obj (op i₀)) (x := Y₀.hom (f₀.left x)) (U := ⊤) (by simp)
    obtain ⟨V, hV, hxV, eV⟩ := exists_isAffineOpen_mem_and_subset
      (X := Y₀.left) (x := f₀.left x) (U := Y₀.hom ⁻¹ᵁ W) hxW
    obtain ⟨U, hU, hxU, eU⟩ := exists_isAffineOpen_mem_and_subset
      (X := X₀.left) (x := x) (U := f₀.left ⁻¹ᵁ V) hxV
    exact ⟨W, V, U, hW, hV, hU, eV, eU, hxU⟩
  choose W V U hW hV hU eV eU hxU using triples
  have hcover : (Set.univ : Set X₀.left) ⊆ ⋃ x, (U x : Set X₀.left) := by
    intro x _
    exact Set.mem_iUnion.mpr ⟨x, hxU x⟩
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover
    (fun x ↦ (U x : Set X₀.left)) (fun x ↦ (U x).isOpen) hcover
  let e := (Fintype.equivFin s).symm
  let n := Fintype.card s
  let Ub (b : Fin n) := U (e b)
  have hUb : (⨆ b, Ub b) = ⊤ := by
    apply top_unique
    intro x _
    obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.mp (hs (Set.mem_univ x))
    obtain ⟨b, hb⟩ := e.surjective ⟨y, hy⟩
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨b, by simpa [Ub, hb] using hxy⟩
  have models (b : Fin n) :=
    exists_affineOpen_directedRingSystem D c hc i₀ (W (e b)) (hW (e b))
  choose F e0 hi eL hL using models
  have charts (b : Fin n) := exists_affineChart_tensorComparison X₀ Y₀ f₀
    (W (e b)) (hW (e b)) (V (e b)) (hV (e b)) (eV (e b))
    (Ub b) (hU (e b)) (eU (e b)) (F b |>.obj j₀) (e0 b)
  choose B C aB aC φ hφ hcomp using charts
  let B' (b : Fin n) : CommAlgCat ((F b).obj j₀) :=
    let := aB b
    CommAlgCat.of ((F b).obj j₀) (B b)
  let C' (b : Fin n) : CommAlgCat ((F b).obj j₀) :=
    let := aC b
    CommAlgCat.of ((F b).obj j₀) (C b)
  let φ' (b : Fin n) : B' b ⟶ C' b := CommAlgCat.ofHom (φ b)
  refine ⟨n, F, B', C', φ', hφ, ?_, ?_⟩
  · rw [IsZariskiLocalAtSource.iff_of_iSup_eq_top
      (P := @Flat) (fun b ↦ (pullback.fst X₀.hom (c.π.app (op i₀))) ⁻¹ᵁ Ub b)
      ((pullback.fst X₀.hom (c.π.app (op i₀))).iSup_preimage_eq_top hUb)]
    apply forall_congr'
    intro b
    let := aB b
    let := aC b
    let aL := (colimit.ι (F b) j₀).hom.toAlgebra
    let := aL
    obtain ⟨g, hg, ⟨eg⟩⟩ := hcomp b c.pt (c.π.app (op i₀)) (colimit (F b))
      aL (eL b) (hL b)
    rw [← hg]
    exact (MorphismProperty.postcomp_iff (W := @Flat) (W' := @IsOpenImmersion)
      g _ inferInstance).trans
      ((MorphismProperty.arrow_mk_iso_iff (P := @Flat) eg).trans Flat.SpecMap_iff)
  · intro j
    rw [IsZariskiLocalAtSource.iff_of_iSup_eq_top
      (P := @Flat) (fun b ↦ (pullback.fst X₀.hom
        (D.map (homOfLE j.property).op)) ⁻¹ᵁ Ub b)
      ((pullback.fst X₀.hom (D.map (homOfLE j.property).op)).iSup_preimage_eq_top hUb)]
    apply forall_congr'
    intro b
    let := aB b
    let := aC b
    let aj := ((F b).map (homOfLE (show j₀ ≤ j from j.property))).hom.toAlgebra
    let := aj
    obtain ⟨ej, hej⟩ := hi b j
    obtain ⟨g, hg, ⟨eg⟩⟩ := hcomp b (D.obj (op j.val))
      (D.map (homOfLE j.property).op) ((F b).obj j) aj ej hej
    rw [← hg]
    exact (MorphismProperty.postcomp_iff (W := @Flat) (W' := @IsOpenImmersion)
      g _ inferInstance).trans
      ((MorphismProperty.arrow_mk_iso_iff (P := @Flat) eg).trans Flat.SpecMap_iff)

end AlgebraicGeometry
