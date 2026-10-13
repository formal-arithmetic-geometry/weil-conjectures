/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ConstantGroupScheme
import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
# Multiplication of the constant group scheme

Source: Stacks Project, Groupoids, Example 39.5.6 (Tag 03YW), and Schemes,
Section 26.14 (Tag 01JA) (blueprint: lem-weil-pbc-constant-group-scheme-multiplication).
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

variable (T : Scheme.{u}) (E : Type v) [Small.{u} E] [AddCommGroup E]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The pair components of the fibre square are clopen, disjoint and covering; the
componentwise maps glue uniquely to multiplication, with the stated properties.
Source: Stacks Project, Groupoids, Example 39.5.6 (Tag 03YW), and Schemes,
Section 26.14 (Tag 01JA) (blueprint: lem-weil-pbc-constant-group-scheme-multiplication).

Proof:
1. By `lem-weil-pbc-scheme-coproduct-family`, the images of the coprojections are
clopen, disjoint and covering. Pull them back along both projections of the fibre
product (`def-pc-fibre-product`); continuity gives clopenness of their intersections.
Distinct pairs differ in a coordinate, giving disjointness; choosing components for
both projections of a point gives coverage. The pullback relation identifies the
two composites to `T`.
2. Regard each pair component as an open subscheme (`def-weil-open-immersion`).
Compose its inclusion with the base projection and the coprojection indexed by the
sum. These local morphisms agree on overlaps: identical indices give identical maps,
and distinct indices give the empty scheme, an initial object.
3. Apply `lem-weil-pbc-scheme-morphism-gluing` to this open cover and these compatible
local maps to obtain a scheme morphism with the prescribed restrictions, unique among all
scheme morphisms having these restrictions.
4. Its composite with the codiagonal restricts to the base projection on every
component, since the codiagonal composed with a coprojection is the identity.
Gluing uniqueness gives the global equality. The restriction formula on points
also puts the image of each pair component in the component indexed by its sum.
5. For a fixed `d`, all pair components summing to `d` lie in its component preimage.
Conversely choose a pair component containing a point in that preimage. Its image
lies in both the component indexed by the sum and that indexed by `d`. Disjointness
of coproduct components forces the sum to equal `d`, proving the preimage formula.
The cover maps used below are open immersions with image exactly the pair components,
so equality after their composition is equality of restrictions as scheme morphisms.
-/
theorem constantGroupSchemeMultiplication_properties :
    (∀ ij : E × E,
      IsOpen (constantGroupSchemePairComponent T E ij.1 ij.2) ∧
        IsClosed (constantGroupSchemePairComponent T E ij.1 ij.2)) ∧
    (∀ ij ij' : E × E, ij ≠ ij' →
      Disjoint (constantGroupSchemePairComponent T E ij.1 ij.2)
        (constantGroupSchemePairComponent T E ij'.1 ij'.2)) ∧
    (⋃ ij : E × E, constantGroupSchemePairComponent T E ij.1 ij.2 = Set.univ) ∧
    ∃ m : constantGroupSchemeSquare T E ⟶ constantGroupScheme T E,
      (∀ ij : E × E,
        let j := (Scheme.Pullback.openCoverOfLeftRight
          (sigmaOpenCover (fun _ : E => T)) (sigmaOpenCover (fun _ : E => T))
          (constantGroupSchemeProjection T E) (constantGroupSchemeProjection T E)).f ij
        j ≫ m = j ≫ constantGroupSchemeSquareProjection T E ≫
          constantGroupSchemeIncl T E (ij.1 + ij.2)) ∧
      (∀ m' : constantGroupSchemeSquare T E ⟶ constantGroupScheme T E,
        (∀ ij : E × E,
          let j := (Scheme.Pullback.openCoverOfLeftRight
            (sigmaOpenCover (fun _ : E => T)) (sigmaOpenCover (fun _ : E => T))
            (constantGroupSchemeProjection T E) (constantGroupSchemeProjection T E)).f ij
          j ≫ m' = j ≫ constantGroupSchemeSquareProjection T E ≫
            constantGroupSchemeIncl T E (ij.1 + ij.2)) → m' = m) ∧
      m ≫ constantGroupSchemeProjection T E = constantGroupSchemeSquareProjection T E ∧
      (∀ ij : E × E,
        Set.MapsTo (m : constantGroupSchemeSquare T E → constantGroupScheme T E)
          (constantGroupSchemePairComponent T E ij.1 ij.2)
          (constantGroupSchemeComponent T E (ij.1 + ij.2))) ∧
      (∀ d : E,
        m ⁻¹' (constantGroupSchemeComponent T E d) =
          ⋃ ij : {ij : E × E // ij.1 + ij.2 = d},
            constantGroupSchemePairComponent T E ij.1.1 ij.1.2) := by
  classical
  let C := Scheme.Pullback.openCoverOfLeftRight
    (sigmaOpenCover (fun _ : E => T)) (sigmaOpenCover (fun _ : E => T))
    (constantGroupSchemeProjection T E) (constantGroupSchemeProjection T E)
  have hVopen (e : E) : IsOpen (constantGroupSchemeComponent T E e) :=
    IsOpenImmersion.isOpen_range (Sigma.ι (fun _ : E => T) e)
  have hVdisj (e d : E) (h : e ≠ d) :
      Disjoint (constantGroupSchemeComponent T E e) (constantGroupSchemeComponent T E d) := by
    rw [Set.disjoint_left]
    rintro x ⟨a, ha⟩ ⟨b, hb⟩
    have he := (sigmaι_eq_iff (fun _ : E => T) e d a b).mp (ha.trans hb.symm)
    exact h (congrArg Sigma.fst he)
  have hVcover (x : constantGroupScheme T E) :
      ∃ e : E, x ∈ constantGroupSchemeComponent T E e := by
    obtain ⟨e, y, hy⟩ := (sigmaOpenCover (fun _ : E => T)).exists_eq x
    exact ⟨e, y, hy⟩
  have hVclosed (e : E) : IsClosed (constantGroupSchemeComponent T E e) := by
    have hc : (constantGroupSchemeComponent T E e)ᶜ =
        ⋃ d : {d : E // d ≠ e}, constantGroupSchemeComponent T E d := by
      ext x
      simp only [Set.mem_compl_iff, Set.mem_iUnion]
      constructor
      · intro hx
        obtain ⟨d, hd⟩ := hVcover x
        exact ⟨⟨d, fun h ↦ hx (h ▸ hd)⟩, hd⟩
      · rintro ⟨d, hd⟩ he
        exact Set.disjoint_left.mp (hVdisj d e d.2) hd he
    rw [← isOpen_compl_iff, hc]
    exact isOpen_iUnion fun d ↦ hVopen d
  have hWdisj (ij ij' : E × E) (h : ij ≠ ij') :
      Disjoint (constantGroupSchemePairComponent T E ij.1 ij.2)
        (constantGroupSchemePairComponent T E ij'.1 ij'.2) := by
    rw [Set.disjoint_left]
    intro x hx hy
    by_cases h1 : ij.1 = ij'.1
    · have h2 : ij.2 ≠ ij'.2 := fun h2 ↦ h (Prod.ext h1 h2)
      exact Set.disjoint_left.mp (hVdisj _ _ h2) hx.2 hy.2
    · exact Set.disjoint_left.mp (hVdisj _ _ h1) hx.1 hy.1
  have hWcover (x : constantGroupSchemeSquare T E) :
      ∃ ij : E × E, x ∈ constantGroupSchemePairComponent T E ij.1 ij.2 := by
    obtain ⟨e, he⟩ := hVcover (pullback.fst (constantGroupSchemeProjection T E)
      (constantGroupSchemeProjection T E) x)
    obtain ⟨d, hd⟩ := hVcover (pullback.snd (constantGroupSchemeProjection T E)
      (constantGroupSchemeProjection T E) x)
    exact ⟨(e, d), he, hd⟩
  have hRange (ij : E × E) :
      Set.range (C.f ij) = constantGroupSchemePairComponent T E ij.1 ij.2 := by
    dsimp only [C]
    rw [Scheme.Pullback.openCoverOfLeftRight_f]
    refine (Scheme.Pullback.range_map
      (f := (sigmaOpenCover (fun _ : E => T)).f ij.1 ≫ constantGroupSchemeProjection T E)
      (g := (sigmaOpenCover (fun _ : E => T)).f ij.2 ≫ constantGroupSchemeProjection T E)
      (constantGroupSchemeProjection T E) (constantGroupSchemeProjection T E)
      ((sigmaOpenCover (fun _ : E => T)).f ij.1)
      ((sigmaOpenCover (fun _ : E => T)).f ij.2) (𝟙 T)
      (Category.comp_id _) (Category.comp_id _)).trans ?_
    rfl
  refine ⟨?_, hWdisj, ?_, ?_⟩
  · intro ij
    change IsOpen ((pullback.fst (constantGroupSchemeProjection T E)
        (constantGroupSchemeProjection T E)) ⁻¹' constantGroupSchemeComponent T E ij.1 ∩
        (pullback.snd (constantGroupSchemeProjection T E)
        (constantGroupSchemeProjection T E)) ⁻¹' constantGroupSchemeComponent T E ij.2) ∧
      IsClosed ((pullback.fst (constantGroupSchemeProjection T E)
        (constantGroupSchemeProjection T E)) ⁻¹' constantGroupSchemeComponent T E ij.1 ∩
        (pullback.snd (constantGroupSchemeProjection T E)
        (constantGroupSchemeProjection T E)) ⁻¹' constantGroupSchemeComponent T E ij.2)
    exact ⟨((hVopen _).preimage (pullback.fst (constantGroupSchemeProjection T E)
          (constantGroupSchemeProjection T E)).continuous).inter
        ((hVopen _).preimage (pullback.snd (constantGroupSchemeProjection T E)
          (constantGroupSchemeProjection T E)).continuous),
      ((hVclosed _).preimage (pullback.fst (constantGroupSchemeProjection T E)
          (constantGroupSchemeProjection T E)).continuous).inter
        ((hVclosed _).preimage (pullback.snd (constantGroupSchemeProjection T E)
          (constantGroupSchemeProjection T E)).continuous)⟩
  · apply Set.eq_univ_of_forall
    intro x
    obtain ⟨ij, hx⟩ := hWcover x
    exact Set.mem_iUnion.mpr ⟨ij, hx⟩
  · let f := fun ij : E × E ↦ C.f ij ≫ constantGroupSchemeSquareProjection T E ≫
        constantGroupSchemeIncl T E (ij.1 + ij.2)
    have hf : ∀ ij ij', pullback.fst (C.f ij) (C.f ij') ≫ f ij =
        pullback.snd (C.f ij) (C.f ij') ≫ f ij' := by
      intro ij ij'
      by_cases h : ij = ij'
      · subst ij'
        dsimp [f]
        simp only [← Category.assoc, pullback.condition]
      · have : IsEmpty ↥(pullback (C.f ij) (C.f ij')) :=
          Scheme.isEmpty_pullback (C.f ij) (C.f ij')
            (by rw [hRange ij, hRange ij']; exact hWdisj _ _ h)
        exact (isInitialOfIsEmpty).hom_ext _ _
    let m := C.glueMorphisms f hf
    have hm (ij : E × E) : C.f ij ≫ m = f ij := C.ι_glueMorphisms f hf ij
    have hmaps (ij : E × E) :
        Set.MapsTo m (constantGroupSchemePairComponent T E ij.1 ij.2)
          (constantGroupSchemeComponent T E (ij.1 + ij.2)) := by
      intro x hx
      obtain ⟨y, rfl⟩ := (hRange ij).symm ▸ hx
      refine ⟨(constantGroupSchemeSquareProjection T E) (C.f ij y), ?_⟩
      exact (congrArg (fun k ↦ k y) (hm ij)).symm
    refine ⟨m, hm, ?_, ?_, hmaps, ?_⟩
    · intro m' hm'
      exact C.hom_ext _ _ fun ij ↦ (hm' ij).trans (hm ij).symm
    · apply C.hom_ext
      intro ij
      rw [← Category.assoc, hm]
      simp [f, constantGroupSchemeIncl, constantGroupSchemeProjection]
    · intro d
      ext x
      simp only [Set.mem_preimage, Set.mem_iUnion]
      constructor
      · intro hx
        obtain ⟨ij, hij⟩ := hWcover x
        have hs : ij.1 + ij.2 = d := by
          by_contra h
          exact Set.disjoint_left.mp (hVdisj _ _ h) (hmaps ij hij) hx
        exact ⟨⟨ij, hs⟩, hij⟩
      · rintro ⟨ij, hij⟩
        change m x ∈ constantGroupSchemeComponent T E d
        have hx := hmaps ij.1 hij
        change m x ∈ constantGroupSchemeComponent T E (ij.1.1 + ij.1.2) at hx
        rw [ij.2] at hx
        exact hx

end AlgebraicGeometry
