/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T2
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceJointSurjectivity
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.AlgebraicGeometry.ResidueField

/-! # Point covers and fppf-local lifting for representable etale families

Source: Stacks Project, Topologies on Spaces, Tag 041F, and Properties of Spaces,
Tag 03BU (blueprint: lem-trf-etale-point-cover-fppf-lifting).
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

/-- An etale family of scheme charts covers point classes precisely when every scheme
section lifts fppf locally to one of its members. The index universe is independent of
the scheme universe; empty families and empty test schemes are included.

Source: Stacks, Topologies on Spaces, Tag 041F, and Properties of Spaces, Tag 03BU
(blueprint: lem-trf-etale-point-cover-fppf-lifting).

Proof: for each scheme test T -> Y, represent the pullback of every chart by U_i -> T.
These maps are etale. If the family covers point classes, apply the lifting condition
to the residue-field representative of each point of T. The lift over a field extension
gives a point of some U_i above that point. Thus the U_i -> T form a jointly surjective
etale, hence fppf, scheme covering. Its generated sieve is contained in the displayed
factorization sieve, proving the covering assertion. Conversely apply that assertion
to a field-valued section. Refine its covering sieve by an fppf scheme family. A member
has a point above the unique point of the field spectrum. Its residue field is an
extension of the original field and its residue-field section factors through a chart.
This is exactly the required extension-lifting equality. Downward closure of the
factorization condition removes the extra factor in Sieve.generate. For an empty test
the empty sieve covers, and an empty index forces all field-valued sections to be absent.
-/
theorem isJointlySurjective_iff_fppf_lifting
    {S : Scheme.{u}} {Y : AlgebraicSpace S} {I : Type v}
    (V : I → Y.EtaleSite) :
    IsJointlySurjective (fun i : I ↦ (V i).obj.hom) ↔
      ∀ (T : Over S) (a : yoneda.obj T ⟶ Y.obj.obj),
        Sieve.generate (fun (U : Over S) (k : U ⟶ T) ↦
          ∃ (i : I) (b : U ⟶ (V i).obj.left),
            yoneda.map k ≫ a = yoneda.map b ≫ (V i).obj.hom) ∈
              (Scheme.fppfTopology.over S) T := by
  classical
  constructor
  · intro hs T a
    choose U p q hsq het using fun i : I ↦ (V i).property T a
    have hsurj : ∀ x : T.left, ∃ i : I, x ∈ Set.range (p i).left := by
      intro x
      let K : Type u := T.left.residueField x
      let s := T.left.fromSpecResidueField x ≫ T.hom
      let t : Over.mk s ⟶ T := Over.homMk (T.left.fromSpecResidueField x)
      obtain ⟨i, L, hL, d, y, hy⟩ := hs K s (yonedaEquiv (yoneda.map t ≫ a))
      let := hL
      let b : Over.mk (Spec.map (CommRingCat.ofHom d) ≫ s) ⟶ Over.mk s :=
        Over.homMk (Spec.map (CommRingCat.ofHom d)) rfl
      have hxy : yoneda.map y ≫ (V i).obj.hom = yoneda.map (b ≫ t) ≫ a := by
        apply yonedaEquiv.injective
        rw [yonedaEquiv_comp, yonedaEquiv_yoneda_map, hy,
          Functor.map_comp, Category.assoc, yonedaEquiv_naturality]
      let l := (hsq i).lift (yoneda.map y) (yoneda.map (b ≫ t)) hxy
      let w := yoneda.preimage l
      have hw : w ≫ p i = b ≫ t := by
        apply yoneda.map_injective
        rw [Functor.map_comp, yoneda.map_preimage]
        exact (hsq i).lift_snd _ _ hxy
      refine ⟨i, w.left (IsLocalRing.closedPoint L), ?_⟩
      have hpoint := congrArg (fun z ↦ z.left (IsLocalRing.closedPoint L)) hw
      simpa [b, t, Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply] using hpoint
    have hcov : Presieve.ofArrows (fun i ↦ (U i).left) (fun i ↦ (p i).left) ∈
        Scheme.etalePrecoverage T.left := by
      rw [Scheme.etalePrecoverage, Scheme.ofArrows_mem_precoverage_iff]
      exact ⟨hsurj, het⟩
    have hR : Sieve.ofArrows U p ∈ (Scheme.fppfTopology.over S) T := by
      apply (Scheme.fppfTopology.mem_over_iff _).mpr
      rw [Sieve.overEquiv_ofArrows]
      exact Scheme.etaleTopology_le_fppfTopology _
        (Precoverage.generate_mem_toGrothendieck hcov)
    apply (Scheme.fppfTopology.over S).superset_covering _ hR
    rintro W k ⟨Z, c, d, ⟨i⟩, hcd⟩
    apply Sieve.le_generate
    refine ⟨i, c ≫ yoneda.preimage (q i), ?_⟩
    rw [Functor.map_comp, yoneda.map_preimage, Category.assoc, (hsq i).w,
      ← Category.assoc, ← Functor.map_comp, hcd]
  · intro hcover K _ s x
    let T := Over.mk s
    let a : yoneda.obj T ⟶ Y.obj.obj := yonedaEquiv.symm x
    let Q := Sieve.generate (fun (U : Over S) (k : U ⟶ T) ↦
      ∃ (i : I) (b : U ⟶ (V i).obj.left),
        yoneda.map k ≫ a = yoneda.map b ≫ (V i).obj.hom)
    obtain ⟨Z, g, hg, _hflat, _hfp, z, _hz⟩ :=
      Scheme.exists_flat_mem_of_mem_fppfTopology_over
        (hcover T a) (IsLocalRing.closedPoint K)
    change Q g at hg
    obtain ⟨W, c, k, ⟨i, d, hd⟩, hck⟩ := hg
    let L : Type u := Z.left.residueField z
    let q : Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of K) :=
      Z.left.fromSpecResidueField z ≫ g.left
    let e : CommRingCat.of K ⟶ CommRingCat.of L := Spec.preimage q
    have he : Spec.map e = q := Spec.map_preimage q
    let b : Over.mk (Spec.map e ≫ s) ⟶ Z :=
      Over.homMk (Z.left.fromSpecResidueField z) (by
        change Z.left.fromSpecResidueField z ≫ Z.hom = Spec.map e ≫ s
        rw [he]
        change Z.left.fromSpecResidueField z ≫ Z.hom =
          (Z.left.fromSpecResidueField z ≫ g.left) ≫ T.hom
        rw [Category.assoc, Over.w g])
    let t : Over.mk (Spec.map e ≫ s) ⟶ T := Over.homMk (Spec.map e) rfl
    have hbg : b ≫ g = t := by
      apply Over.OverMorphism.ext
      exact he.symm
    refine ⟨i, L, inferInstance, e.hom, b ≫ c ≫ d, ?_⟩
    have hnat : yoneda.map (b ≫ c ≫ d) ≫ (V i).obj.hom = yoneda.map t ≫ a := by
      rw [Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc,
        ← hd, ← Category.assoc, ← Functor.map_comp, ← Category.assoc,
        ← Functor.map_comp, Category.assoc, hck, hbg]
    change (V i).obj.hom.app _ (b ≫ c ≫ d) = Y.obj.obj.map t.op x
    calc
      _ = yonedaEquiv (yoneda.map t ≫ a) := by
        rw [← hnat, yonedaEquiv_comp, yonedaEquiv_yoneda_map]
        rfl
      _ = _ := by
        rw [← yonedaEquiv_naturality]
        simp only [a, Equiv.apply_symm_apply]


end AlgebraicGeometry.AlgebraicSpace
