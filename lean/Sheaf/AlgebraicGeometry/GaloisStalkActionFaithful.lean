/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE
-/
module

public import Mathlib.AlgebraicGeometry.Sites.EtalePoint

/-! Faithfulness of the canonical Galois stalk functor.
Source: Stacks Project, Tags 03QT and 04JM (blueprint: lem-exc-galois-stalk-action-faithful).
-/

@[expose] public section

universe u v

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme

/-- Source: Stacks Project, Tags 03QT and 04JM.
(blueprint: lem-exc-galois-stalk-action-faithful).

Proof: Equal germs become equal on a pointed refinement by the stalk colimit equality
criterion. Every point of an etale scheme over K lifts to Omega, so these refinements
cover every point. Consequently the equalizer sieve is covering, and sheaf separatedness
makes the section values equal. Applying this to each section of each object proves
faithfulness. This also handles the empty scheme through the empty covering sieve. -/
theorem field_sheafFiber_faithful (K Ω : Type u) [Field K] [Field Ω]
    [Algebra K Ω] [IsAlgClosed Ω] :
    ((pointSmallEtale (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))).sheafFiber
      (A := Type (max (u + 1) v))).Faithful := by
  let s := Spec.map (CommRingCat.ofHom (algebraMap K Ω))
  let p := pointSmallEtale s
  refine ⟨fun {F F'} φ ψ h ↦ ?_⟩
  apply Sheaf.hom_ext
  ext U z
  let R := Presheaf.equalizerSieve (F := F'.obj) (X := U) (φ.hom.app U z) (ψ.hom.app U z)
  have hR : R ∈ (Spec (.of K)).smallEtaleTopology U.unop := by
    obtain ⟨ι, Y, f, hf⟩ := R.exists_eq_ofArrows
    rw [hf, ofArrows_mem_smallEtaleTopology_iff]
    ext y
    simp only [Set.mem_iUnion, Set.mem_range, Set.mem_univ, iff_true]
    have : AlgebraicGeometry.Etale U.unop.hom := U.unop.prop
    obtain ⟨l, hl, hy⟩ := exists_fac_of_etale_of_isSepClosed U.unop.hom s y
      (Subsingleton.elim (α := Spec (.of K)) _ _)
    let x : p.fiber.obj U.unop := Over.homMk l hl
    have hz : p.toPresheafFiber U.unop x F'.obj (φ.hom.app U z) =
        p.toPresheafFiber U.unop x F'.obj (ψ.hom.app U z) := by
      rw [← p.toPresheafFiber_naturality_apply,
        ← p.toPresheafFiber_naturality_apply]
      exact ConcreteCategory.congr_hom h _
    obtain ⟨Z, g, t, ht, he⟩ := (p.toPresheafFiber_eq_iff' _ _ _ _).mp hz
    have hg : R g := he
    rw [hf] at hg
    obtain ⟨W, a, b, ⟨i⟩, hab⟩ := hg
    refine ⟨i, a.left (t.left (default : Spec (.of Ω))), ?_⟩
    have hfac : g.left = a.left ≫ (f i).left := by
      exact congrArg (fun q ↦ q.left) hab.symm
    have ht' : t.left ≫ g.left = x.left := congrArg (fun q ↦ q.left) ht
    rw [hfac] at ht'
    have := congrArg (fun q : Spec (.of Ω) ⟶ U.unop.left ↦ q default) ht'
    change (f i).left (a.left (t.left (default : Spec (.of Ω)))) = l default at this
    exact this.trans hy
  exact Sheaf.isSeparated F' U.unop R hR _ _ (fun Y f hf ↦ hf)

end AlgebraicGeometry.Scheme
