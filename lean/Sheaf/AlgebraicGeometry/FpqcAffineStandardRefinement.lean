/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.RingTheory.RingHom.FaithfullyFlat

/-!
# Finite standard affine refinements of fpqc coverings

Source: Stacks Project, Topologies, Definition 022B, and Descent, Lemma 03N0
(blueprint: lem-weil-pbc-fpqc-affine-standard-refinement).
-/

@[expose] public section

universe u v

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- An fpqc covering of `Spec R` admits finitely many affine opens of its members such
that the induced map from `R` to the product of their coordinate rings is faithfully flat.
Source: Stacks Project, Definition 022B and Lemma 03N0
(blueprint: lem-weil-pbc-fpqc-affine-standard-refinement).

Proof:
1. Apply the affine-open condition of `def-weil-pbc-fpqc-covering` to the whole base.
   Select finitely many affine opens whose images cover it, allowing the empty family
   when the base is empty. Quasi-compact opens in Mathlib's formulation can be covered
   by finitely many affine opens.
2. Each coordinate map is flat by `lem-weil-pbc-flat-morphism-affine-criterion`
   (Stacks 01U5). Their finite product is flat by
   `lem-weil-pbc-finite-product-flat-modules`.
3. Every prime of `R` lifts to one selected coordinate ring because the images cover
   the base. Pull that prime back along the coordinate projection from the product.
   Thus the product map is surjective on spectra and is faithfully flat by
   `lem-weil-pbc-flat-surjective-spectrum-faithfully-flat` (Stacks 00HQ).
The coordinate ring of an affine open is the global-section ring of its open subscheme;
its spectrum is canonically isomorphic to that subscheme. -/
theorem exists_fpqc_affine_standard_refinement (R : CommRingCat.{u})
    {I : Type v} (T : I → Scheme.{u}) (f : ∀ i, T i ⟶ Spec R)
    (hf : Presieve.ofArrows T f ∈ fpqcPrecoverage (Spec R)) :
    ∃ (n : ℕ) (a : Fin n → I) (V : ∀ j, (T (a j)).Opens),
      (∀ j, IsAffineOpen (V j)) ∧
      (RingHom.pi (fun j : Fin n ↦
        ((ΓSpecIso R).inv ≫ ((V j).ι ≫ f (a j)).appTop).hom)).FaithfullyFlat := by
  classical
  let E : PreZeroHypercover (Spec R) := ⟨I, T, f⟩
  have hqc : QuasiCompactCover E := presieve₀_mem_qcPrecoverage_iff.mp hf.1
  have hflat : ∀ i, Flat (f i) := ((ofArrows_mem_precoverage_iff @Flat).mp hf.2).2
  obtain ⟨n, a, V, hV, hcover⟩ :=
    QuasiCompactCover.exists_isAffineOpen_of_isCompact E (isAffineOpen_top _).isCompact
  have : ∀ j, IsAffine (V j).toScheme := hV
  let A (j : Fin n) := Γ((V j).toScheme, ⊤)
  let g (j : Fin n) : R →+* A j :=
    ((ΓSpecIso R).inv ≫ ((V j).ι ≫ f (a j)).appTop).hom
  have hg : ∀ j, (g j).Flat := by
    intro j
    have : Flat (f (a j)) := hflat _
    exact RingHom.Flat.comp
      (RingHom.Flat.of_bijective (ConcreteCategory.bijective_of_isIso (ΓSpecIso R).inv))
      (((V j).ι ≫ f (a j)).flat_appTop)
  let : ∀ j, Algebra R (A j) := fun j ↦ (g j).toAlgebra
  have : ∀ j, Module.Flat R (A j) := hg
  have hpi : (RingHom.pi g).Flat := by
    change Module.Flat R (∀ j, A j)
    exact Module.Flat.of_linearEquiv
      (DirectSum.linearEquivFunOnFintype R (Fin n) (fun j ↦ ↥(A j))).symm
  refine ⟨n, a, V, hV, RingHom.FaithfullyFlat.iff_flat_and_comap_surjective.mpr ⟨hpi, ?_⟩⟩
  intro p
  have hp : p ∈ ⋃ j, f (a j) '' (V j) := by
    rw [hcover]
    trivial
  obtain ⟨j, x, hx, hxp⟩ := Set.mem_iUnion.mp hp
  let q : PrimeSpectrum (A j) := (V j).toScheme.isoSpec.hom ⟨x, hx⟩
  have hq : PrimeSpectrum.comap (g j) q = p := by
    change (Spec.map (CommRingCat.ofHom (g j)))
      ((V j).toScheme.isoSpec.hom ⟨x, hx⟩) = p
    have heq : (V j).toScheme.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom (g j)) =
        (V j).ι ≫ f (a j) := by
      change (V j).toScheme.toSpecΓ ≫
        Spec.map ((ΓSpecIso R).inv ≫ ((V j).ι ≫ f (a j)).appTop) = _
      rw [Spec.map_comp, ← Category.assoc, ← toSpecΓ_naturality,
        Category.assoc, toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]
    exact (congrArg (fun k : (V j).toScheme ⟶ Spec R ↦ k ⟨x, hx⟩) heq).trans hxp
  refine ⟨PrimeSpectrum.comap (Pi.evalRingHom (fun j ↦ ↥(A j)) j) q, ?_⟩
  rw [← PrimeSpectrum.comap_comp_apply]
  exact hq

end AlgebraicGeometry.Scheme
