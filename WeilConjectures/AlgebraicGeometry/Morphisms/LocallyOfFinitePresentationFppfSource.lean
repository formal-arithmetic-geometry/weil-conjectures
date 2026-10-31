/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Limits
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation

/-!
# Local finite presentation is fppf local on the source

Source: Stacks Project, Descent, Tag 036N,
`lemma-locally-finite-presentation-fppf-local-source`
(blueprint: lem-trf-lfp-fppf-source-locality).
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A morphism is locally of finite presentation exactly when its composites with a jointly
surjective family of flat locally finitely presented source maps are locally of finite
presentation. The index type may be empty, and no quasi-compactness, separation or Noetherian
hypothesis is required.

Source: Stacks Project, Descent, Tag 036N, with affine reduction Tag 036H and algebra input
Tag 02KK (blueprint: lem-trf-lfp-fppf-source-locality).

Proof, following the eight steps of the node:
1. If `f` is locally of finite presentation, so is every `h i ≫ f` by
   `lem-sbc-locally-finite-presentation-composition`. For the converse assume the latter.
2. Fix `x : X`. By `lem-weil-pbc-affine-opens-basis`, choose affine neighbourhoods
   `V = Spec R` of `f x` and `W = Spec A` of `x` with `W` mapping into `V`. Cover each
   inverse image of `W` in `U i` by affine opens `T_ia = Spec B_ia`. By
   `def-sbc-locally-finite-presentation`, it suffices to show `R → A` finitely presented.
   If `X` is empty there are no points to check, including when the family is empty.
3. By `lem-weil-pbc-flat-morphism-affine-criterion`, each `A → B_ia` is flat.
   By `lem-weil-pbc-lfp-affine-opens-finite-presentation` for `h i` and `h i ≫ f`,
   both `A → B_ia` and `R → B_ia` are finitely presented. These form compatible towers
   `R → A → B_ia` because the second map of schemes is the composite.
4. By `lem-weil-pbc-flat-lfp-open`, every `h i` is open. Joint surjectivity implies
   that the open images of the `T_ia` cover `W`. The affine scheme `W` is quasi-compact
   by `lem-weil-pbc-affine-scheme-qcqs`; select finitely many images covering `W`.
5. Form the finite coproduct `Z` of the selected `T_j` using
   `lem-weil-pbc-scheme-coproduct-family`. By
   `lem-weil-pbc-finite-affine-coproduct-spectrum`, it is `Spec B` for the product
   of their rings, with the specified component projections. The induced `q : Z → W`
   is surjective, and the induced `p : Z → V` equals `q ≫ f|_W` by the coproduct
   universal property. Its components are open and closed and cover `Z`.
6. At a point of a component `T_j`, the stalk map of `q` is that of the corresponding
   `h i`, after open restrictions; thus `q` is flat by `def-weil-flat-morphism`.
   The affine neighbourhood `T_j` and the finite presentations from step 3 show that
   both `q` and `p` are locally of finite presentation by
   `def-sbc-locally-finite-presentation`.
7. Since `Z`, `W` and `V` are affine, the affine flatness and finite-presentation
   criteria from step 3 give `A → B` flat and finitely presented and `R → B` finitely
   presented. Surjectivity of `q` is surjectivity on spectra, so
   `lem-weil-pbc-flat-surjective-spectrum-faithfully-flat` makes `A → B` faithfully flat.
   The equality from step 5 identifies `R → B` with the composite `R → A → B`.
8. Apply `lem-trf-finite-presentation-fppf-source-algebra` to this tower to obtain
   finite presentation of `R → A`. The neighbourhoods in step 2 now witness local
   finite presentation at `x` by `def-sbc-locally-finite-presentation`. Since `x` was
   arbitrary, this proves the converse. -/
theorem locallyOfFinitePresentation_iff_of_fppf_source_family
    {X S : Scheme.{u}} (f : X ⟶ S) {I : Type v}
    (U : I → Scheme.{u}) (h : ∀ i : I, U i ⟶ X)
    [∀ i : I, Flat (h i)] [∀ i : I, LocallyOfFinitePresentation (h i)]
    (hjoint : ∀ x : X, ∃ (i : I) (y : U i), h i y = x) :
    LocallyOfFinitePresentation f ↔ ∀ i : I, LocallyOfFinitePresentation (h i ≫ f) := by
  classical
  constructor
  · intro hf i
    have : LocallyOfFinitePresentation f := hf
    infer_instance
  · intro hcomp
    -- Select a small covering subfamily even when I is in a larger universe.
    choose i y hy using hjoint
    let V : X → Scheme.{u} := fun x ↦ U (i x)
    let k : ∀ x : X, V x ⟶ X := fun x ↦ h (i x)
    let g : (∐ V) ⟶ X := Sigma.desc k
    have : Flat g := IsZariskiLocalAtSource.sigmaDesc fun _ ↦ inferInstance
    have : LocallyOfFinitePresentation g :=
      IsZariskiLocalAtSource.sigmaDesc fun _ ↦ inferInstance
    have : LocallyOfFinitePresentation (g ≫ f) := by
      have heq : g ≫ f = Sigma.desc (fun x : X ↦ k x ≫ f) := by
        ext x
        simp [g]
      rw [heq]
      exact IsZariskiLocalAtSource.sigmaDesc fun x ↦ hcomp (i x)
    have : Surjective g := Surjective.sigmaDesc_of_union_range_eq_univ <|
      Set.eq_univ_of_forall fun x ↦ Set.mem_iUnion.mpr ⟨x, y x, hy x⟩
    exact LocallyOfFinitePresentation.of_comp_of_flat_of_surjective g f

end AlgebraicGeometry
