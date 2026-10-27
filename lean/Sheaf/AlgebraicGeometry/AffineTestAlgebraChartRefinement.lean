module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Noetherian.Defs

/-! # Affine charts for a finite type test algebra

Source: Stacks Project, Tag 07R4 (`lemma-J`), proof, first, second and last paragraphs
(blueprint: lem-trf-affine-test-algebra-chart-refinement).
-/

@[expose] public section

universe u v

open CategoryTheory

namespace AlgebraicGeometry

/-- A finite type algebra over an affine open of a locally Noetherian scheme has affine
charts refining any prescribed affine open covering of the scheme.

Source: Stacks Project, Tag 07R4 (`lemma-J`), proof, first, second and last paragraphs
(blueprint: lem-trf-affine-test-algebra-chart-refinement).

Proof plan:
1. By `pqf-lem-affine-open-locnoeth`, the section ring of `V` is Noetherian. Apply
   `lem-weil-pbc-finite-type-algebra-noetherian` to the finite type map to `B`. The singleton
   affine cover of `Spec B`, including when `B` is the zero ring, gives local Noetherianity
   by `pqf-def-locnoeth` and `def-weil-affine-spectrum`.
2. Apply `lem-weil-pbc-lft-pointwise-criterion` to the affine pair `(Spec B, V)`.
   Under `V.2.isoSpec`, its section map is the given map `φ`, so the spectrum morphism
   to `V` is locally of finite type. This is vacuous when `Spec B` is empty.
3. The inclusion of `V` is an immersion, hence locally of finite type by
   `lem-weil-pbc-immersion-base-change-lft`. Compose using clause (e) of
   `lem-weil-pbc-proper-fp-permanence` to get local finite type over `X`.
4. For each point `y`, choose a chart `U a` containing its image, and use
   `lem-weil-pbc-affine-opens-basis` inside the open inverse image to choose an affine
   neighbourhood `W y`. Choose the index and neighbourhood together.
5. Apply `lem-weil-pbc-lft-affine-pairs` to each affine pair `(W y, U (i y))` and its
   containment proof to obtain finite type of the induced section map.
6. Each point belongs to its own neighbourhood, so their union is all of `Spec B`.
   No finiteness of the prescribed cover is used. For empty `Spec B`, the functions and
   family are empty, their union is empty, and all pointwise conditions are vacuous.
-/
theorem affine_test_algebra_chart_refinement
    (X : Scheme.{u}) [IsLocallyNoetherian X]
    {I : Type v} (U : I → X.affineOpens) (hcover : (⨆ a, (U a).1) = ⊤)
    (V : X.affineOpens) (B : Type u) [CommRing B]
    (φ : Γ(X, V.1) →+* B) (hφ : φ.FiniteType) :
    IsNoetherianRing Γ(X, V.1) ∧
      LocallyOfFiniteType (Spec.map (CommRingCat.ofHom φ) ≫ V.2.isoSpec.inv) ∧
      LocallyOfFiniteType (Spec.map (CommRingCat.ofHom φ) ≫ V.2.fromSpec) ∧
      IsLocallyNoetherian (Spec (CommRingCat.of B)) ∧
      ∃ (i : Spec (CommRingCat.of B) → I)
        (W : Spec (CommRingCat.of B) → (Spec (CommRingCat.of B)).affineOpens),
        (∀ y, y ∈ (W y).1) ∧ (⨆ y, (W y).1) = ⊤ ∧
        ∃ e : ∀ y, (W y).1 ≤
            (Spec.map (CommRingCat.ofHom φ) ≫ V.2.fromSpec) ⁻¹ᵁ (U (i y)).1,
          ∀ y, ((Spec.map (CommRingCat.ofHom φ) ≫ V.2.fromSpec).appLE
            (U (i y)).1 (W y).1 (e y)).hom.FiniteType := by
  sorry

end AlgebraicGeometry
