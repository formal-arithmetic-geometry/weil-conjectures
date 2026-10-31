/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen

/-! # Finite affine source charts over an affine target neighbourhood

Source: Stacks Project, Descent, Tag 02KL, `lemma-flat-finitely-presented-permanence`,
locally-of-finite-type alternative, affine reduction and finite affine selection;
coordinate criteria: Morphisms, Tags 01U5, 01TQ and 01T2
(blueprint: lem-a1-fppf-source-finite-affine-charts).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- Around every target point of a flat surjective locally finitely presented morphism,
choose affine target and base neighbourhoods and finitely many affine source opens whose
images cover the target neighbourhood. Their coordinate maps are flat and finitely presented,
and their composites from the base are finite type. The coordinate rings are canonically
`R = Γ(S, V)`, `A = Γ(Y, W)` and `B i = Γ(X, U i)`; `IsAffineOpen` identifies each open
subscheme with the spectrum of its section ring. The maps are the canonical `appLE` maps.
No quasi-compactness or separation of the original schemes or morphisms is assumed.

Source: Stacks Project, Descent, Tag 02KL, `lemma-flat-finitely-presented-permanence`,
locally-of-finite-type alternative; Morphisms, Tags 01U5, 01TQ and 01T2
(blueprint: lem-a1-fppf-source-finite-affine-charts).

Proof:
1. Fix y. Use lem-weil-pbc-affine-opens-basis first at h(y) to choose affine V,
   then at y inside the open inverse image of V to choose affine W. Put
   R = O_S(V) and A = O_Y(W). Continuity gives the open inverse image.
2. All affine opens contained in the inverse image of W cover that inverse image,
   by lem-weil-pbc-affine-opens-basis. Surjectivity of q makes their images cover W.
   By lem-weil-pbc-flat-lfp-open, q is open, so these images are open.
   The affine W is quasi-compact by lem-weil-pbc-affine-scheme-qcqs. The finite-subcover
   condition in def-weil-pbc-quasi-compact-scheme selects finitely many images covering W.
   This does not assert that the selected source opens cover the entire inverse image.
3. Put B_i = O_X(U_i). The containments induce the canonical maps R to A to B_i,
   using def-pc-scheme and def-weil-affine-spectrum. Functoriality of the structure sheaf
   identifies their composite with the coordinate map of q followed by h.
   Affine opens are canonically the spectra of their section rings.
4. Apply lem-weil-pbc-flat-morphism-affine-criterion to q and (U_i,W) for flatness;
   apply lem-weil-pbc-lfp-affine-opens-finite-presentation to the same pair for finite
   presentation. Apply lem-weil-pbc-lft-affine-pairs to q followed by h and (U_i,V)
   for finite type of the composite. These arbitrary-affine-pair criteria require no
   quasi-compactness or separation of the ambient schemes or morphisms. -/
theorem exists_fppf_source_finite_affine_charts
    {X Y S : Scheme.{u}} (q : X ⟶ Y) (h : Y ⟶ S)
    [Flat q] [LocallyOfFinitePresentation q] [Surjective q]
    [LocallyOfFiniteType (q ≫ h)] (y : Y) :
    ∃ (V : S.Opens) (W : Y.Opens),
      IsAffineOpen V ∧ IsAffineOpen W ∧ h y ∈ V ∧ y ∈ W ∧
      ∃ (eWV : W ≤ h ⁻¹ᵁ V) (n : ℕ) (U : Fin n → X.Opens),
        (∀ i : Fin n, IsAffineOpen (U i)) ∧
        (W : Set Y) = ⋃ i : Fin n, q '' (U i : Set X) ∧
        ∃ (eUW : ∀ i : Fin n, U i ≤ q ⁻¹ᵁ W)
          (eUV : ∀ i : Fin n, U i ≤ (q ≫ h) ⁻¹ᵁ V),
          ∀ i : Fin n,
            (q.appLE W (U i) (eUW i)).hom.Flat ∧
            (q.appLE W (U i) (eUW i)).hom.FinitePresentation ∧
            (h.appLE V W eWV ≫ q.appLE W (U i) (eUW i)).hom.FiniteType ∧
            h.appLE V W eWV ≫ q.appLE W (U i) (eUW i) =
              (q ≫ h).appLE V (U i) (eUV i) := by
  classical
  obtain ⟨V, hV, hyV, _⟩ :=
    TopologicalSpace.Opens.isBasis_iff_nbhd.mp S.isBasis_affineOpens
      (U := ⊤) (x := h y) (by trivial)
  obtain ⟨W, hW, hyW, eWV⟩ :=
    TopologicalSpace.Opens.isBasis_iff_nbhd.mp Y.isBasis_affineOpens
      (U := h ⁻¹ᵁ V) (x := y) hyV
  let I := {U : X.Opens // IsAffineOpen U ∧ U ≤ q ⁻¹ᵁ W}
  have hcover : (W : Set Y) ⊆ ⋃ U : I, q '' (U.val : Set X) := by
    intro w hw
    obtain ⟨x, rfl⟩ := q.surjective w
    obtain ⟨U, hU, hxU, eUW⟩ :=
      TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens
        (U := q ⁻¹ᵁ W) (x := x) hw
    exact Set.mem_iUnion.mpr ⟨⟨U, hU, eUW⟩, ⟨x, hxU, rfl⟩⟩
  obtain ⟨t, ht⟩ := hW.isCompact.elim_finite_subcover
    (fun U : I ↦ q '' (U.val : Set X))
    (fun U ↦ q.isOpenMap _ U.val.isOpen) hcover
  let e : Fin (Fintype.card t) ≃ t := (Fintype.equivFin t).symm
  let U : Fin (Fintype.card t) → X.Opens := fun i ↦ (e i).val.val
  have hU (i) : IsAffineOpen (U i) := (e i).val.property.1
  have eUW (i) : U i ≤ q ⁻¹ᵁ W := (e i).val.property.2
  have eUV (i) : U i ≤ (q ≫ h) ⁻¹ᵁ V := by
    intro x hx
    exact eWV (eUW i hx)
  refine ⟨V, W, hV, hW, hyV, hyW, eWV, Fintype.card t, U, hU, ?_, eUW, eUV, ?_⟩
  · apply Set.Subset.antisymm
    · intro w hw
      obtain ⟨a, ha⟩ := Set.mem_iUnion.mp (ht hw)
      obtain ⟨hat, hwa⟩ := Set.mem_iUnion.mp ha
      exact Set.mem_iUnion.mpr ⟨e.symm ⟨a, hat⟩, by simpa [U] using hwa⟩
    · intro w hw
      obtain ⟨i, x, hx, rfl⟩ := Set.mem_iUnion.mp hw
      exact eUW i hx
  · intro i
    refine ⟨q.flat_appLE hW (hU i) (eUW i),
      q.finitePresentation_appLE hW (hU i) (eUW i), ?_, ?_⟩
    · rw [Scheme.Hom.appLE_comp_appLE]
      exact (q ≫ h).finiteType_appLE hV (hU i) (eUV i)
    · exact Scheme.Hom.appLE_comp_appLE q h V W (U i) eWV (eUW i)

end AlgebraicGeometry
