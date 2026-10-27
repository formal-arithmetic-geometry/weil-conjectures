module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Morphisms.Basic
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem

/-!
# Finiteness near an embedded projective fibre

Source: Stacks Project, Tag 0D2N, proof of `lemma-ample-in-neighbourhood`, final paragraph;
the arbitrary-base finite-neighbourhood input is Tag 02UP.
(blueprint: lem-trf-projective-map-finite-near-embedded-fibre)
-/

@[expose] public section

universe u

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A proper map to projective space whose map on the fibre over `s` is a closed immersion
is finite over the inverse image of an affine neighbourhood of `s` in the base.
The coordinate type `ULift (Fin (r + 1))` represents classical projective dimension `r`.
The `pullback.map` in the hypothesis is the canonical map from the fibre of the composite
to the fibre of the projective-space projection, both over `Spec κ(s)`.

Source: Stacks Project, Tag 0D2N, final paragraph of `lemma-ample-in-neighbourhood`.
(blueprint: lem-trf-projective-map-finite-near-embedded-fibre)

Proof:
1. For every point `p` of the projective-space fibre, the fibre homeomorphisms
   (`def-pc-scheme-fibre`) and injectivity of the closed immersion on the base fibre
   (`def-weil-closed-immersion`) show that the underlying fibre of `φ` at `p` has at most
   one point, including when it is empty.
2. Apply `lem-trf-proper-finite-fibre-finite-near` (Tag 02UP) at every such `p` to obtain
   open neighbourhoods where `φ` is finite. Their union `W` contains the entire projective
   fibre, and `lem-weil-pbc-finite-local-on-target`, condition (3), makes `φ` finite over `W`.
3. The projection `q` is proper by `lemma-nagata-projective-space-base-change-proper`,
   hence closed by `def-weil-proper-morphism`. Remove the closed image `q(P \ W)` from
   the base. The resulting neighbourhood `V₀` of `s` has `q⁻¹(V₀) ⊆ W`.
4. Choose an affine neighbourhood `s ∈ V ⊆ V₀` using `lem-weil-pbc-affine-opens-basis`.
   Restrict the finite map over `W` to `q⁻¹(V)`, using the restriction clause of
   `lem-weil-pbc-finite-local-on-target`. Its source is exactly `(φ ≫ q)⁻¹(V)`.
-/
theorem ProjectiveSpace.exists_isFinite_restrict_near_embedded_fibre
    {S Z : Scheme.{u}} (r : ℕ)
    (φ : Z ⟶ ℙ(ULift.{u} (Fin (r + 1)); S)) [IsProper φ] (s : S)
    (hφs : IsClosedImmersion
      (pullback.map
        (φ ≫ (ℙ(ULift.{u} (Fin (r + 1)); S) ↘ S)) (S.fromSpecResidueField s)
        (ℙ(ULift.{u} (Fin (r + 1)); S) ↘ S) (S.fromSpecResidueField s)
        φ (𝟙 _) (𝟙 _) (by simp) (by simp))) :
    ∃ V : S.Opens, s ∈ V ∧ IsAffineOpen V ∧
      IsFinite (φ ∣_ ((ℙ(ULift.{u} (Fin (r + 1)); S) ↘ S) ⁻¹ᵁ V)) := by
  sorry

end AlgebraicGeometry
