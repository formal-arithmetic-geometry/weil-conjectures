module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Integral
public import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.AlgebraicGeometry.Fiber
import Sheaf.RingTheory.AlgebraicFieldImagePrincipalNeighbourhood

/-!
# Compatible affine neighbourhoods for integral pinching

Source: Stacks Project, Tag 0ECJ,
`lemma-prepare-pushout-along-closed-immersion-and-integral`, in
`situation-pushout-along-closed-immersion-and-integral`
(blueprint: lem-sfb-integral-pinching-compatible-affines).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A closed immersion and an integral morphism admit compatible affine neighbourhoods
provided the image of each fibre is contained in an affine open of the ambient scheme.
Equality in `Z.Opens` identifies the open subschemes with their restricted structure sheaves.

Source: Stacks Project, Tag 0ECJ,
`lemma-prepare-pushout-along-closed-immersion-and-integral`
(blueprint: lem-sfb-integral-pinching-compatible-affines).

Proof:
1. Fix t and choose an affine U₀ containing the image of the whole fibre. Its inverse
   image Ω₀ under the closed immersion is affine, and the map on sections is surjective
   (def-weil-closed-immersion). The integral map j is closed by
   pqf-lem-integral-univclosed. Thus T minus j(Z minus Ω₀) is an open neighbourhood of t.
   Choose an affine neighbourhood V₀ therein using lem-weil-pbc-affine-opens-basis;
   then j⁻¹(V₀) is contained in Ω₀.
2. The scheme-theoretic fibre Z_t (def-pc-scheme-fibre) is the spectrum of an algebra
   integral over κ(t), by lem-sbc-integral-morphism-base-change and
   def-weil-finite-integral-morphism. Its map to Z factors through Ω₀, and its image
   is the whole topological fibre j⁻¹({t}) (def-weil-open-immersion).
3. Apply lem-sfb-algebraic-field-image-principal-neighbourhood to this spectrum map
   (def-weil-affine-spectrum) and the open j⁻¹(V₀) inside Ω₀. It gives a principal
   neighbourhood of the fibre inside j⁻¹(V₀). Lift its defining function along the
   surjection on sections of the closed immersion, and shrink U₀ to the corresponding
   principal affine open U₁ (lem-weil-pbc-principal-localization-open-immersion).
   Contraction of primes gives Ω₁ = i⁻¹(U₁), containing the fibre and contained in j⁻¹(V₀).
4. Closedness of j makes H₁ = V₀ minus j(Z minus Ω₁) an open neighbourhood of t in V₀.
   Apply lem-sfb-algebraic-field-image-principal-neighbourhood to Spec κ(t) → V₀
   (def-pc-scheme-fibre), giving g with t in V = D(g) contained in H₁.
   This V is affine (lem-weil-pbc-principal-localization-open-immersion), and
   j⁻¹(V) is contained in Ω₁.
5. Pull g back to Ω₁ and lift the resulting section to U₁ using the closed immersion.
   Its principal open U is affine. Contraction of primes (def-weil-affine-spectrum)
   identifies i⁻¹(U) with Ω₁ intersected with j⁻¹(V), hence with j⁻¹(V).
   Equal opens have the same restricted structure sheaf (def-weil-open-immersion).
-/
theorem exists_affineOpens_preimage_eq_of_isIntegralHom
    {X T Z : Scheme.{u}} (i : Z ⟶ X) (j : Z ⟶ T)
    [IsClosedImmersion i] [IsIntegralHom j]
    (h : ∀ t : T, ∃ U : X.Opens, IsAffineOpen U ∧
      ∀ z : Z, j z = t → i z ∈ U) :
    ∀ t : T, ∃ (U : X.Opens) (V : T.Opens),
      IsAffineOpen U ∧ IsAffineOpen V ∧ t ∈ V ∧ i ⁻¹ᵁ U = j ⁻¹ᵁ V := by
  sorry

end AlgebraicGeometry
