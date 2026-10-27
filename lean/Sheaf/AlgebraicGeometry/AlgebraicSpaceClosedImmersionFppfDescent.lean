module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceJointSurjectivity
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFourPropertyFppfDescent
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFppfFiniteAffineRefinement
import Sheaf.AlgebraicGeometry.FpqcClosedImmersionDescent
import Mathlib.AlgebraicGeometry.Sites.Fpqc

/-! # Fppf descent of closed immersions of algebraic spaces

Source: Stacks Project, Spaces Descent, Tag 0420,
lemma-descending-property-closed-immersion, specialized to fppf families
(blueprint: lem-sfb-space-closed-immersion-fppf-descent).

Closed immersion is expressed by the existing scheme-test representability predicate,
with the scheme closed-immersion property. The pullback projection is taken on the
underlying presheaves; this represents the sheaf fibre product, since limits of sheaves
are computed on sections.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- A morphism of algebraic spaces is a closed immersion exactly when all its pullbacks
along an fppf covering family are closed immersions. Representability is part of each
closed-immersion assertion, not a hypothesis on the original morphism or the covering.
Source: Stacks Project, Spaces Descent, Tag 0420;
Morphisms of Spaces, Tag 03M4; Topologies on Spaces, Tag 0DFQ
(blueprint: lem-sfb-space-closed-immersion-fppf-descent).

Proof:
1. If f is a closed immersion, for every scheme T mapping to Y_i the iterated fibre
   product (X times_Y Y_i) times_{Y_i} T identifies with X times_Y T, preserving the
   projection to T. This gives representability and the closed-immersion property for
   each pullback, by def-trf-algebraic-space and lem-trf-space-fibre-products-etale-covers.
2. Conversely, the local closed immersions have affine source on affine scheme tests,
   by def-weil-closed-immersion. The affine clause of
   lem-sfb-space-four-property-fppf-descent therefore makes f affine; it does not require
   f to be representable or finitely presented in advance.
3. For an affine scheme test T mapping to Y, apply
   lem-sfb-space-fppf-finite-affine-refinement. Its finite affine scheme family V_j to T
   factors through members Y_i, is flat, locally finitely presented and jointly
   surjective, and is fppf by def-pc-fppf-site, hence fpqc by
   lem-trf-fppf-covering-is-fpqc. No individual Y_i to Y need be quasi-compact.
4. The affine scheme E_T representing X times_Y T pulls back over each V_j to the
   corresponding scheme test of the assumed local closed immersion. The fibre-product
   identifications preserve projections. Apply lem-pc-fpqc-descend-closed-immersion to
   E_T to T and this fpqc family. Thus every affine scheme test is a closed immersion.
5. For an arbitrary scheme T mapping to Y, lem-sfb-space-affine-locality gives a
   representing scheme E for X times_Y T. On each affine open V of T, its inverse image
   is X times_Y V and the projection is a closed immersion by Step 4. The affine-open
   characterization of def-weil-closed-immersion gives that E to T is a closed immersion.
   This proves the scheme-test assertion. An empty jointly surjective covering forces
   Y empty; finite refinement allows the empty family over an empty affine test. -/
theorem closedImmersion_iff_fppf_pullback {S : Scheme.{u}} {I : Type w}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (Yᵢ : I → AlgebraicSpace S) (g : ∀ i : I, Yᵢ i ⟶ Y)
    (hflat : ∀ i : I, MapIsFlat (g i))
    (hlfp : ∀ i : I, MapIsLocallyOfFinitePresentation (g i))
    (hsurj : IsJointlySurjective (fun i : I ↦ (g i).hom.hom)) :
    IsRepresentableWith (fun _ _ p ↦ IsClosedImmersion p.left) f.hom.hom ↔
      ∀ i : I, IsRepresentableWith (fun _ _ p ↦ IsClosedImmersion p.left)
        (Limits.pullback.snd f.hom.hom (g i).hom.hom) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
