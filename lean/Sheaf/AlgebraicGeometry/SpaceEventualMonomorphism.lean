module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceAbsoluteQuasiSeparated
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceAffineQuasiFinite
public import Sheaf.AlgebraicGeometry.StackQcqsMorphism
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.Limits.IsLimit
import Sheaf.AlgebraicGeometry.AlgebraicSpaceLftDiagonalLfp
import Sheaf.AlgebraicGeometry.AlgebraicSpaceEtaleOpenImage
import Sheaf.AlgebraicGeometry.SpaceQuasiCompactAffineTests
import Mathlib.AlgebraicGeometry.Sites.MorphismProperty

/-! # Eventual monicity of a map into an algebraic-space limit

Source: Stacks Project, Limits of Spaces, Tag 0828, clause (4)
(blueprint: lem-sfb-space-eventual-monomorphism).

The limit is taken in algebraic spaces over B. Monicity is expressed by injectivity
on sections over every S-scheme. Absolute quasi-separatedness does not require the
auxiliary scheme S to be quasi-separated.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

/-- A monomorphism from a quasi-compact space locally of finite type over B into an
affine-transition limit of quasi-separated spaces is monic at every sufficiently late stage.
Source: Stacks Project, Limits of Spaces, Tag 0828(4)
(blueprint: lem-sfb-space-eventual-monomorphism).

Proof:
1. Choose an index o and restrict to its cofinal tail. Write f_i : A to Z_i and
   R_i = A times_{Z_i} A, using [lem-trf-space-fibre-products-etale-covers]. By
   [lem-sfb-space-lft-cancellation], f_o is locally of finite type since A to B is.
   By [lem-sfb-space-lft-diagonal-lfp], its diagonal A to R_o is locally finitely
   presented. This needs no quasi-separatedness of A.
2. By [lem-a1-space-etale-open-image], atlas quasi-compactness agrees with point-space
   quasi-compactness. Since A is quasi-compact and Z_i is quasi-separated,
   [lem-sfb-space-qcqs-permanence] makes f_i quasi-compact. Base change by f_i and
   then by a quasi-compact scheme atlas of A preserves this property by
   [lem-sfb-space-quasicompact-affine-tests]. Choose a quasi-compact scheme atlas of
   that pullback. Its composite to R_i is a surjective etale atlas by
   [lem-trf-space-fibre-products-etale-covers] and
   [lem-weil-pbc-etale-covering-composition]. Thus R_i is quasi-compact.
3. Affine transitions Z_j to Z_i have closed diagonals by
   [lem-sfb-space-affine-locality]. The map R_j to R_i is the base change of this
   diagonal along the pair of maps to Z_j; hence it is a closed immersion. This
   follows on sections by eliminating the common Z_j coordinate of the pullback.
4. The diagonals A to R_i form a limit cone over R_o. A compatible family of maps
   into R_i gives a fixed pair a,b into A, by directedness. Their composites to
   each Z_i agree. Cofinality of the tail and the given limit over B imply ua=ub.
   Sectionwise injectivity of u gives a=b. Conversely a gives the diagonal pair,
   uniquely and naturally. Thus the limit of the R_i is A.
5. Closed immersions R_i to R_o are locally of finite type by
   [lem-sfb-space-closed-subspace-proper]. Apply
   [lem-sfb-space-closed-limit-stabilization] over R_o, using steps 1 through 4.
   A to R_i is an isomorphism at a sufficiently late stage i_0. A pair of sections
   with equal f_{i_0} image therefore lies on the diagonal, proving injectivity.
   At any later i, equality after f_i implies equality after f_{i_0}, so the same
   injectivity holds for every i greater than or equal to i_0. -/
theorem eventually_injective_of_limit
    {S : Scheme.{u}} (B : AlgebraicSpace S)
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : Iᵒᵖ ⥤ Over B)
    (haff : ∀ {i j : Iᵒᵖ} (f : i ⟶ j), MapIsAffine (D.map f).left)
    (hqs : ∀ i : Iᵒᵖ, IsAbsolutelyQuasiSeparated (D.obj i).left)
    (c : Cone D) (hc : IsLimit c)
    (A : Over B) (hAqc : IsQuasiCompact A.left.obj)
    (u : A ⟶ c.pt) (hlft : MapIsLocally (@LocallyOfFiniteType) A.hom)
    (hu : ∀ T : Over S, Function.Injective (u.left.hom.hom.app (op T))) :
    ∃ i₀ : I, ∀ i : I, i₀ ≤ i →
      ∀ T : Over S,
        Function.Injective ((u.left ≫ (c.π.app (op i)).left).hom.hom.app (op T)) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
