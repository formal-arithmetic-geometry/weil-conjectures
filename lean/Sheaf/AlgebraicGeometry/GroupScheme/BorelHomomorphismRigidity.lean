module

public import Sheaf.AlgebraicGeometry.GroupScheme.Borel
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
import Sheaf.AlgebraicGeometry.GroupScheme.HomogeneousQuotient
import Sheaf.AlgebraicGeometry.ProperReducedGlobalSectionsProduct
import WeilConjectures.AlgebraicGeometry.Cohomology.FlatCohomologySeparated
import WeilConjectures.AlgebraicGeometry.OpenCohomologyZeroSections
import WeilConjectures.AlgebraicGeometry.Cohomology.FlatCohomologyComparison
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
import Mathlib.AlgebraicGeometry.Pullbacks

/-! # Borel restriction determines homomorphisms after arbitrary scalar extension

Source: Milne, Algebraic Groups (2017), Proposition 17.21, printed p.358,
with the conventions of Section 17b, printed p.353.
(blueprint: lem-sfb-borel-homomorphism-rigidity)
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry

/-- Homomorphisms of smooth connected affine finite-type groups are determined by
restriction to a Borel after scalar extension to any commutative algebra.
The group structures on the pullbacks are the canonical ones transported by
`Over.pullback`, through its finite-product-preserving monoidal structure.

Source: Milne, Algebraic Groups (2017), Proposition 17.21, printed p.358;
Section 17b, printed p.353. (blueprint: lem-sfb-borel-homomorphism-rigidity)

Proof plan:
1. Use lem-sfb-algebraic-group-homogeneous-quotient for G/B and
   lem-sfb-borel-quotient-proper-geometry for its smooth geometrically integral
   proper separated finite-type geometry. The identity gives a rational point x₀.
2. Define δ(g) = f₁(g) f₂(g)⁻¹. Agreement on B_R shows δ(gb) = δ(g) on every
   test scheme; this uses cancellation, not commutativity of H.
3. The quotient's fpqc-local lifts and coset fibres, together with
   lem-weil-pbc-fpqc-representable-descent, descend δ to d : (G/B)_R → H_R.
   Uniqueness of gluing supplies independence of lifts, naturality and the R-map property.
4. By lem-weil-pbc-proper-reduced-algclosed-global-sections-product,
   Γ(G/B, O) = k canonically. The map k → R is flat by lem-pc-flat-field.
   Apply lem-pc-flat-cohomology-separated in degree zero, using
   lem-sc-open-cohomology-zero-sections and def-pc-flat-cohomology-comparison:
   the actual scalar map R → Γ((G/B)_R, O) is an isomorphism, even for nonreduced R.
5. By lem-weil-pbc-fibre-product-affine-spectra, H_R is affine.
   Apply lem-weil-pbc-morphism-into-affine-scheme to factor d through Spec R,
   using the inverse of the scalar isomorphism on global sections.
6. Evaluation at x₀ shows this constant is the identity, since both homomorphisms
   preserve the identity. Thus δ is identically one and f₁ = f₂ on all test schemes,
   hence as morphisms by Yoneda. For the zero algebra all pullbacks are empty,
   and the morphisms are uniquely equal. -/
theorem hom_ext_of_borel_baseChange {k : Type u} [Field k] [IsAlgClosed k]
    (G H B : Over (Spec (.of k))) [GrpObj G] [GrpObj H] [GrpObj B]
    [Smooth G.hom] [ConnectedSpace G.left] [IsAffine G.left]
    [LocallyOfFiniteType G.hom] [QuasiCompact G.hom]
    [Smooth H.hom] [ConnectedSpace H.left] [IsAffine H.left]
    [LocallyOfFiniteType H.hom] [QuasiCompact H.hom]
    (i : B ⟶ G) (hB : IsBorelGroupScheme i)
    (R : Type u) [CommRing R] [Algebra k R]
    (f₁ f₂ : (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap k R)))).obj G ⟶
      (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap k R)))).obj H)
    [IsMonHom f₁] [IsMonHom f₂]
    (h : ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap k R)))).map i ≫
        f₁).left =
      ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap k R)))).map i ≫
        f₂).left) :
    f₁ = f₂ := by
  sorry

end AlgebraicGeometry
