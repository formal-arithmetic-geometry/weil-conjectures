module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.Defs
public import Mathlib.CategoryTheory.Monoidal.Grp
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

import Sheaf.AlgebraicGeometry.GroupScheme.AffineHomomorphismFlatImage
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

/-!
# Faithful homomorphisms of affine algebraic groups are closed immersions

Source: Milne, Algebraic Groups (2017), Corollary 3.35, printed p.75, with Theorem 3.34
on the same page.
(blueprint: lem-sfb-geometric-unipotence-faithful-closed-immersion)
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A homomorphism of affine group schemes of finite type over a field that is injective on
all commutative algebra points is a closed immersion.

Source: Milne, Algebraic Groups (2017), Corollary 3.35, printed p.75, with Theorem 3.34
on the same page. The proof factors the homomorphism through its faithfully flat image and
uses fpqc descent; no smoothness, connectedness, reducedness, perfectness, or characteristic
hypothesis is imposed.

Proof plan:
1. Apply `lem-sfb-affine-homomorphism-flat-image`: write `f = u ≫ j`, with `j` a closed
   immersion and `u` faithfully flat onto an affine finite-type group `I`. Equality after
   `u` implies equality after `f`, so `u` is injective on all algebra points.
2. Identify `u` with the spectrum map on global sections (`def-weil-affine-spectrum`).
   Faithful flatness implies flatness (`def-weil-pbc-faithfully-flat-ring-map`), hence
   scheme flatness (`lem-weil-pbc-flat-ring-map-iff-flat-affine`), and surjectivity
   (`lem-weil-pbc-faithfully-flat-surjective-spectrum`). A morphism between affines is
   affine (`lem-weil-pbc-morphism-affine-schemes-affine`), so each affine open of `I`
   has an affine preimage mapping onto it. This makes `u` an fpqc covering
   (`def-weil-pbc-fpqc-covering`).
3. Form `P = G ×_I G` (`def-pc-fibre-product`). Affine base change and affine total
   space (`lem-weil-pbc-affine-morphism-permanence`) make `P` affine. Its projections
   are algebra points over its global-section algebra; their composites with `u`
   agree, so injectivity gives equality of the projections.
4. Descend the identity of `G` along `u`, using this equality as compatibility
   (`lem-weil-pbc-fpqc-representable-descent`). Obtain `s : I ⟶ G` with `u ≫ s = 𝟙 G`.
   Both `s ≫ u` and the identity restrict to `u`, so descent uniqueness gives
   `s ≫ u = 𝟙 I`. Thus `u` is an isomorphism.
5. On every affine open of `H`, the closed immersion `j` is a spectrum of a quotient.
   Transport this description through the isomorphism `u`; the same affine criterion
   (`def-weil-closed-immersion`) proves `f` is a closed immersion. No extra field or
   group regularity hypotheses were used.
(blueprint: lem-sfb-geometric-unipotence-faithful-closed-immersion)
-/
theorem isClosedImmersion_of_faithful_affineGroupHom
    {k : Type u} [Field k]
    (G H : Over (Spec (.of k))) [GrpObj G] [GrpObj H]
    [IsAffine G.left] [LocallyOfFiniteType G.hom] [QuasiCompact G.hom]
    [IsAffine H.left] [LocallyOfFiniteType H.hom] [QuasiCompact H.hom]
    (f : G ⟶ H) [IsMonHom f]
    (hinj : ∀ (R : Type u) [CommRing R] [Algebra k R],
      Function.Injective
        (fun x : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k R))) ⟶ G ↦ x ≫ f)) :
    IsClosedImmersion f.left := by
  sorry

end AlgebraicGeometry
