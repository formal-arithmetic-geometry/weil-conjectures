/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NR
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import WeilConjectures.AlgebraicGeometry.QuasiFiniteMorphism
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.Limits.Shapes.Diagonal
import WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Representability
import Sheaf.AlgebraicGeometry.EtaleRelationFindingOpens
import Sheaf.AlgebraicGeometry.EtaleRelationQuotient
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
import WeilConjectures.AlgebraicGeometry.SeparatedLqfBaseChange
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Pullbacks
import Sheaf.AlgebraicGeometry.AlgebraicSpaceAffineAtlasOpenCover
import Sheaf.AlgebraicGeometry.EtaleQuasiAffineImageScheme
import Sheaf.AlgebraicGeometry.FiniteFlatAffineRelationQuotient
import Sheaf.AlgebraicGeometry.ProperEtaleRelationFiniteNeighbourhood

/-!
# Separated locally quasi-finite algebraic spaces over schemes are schemes

Source: Stacks Project, Spaces Morphisms, Tag 03XX, Section 0417
(blueprint: lem-a1-separated-locally-qf-space-representable).

The natural transformation to `h_T` retains the arbitrary target scheme over `S`.
The equality in the conclusion makes the representing isomorphism an isomorphism over `T`.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- A separated, chartwise locally quasi-finite algebraic space over a scheme is a scheme.
Here `yoneda.preimage (a ≫ f)` is the unique scheme map corresponding to the composite
of the chart with `f`, by the fully faithful Yoneda embedding. The diagonal is the actual
map into the presheaf fibre product over `h_T`.
Source: Stacks Project, Spaces Morphisms, Tag 03XX, Section 0417
(blueprint: lem-a1-separated-locally-qf-space-representable).

Proof:
1. Regard `E` as a space over `T`: restrict its sheaf to sections with the specified
   composite to `T`. The diagonal is a base change of the diagonal over `S`, and its
   atlas remains an atlas (def-trf-algebraic-space,
   lem-trf-space-fibre-products-etale-covers). By lem-a1-space-affine-atlas-open-cover,
   cover it by open spaces with affine atlases over affine opens of `T`.
   Representability is local for such open covers by lem-pc-schemes-criterion.
2. The hypotheses persist on these pieces: compose each chart with the open inclusion
   and use lem-weil-pbc-etale-composition-cancellation and
   lem-weil-pbc-separated-lqf-base-change. The relative diagonal on a piece is a base
   change of the original one, so use lem-weil-pbc-closed-immersion-base-change.
3. For an affine atlas `U` over an affine target, form `R = U ×_E U`. The space diagonal
   makes this a scheme; its projections are surjective étale by
   lem-trf-space-fibre-products-etale-covers. The relation map into `U ×_T U` is closed.
   The latter scheme is affine by lem-weil-pbc-fibre-product-affine-spectra, so `R` is
   affine by def-weil-closed-immersion. The chart hypothesis makes `U → T` locally
   quasi-finite. The fibre-product identity makes `R` an equivalence relation.
4. Identify `U/R` with `E`: each section lifts along the pullback of the atlas, an
   étale surjective covering and hence an fppf covering by def-weil-etale-morphism and
   def-pc-fppf-site. Two lifts agree exactly when related by `R`; glue using the sheaf
   axiom. This identification persists after base change and agrees with the quotient
   universal property of lem-trf-etale-relation-quotient.
5. Lift a point of `E` to `U`. Apply lem-a1-proper-etale-relation-finite-neighbourhood:
   after an affine étale neighbourhood of the image in `T`, there are clopen finite
   pieces `U'` and `R'`, containing a lift of that point, with `R'` the full restricted
   relation. The restricted projections are still étale.
6. Since `T'` is affine and the pieces finite, `U'` and `R'` are affine by
   def-weil-finite-integral-morphism. Finite generation over the base ring implies
   finite generation over the ring of `U'` for either projection. Thus both projections
   are finite étale, hence finite locally free by def-weil-etale-morphism and
   def-pc-finite-locally-free. Apply lem-a1-finite-flat-affine-relation-quotient to
   represent `U'/R'` by an affine scheme.
7. Apply lem-trf-etale-relation-finding-opens to the clopen inclusion and full restricted
   relation. Its flatness and finite-presentation assumptions follow from étaleness
   (def-weil-etale-morphism, lem-weil-pbc-etale-composition-cancellation). Step 4 and
   lem-trf-space-fibre-products-etale-covers identify the target with the base-changed
   space. We obtain an affine open neighbourhood of the lifted point.
8. Its map to affine `T'` is affine, hence quasi-affine. By
   lem-a1-etale-quasi-affine-image-scheme its image is a schematic open neighbourhood
   of the original point. These opens cover the space. Apply lem-pc-schemes-criterion,
   then apply it again to the pieces of step 1. Finally Yoneda turns the composite
   `h_Z ≅ E → h_T` into a scheme morphism `g : Z → T`; naturality gives the equality
   in the conclusion, so the isomorphism is over `T`. -/
theorem exists_scheme_of_separated_locally_quasi_finite {S : Scheme.{u}}
    (T : Over S) (E : AlgebraicSpace S) (f : E.obj.obj ⟶ yoneda.obj T)
    (hqf : ∀ (V : Over S) (a : yoneda.obj V ⟶ E.obj.obj), IsEtale a →
      Scheme.Hom.IsLocallyQuasiFinite (yoneda.preimage (a ≫ f)).left)
    (hsep : IsRepresentableWith (fun _ _ p ↦ IsClosedImmersion p.left)
      (pullback.diagonal f)) :
    ∃ (Z : Over S) (g : Z ⟶ T) (e : yoneda.obj Z ≅ E.obj.obj),
      e.hom ≫ f = yoneda.map g := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
