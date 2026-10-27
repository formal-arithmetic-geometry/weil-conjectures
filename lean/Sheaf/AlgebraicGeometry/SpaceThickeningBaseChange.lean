/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q157
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
public import Sheaf.AlgebraicGeometry.ProperCurveModuli
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.Topology.Homeomorph.Defs
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-! # Arbitrary thickenings of algebraic spaces under base change

Source: Stacks Project, spaces-more-morphisms.tex, Tag 09ZX
(lemma-base-change-thickening), and spaces-morphisms.tex, Tag 042R
(lemma-immersions-monomorphisms)
(blueprint: lem-sfb-space-thickening-base-change).

Closed immersions are tested on schemes using `IsRepresentableWith` and the existing
scheme predicate. The topology and map on point classes are the shared constructions.
The fibre product is formed in fppf sheaves; `fibreProduct_isAlgebraicSpace` identifies
it as an algebraic-space fibre product. No finite-order hypothesis is imposed.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- A thickening is monic, and every algebraic-space base change is a thickening.
Source: Stacks, Tag 09ZX (lemma-base-change-thickening) and Tag 042R
(lemma-immersions-monomorphisms)
(blueprint: lem-sfb-space-thickening-base-change).

Proof:
1. For any representable closed immersion E → F, a scheme R and two sections with
   equal image, form h_R ×_F E. Its scheme projection to R is a closed immersion and
   hence monic by lem-pc-proper-monomorphism-closed. The two sections of that projection
   agree. Thus E(R) → F(R) is injective for every R. Evaluating natural transformations
   on sections then proves cancellation for maps from every algebraic space H.
2. For T → W, let P = Z ×_W T. By lem-trf-space-fibre-products-etale-covers it is an
   algebraic space. For every scheme R → T, pullback pasting identifies P ×_T R with
   Z ×_W R. This is a scheme closed in R, so P → T is a representable closed immersion.
   Step 1 also makes its maps on scheme sections injective.
3. Surjectivity of |Z| → |W| lifts a field representative of any point of T after a
   common field extension, giving a point of P above it. If two points of P have equal
   image in T, def-a1-algebraic-space-point-classes supplies a common extension on which
   their T-sections agree. Step 2 makes their P-sections agree, proving injectivity.
4. The scheme tests in step 2 are finite by lem-weil-pbc-closed-immersion-finite.
   Thus lem-sfb-finite-space-morphism-topology makes |P| → |T| continuous and closed
   for def-a1-space-point-topology. A continuous closed bijection is a homeomorphism.
   Together with step 2 this is a thickening, without any finite-order or finite-type
   assumption. -/
theorem thickening_mono_and_baseChange {B : Scheme.{u}} (Z W : AlgebraicSpace B)
    (i : Z ⟶ W)
    (hi : IsRepresentableWith (fun _ _ p ↦ IsClosedImmersion p.left) i.hom.hom)
    (hiTop : IsHomeomorph (mapPoint i.hom.hom)) :
    Mono i ∧ ∀ (T : AlgebraicSpace B) (t : T ⟶ W),
      IsRepresentableWith (fun _ _ p ↦ IsClosedImmersion p.left)
        (Limits.pullback.snd i.hom t.hom).hom ∧
      IsHomeomorph (mapPoint (Limits.pullback.snd i.hom t.hom).hom) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
