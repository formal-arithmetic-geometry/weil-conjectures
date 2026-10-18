/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q08
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Sheaf.AlgebraicGeometry.EtaleSpaceLocallyQuasiFinite
import Sheaf.AlgebraicGeometry.SeparatedLocallyQuasiFiniteSpaceRepresentable

/-!
# Separated étale algebraic spaces over schemes are schemes

Source: Stacks Project, Spaces Morphisms, Tags 03XU and 03XX, Section 0417
(blueprint: lem-a1-separated-etale-space-scheme).

Working on `Sch/X` encodes the structure map to `X`. Consequently the product of
presheaves on this category is the fibre product over `X`, and a Yoneda isomorphism
on this category is an isomorphism over `X`.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- A separated algebraic space étale over a scheme is represented by an étale scheme,
without any quasi-compactness hypothesis. The first assumption tests étaleness on
all representable étale scheme charts; the second tests the relative diagonal for
closed immersion after every scheme base change.
Source: Stacks Project, Spaces Morphisms, Tags 03XU and 03XX, Section 0417
(blueprint: lem-a1-separated-etale-space-scheme).

Proof:
1. Apply `lem-a1-etale-space-locally-quasi-finite` (Tag 03XU) to the chartwise
   étale hypothesis: every scheme chart has locally quasi-finite structure map.
2. The diagonal condition is precisely separatedness, by
   `def-weil-proper-morphism` and `def-weil-closed-immersion`, with the latter
   property tested on schemes as in `def-trf-algebraic-space`.
3. Apply `lem-a1-separated-locally-qf-space-representable` (Tag 03XX) with
   base and target both `X`. Obtain `Z` over `X` and an isomorphism `h_Z ≅ E` over `X`.
4. This isomorphism is a representable étale scheme chart: each scheme base
   change is an isomorphism, hence an open immersion, hence étale by
   `lem-weil-pbc-etale-composition-cancellation`(1). Apply the chartwise hypothesis
   to this chart. Its composite to `X` is `Z.hom`, which is therefore étale. -/
theorem exists_scheme_of_separated_etale {X : Scheme.{u}} (E : AlgebraicSpace X)
    (het : ∀ (V : Over X) (a : yoneda.obj V ⟶ E.obj.obj), IsEtale a → Etale V.hom)
    (hsep : IsRepresentableWith (fun _ _ p ↦ IsClosedImmersion p.left)
      (prod.lift (𝟙 E.obj.obj) (𝟙 E.obj.obj))) :
    ∃ Z : Over X, Nonempty (yoneda.obj Z ≅ E.obj.obj) ∧ Etale Z.hom := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
