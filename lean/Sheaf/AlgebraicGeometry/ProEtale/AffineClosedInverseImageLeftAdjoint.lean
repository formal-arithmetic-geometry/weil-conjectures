/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NE
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleInverseImage
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Mathlib.CategoryTheory.Yoneda
import Mathlib.CategoryTheory.Sites.DenseSubsite.SheafEquiv
import WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.Affine
import Sheaf.AlgebraicGeometry.ProEtale.AffineClosedSiteFunctorProperties
import Sheaf.AlgebraicGeometry.IndEtaleBasisWeaklyContractibleCover
import Sheaf.CategoryTheory.Sites.LowerShriekCoveringGenerators
import Sheaf.AlgebraicGeometry.ProEtale.AffineClosedInverseImageEvaluation
import Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory
import Sheaf.AlgebraicGeometry.ProEtaleRingInverseImage

/-!
# An extra left adjoint for affine closed pro-etale inverse image

Source: Stacks Project, Tag 09BL, clause (3), using Tag 09BK
(blueprint: lem-weil-pbc-affine-closed-inverse-image-left-adjoint).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- The ordinary inverse image on set-valued small pro-etale sheaves for a closed
immersion of affine schemes has a left adjoint. The adjunction provides the bijections
`Hom(L G, F) ≃ Hom(G, i⁻¹ F)`, natural in both `G` and `F`.

Source: Stacks Project, Tag 09BL, clause (3), and Tag 09BK
(blueprint: lem-weil-pbc-affine-closed-inverse-image-left-adjoint).

Proof plan:
1. Restrict to the full affine ind-etale bases. Cover-density and the induced topology
   give restriction equivalences R_X and R_Z, with quasi-inverses E_X and E_Z
   (lem-weil-pbc-ind-etale-basis and lem-pc-fppf-dense-sheaf-equivalence).
2. Put T = R_Z i⁻¹ E_X for the ordinary base-change inverse image. The canonical
   closed-site lift v and its evaluation formula identify T(F)(V) naturally with F(v(V))
   for weakly contractible V (lem-weil-pbc-affine-closed-site-functor-properties and
   lem-weil-pbc-affine-closed-inverse-image-evaluation). Transport the ordinary
   inverse-image/direct-image adjunction through the equivalences; T preserves finite limits.
3. Sheafify the representable presheaf of v(V). Sheafification's universal property
   and Yoneda identify maps from this sheaf to F naturally with F(v(V)), hence T(F)(V)
   (def-weil-pbc-sheafification and lem-galois-yoneda-hom-bijection).
4. The basis has covers by weakly contractible objects
   (lem-weil-pbc-ind-etale-basis-wcontractible-cover). Apply
   lem-weil-pbc-topos-lower-shriek-existence-on-covering-generators to obtain L ⊣ T.
5. Transport L back as E_X L R_Z. Full faithfulness of both restriction equivalences,
   L ⊣ T, and E_X R_X ≅ id give the required Hom bijections, naturally in both variables.
-/
theorem exists_affineClosedInverseImageLeftAdjoint {Z X : Scheme.{u}}
    [IsAffine Z] [IsAffine X] (i : Z ⟶ X) [IsClosedImmersion i] :
    ∃ L : Sheaf (ProEt.topology Z) (Type (u + 1)) ⥤
      Sheaf (ProEt.topology X) (Type (u + 1)),
      Nonempty (L ⊣ proEtaleSheafInverseImage i (Type (u + 1))) := sorry

end AlgebraicGeometry.Scheme
