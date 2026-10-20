/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G3
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import WeilConjectures.RingTheory.Depth

import WeilConjectures.AlgebraicGeometry.Morphisms.DepthTwoFiniteExtensionUniqueness
import Sheaf.AlgebraicGeometry.Morphisms.RegularCodimensionTwoFiniteEtaleModel

/-!
# Flatness at a regular codimension-two boundary point

Source: Stacks Project, Tags 0BMA, 0EY7 and 0EY6(2).
(blueprint: lem-sbc-regular-codimension-two-finite-flat-stalk)
-/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme

/-- A supplied finite depth-two extension has a flat stalk map at a missing point
when all missing target points are regular of local dimension at least two.

Source: Stacks Project, Tag 0BMA (local purity), Tag 0EY7 (Noetherian
extension), and Tag 0EY6(2) (uniqueness of the depth-two extension).
(blueprint: lem-sbc-regular-codimension-two-finite-flat-stalk)

Proof: Choose a Noetherian affine open W around p(z). Restrict V and p to W.
Open-immersion stalk isomorphisms preserve the regularity, dimension and
source-depth hypotheses. At every point of W outside V the regular local
ring has dimension at least two, so 0BMA gives purity for its punctured
spectrum. Apply 0EY7 on W to extend the finite etale restriction of p to
some finite etale r over W. Explicitly, choose a generic point of a component
of the missing closed set. Its local inverse image of the current open is
the punctured spectrum. Local purity extends the cover there; spreading
finite presentation and then finiteness and etaleness enlarges the open
while preserving the given cover. Noetherian induction yields r on W.
Regular local rings have depth equal to dimension, so W has depth at least
two outside V. The etale extension r also has source depth at least two
there: for each of its source points the flat local depth formula bounds
its depth below by that of the target. Both p restricted to W and r are
therefore finite extensions of the same cover with source boundary depth
at least two. The regular-generator lemma supplies the regular sequence,
`IsLocalRing.depth_eq_add_of_flat_local` supplies the source depth lower bound,
and `iso_of_finite_depth_two_extensions` gives the isomorphism over W.
By the Hartogs identity used in 0EY6(2), their finite
structure algebras are the direct image of that cover's structure algebra.
The identity on the open consequently extends to an algebra isomorphism
and hence an isomorphism of the finite W-schemes. Transport flatness of r
across this isomorphism to the stalk map of p at z, using the open-immersion
stalk isomorphisms to return to L. The argument is local in L and needs no
global quasi-compactness. If the source is empty there is no z; if V is all
of L there is no missing point. For a disconnected target the chosen
Noetherian affine W and the same induction apply without irreducibility. -/
theorem flat_stalk_of_regular_codimension_two_depth_two_extension
    {L E : Scheme.{u}} [IsLocallyNoetherian L] (V : L.Opens)
    (hboundary : ∀ y : L, y ∉ V → IsRegularLocalRing (L.presheaf.stalk y) ∧
      (2 : WithBot ℕ∞) ≤ ringKrullDim (L.presheaf.stalk y))
    (p : E ⟶ L) [IsFinite p] [Etale (p ∣_ V)]
    (hsource : ∀ z : E, p z ∉ V →
      (2 : ℕ∞) ≤ IsLocalRing.depth (R := E.presheaf.stalk z) (E.presheaf.stalk z))
    (z : E) (hz : p z ∉ V) :
    (p.stalkMap z).hom.Flat := by
  have _ := hz
  obtain ⟨F, r, hfin, het, hdepth, e, he⟩ :=
    exists_finite_etale_depth_two_model V hboundary p
  have : IsFinite r := hfin
  have : Etale r := het
  obtain ⟨i, hi⟩ := iso_of_finite_depth_two_extensions V r p hdepth hsource e he
  have hp : p = i.inv ≫ r := by
    rw [← hi, ← Category.assoc, i.inv_hom_id, Category.id_comp]
  have : Flat p := by
    rw [hp]
    infer_instance
  exact Flat.stalkMap p z

end AlgebraicGeometry.Scheme
