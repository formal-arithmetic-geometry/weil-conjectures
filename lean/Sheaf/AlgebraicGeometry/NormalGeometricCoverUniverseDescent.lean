/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S8
-/
module

public import Sheaf.AlgebraicGeometry.SchemeUniverseEnlargement
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.ValuativeCriterion
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed

/-!
# Small finite etale components of universe-enlarged geometric coverings

Source: Bhatt--Scholze, The pro-etale topology for schemes, proof of Lemma 7.4.10;
Stacks Project, Tags 01JA and 01WG
(blueprint: lem-a1-normal-geometric-cover-universe-descent).
-/

@[expose] public section

set_option autoImplicit false
universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A nonempty geometric covering of the canonical universe enlargement of a normal
connected Noetherian scheme contains the enlargement of a finite etale surjective cover
in the original universe. This assertion concerns schemes and their morphisms only.

Source: Bhatt--Scholze, proof of Lemma 7.4.10; Stacks Project, Tag 01JA (affine gluing)
and Tag 01WG (finite morphisms)
(blueprint: lem-a1-normal-geometric-cover-universe-descent).

Proof: on each affine chart Spec A of X, canonical enlargement replaces A by ULift A.
The prime spectrum homeomorphisms and the local ring equivalences glue, using the
explicit affine-colimit universal property defining schemeUniverseLift. Consequently
normal local domains, connectedness, local Noetherianity and quasi-compactness transport
to the enlarged base. Apply normalGeometricCoverComponents to q and choose the component
of any point of Z. Its map to the enlarged base is finite etale and surjective.
Over an original affine chart this component is Spec B for a finite ULift A-algebra B.
A finite module is a quotient of a finite power of A, so its underlying set is small
in the original universe. Transport the ring and algebra structures to a small model.
Transport the overlap isomorphisms as well; their cocycle identities and their inverses
are preserved by the faithful change of carriers. Glue these affine models to Y over X.
Finiteness, etaleness and surjectivity hold on the affine charts and are invariant under
these ring equivalences, so the resulting p has all three properties. The lifted gluing
identifies schemeUniverseLift Y with the chosen component over schemeUniverseLift X.
Compose this identification with the component inclusion to obtain i; equality over
the base gives i followed by q equal to schemeUniverseLiftMap p. No bound on the number
of components of Z and no quasi-compactness of Z are used. -/
theorem normalGeometricCover_universeDescent
    {X : Scheme.{u}} [ConnectedSpace X] [IsLocallyNoetherian X] [CompactSpace X]
    (hnormal : ∀ x : X, IsDomain (X.presheaf.stalk x) ∧
      IsIntegrallyClosed (X.presheaf.stalk x))
    {Z : Scheme.{u + 1}} [Nonempty Z]
    (q : Z ⟶ schemeUniverseLift.{u, u + 1} X) (hetale : Etale q)
    (hval : ValuativeCriterion q) :
    ∃ (Y : Scheme.{u}) (p : Y ⟶ X),
      IsFinite p ∧ Etale p ∧ Surjective p ∧
      ∃ i : schemeUniverseLift.{u, u + 1} Y ⟶ Z,
        i ≫ q = schemeUniverseLiftMap.{u, u + 1} p := by sorry

end AlgebraicGeometry
