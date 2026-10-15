module

public import Sheaf.AlgebraicGeometry.ProEtale.ClosedSiteLift
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

import Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import Mathlib.CategoryTheory.Sites.DenseSubsite.SheafEquiv

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

/-- Affine coordinates transport projectivity of evaluation and the closed-fibre
specialization condition. The ideal is the actual kernel of the global-sections
map of the closed base change, rather than an ideal selected from existence.

Source: Stacks Project, Tag 09AC, first reduction; Tags 09A5 and 03CF for
localization, and Tag 01R8 for the affine closed immersion
(blueprint: new-lem-weil-pbc-specialization-affine-coordinates).

Proof. Localize the pro-etale site at V. Its sheaf category is the slice topos
at the sheaf represented by V; projectivity of that representable says that the
terminal object of this slice is projective. Explicitly, the forgetful functor
from the slice preserves epimorphisms, so the identity of the representable
lifts through any epimorphism to it. The equivalence with the small site of
V.left preserves this property and evaluates it at the identity object.
Transport along V.left.isoSpec, then restrict along the dense affine ind-etale
basis. Restriction is an equivalence, preserves epimorphisms, and keeps the
identity object's sections. This proves the first clause.
The closed base change is affine and its global-sections map is surjective.
The first isomorphism theorem identifies its ring with A/I, for the displayed
kernel I. The resulting Spec isomorphism commutes with its map to V.left.
Continuous isomorphisms preserve specialization; transport the given point and
its specialization through these isomorphisms. Finally use the pullback along
the identity to express the closed point as a point of the displayed pullback.
If V is empty, A is the zero ring, both spectra are empty, and the geometric
clause is vacuous. -/
theorem specialization_affine_coordinates
    {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (V : X.ProEt) [IsAffine V.left]
    (hweak : ∀ (P Q : Sheaf (ProEt.topology X) (Type (u + 1))) (φ : P ⟶ Q),
      Epi φ → Function.Surjective (φ.hom.app (op V)))
    (hspec : ∀ x : V.left, ∃ z : ↥(pullback V.hom i),
      Specializes x ((pullback.fst V.hom i) z)) :
    let A := Γ(V.left, ⊤)
    let I := RingHom.ker (pullback.fst V.hom i).appTop.hom
    let B := AffineProEt.ofEtale (𝟙 (Spec A))
    (∀ (P Q : Sheaf (AffineProEt.topology (Spec A)) (Type (u + 1))) (φ : P ⟶ Q),
      Epi φ → Function.Surjective (φ.hom.app (op B))) ∧
    (∀ x : B.left, ∃ z : ↥(pullback B.hom
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))),
      Specializes x ((pullback.fst B.hom
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))) z)) := by
  sorry

end AlgebraicGeometry.Scheme
