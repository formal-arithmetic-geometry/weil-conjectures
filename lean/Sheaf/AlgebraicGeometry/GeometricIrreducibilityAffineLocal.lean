/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q73
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Irreducible
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Over
import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
# Affine-local geometric irreducibility

Source: Stacks Project, Tag 038G, `lemma-geometrically-irreducible-local`, equivalence
(1) and (2) for irreducible schemes and the final assertion
(blueprint: lem-zl-geometric-irreducibility-affine-local).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- For an irreducible scheme over a field, geometric irreducibility is equivalent to
geometric irreducibility of the spectra of the section rings of every nonempty affine open.
The structure map on each such spectrum is induced by the canonical affine open immersion.
Moreover, every nonempty open subscheme of a geometrically irreducible scheme is geometrically
irreducible. No reducedness, quasi-compactness, or finite-type assumption is needed.

Source: Stacks Project, Tag 038G, `lemma-geometrically-irreducible-local`
(blueprint: lem-zl-geometric-irreducibility-affine-local).

Proof: For any field extension K/k, the projection X_K → X is surjective: Spec K → Spec k
is surjective (lem-pc-field-extension-surjective), and surjectivity is preserved by base change
(lem-weil-pbc-surjective-base-change). Thus the inverse image of a nonempty open is nonempty.
If X_K is irreducible, that inverse image is irreducible. For affine U, the canonical
isomorphism U ≅ Spec Γ(X,U) respects the induced structure morphism to Spec k. This proves
the forward implication and, without affineness, the moreover assertion.

Conversely, the nonempty affine opens cover X and form a nonempty family, since X is
irreducible. Their inverse images cover X_K and are irreducible by the hypothesis on their
spectra. Any two intersect: their intersection in X is nonempty by irreducibility, and its
inverse image is nonempty by surjectivity. A nonempty family of pairwise intersecting
irreducible opens covers an irreducible space. Indeed, in a covering by two closed sets,
each irreducible open lies in one of them. Choose one lying in the first closed set; its
intersection with any other member is a nonempty open, hence dense in that irreducible
member. The other member therefore also lies in the first closed set. Thus the first closed
set contains the whole space. Apply this to X_K for every K/k. -/
theorem geometricallyIrreducible_affineLocal
    (k : Type u) [Field k] (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [IrreducibleSpace X] :
    (GeometricallyIrreducible (X ↘ Spec (.of k)) ↔
      ∀ (U : X.Opens) (hU : IsAffineOpen U), (U : Set X).Nonempty →
        GeometricallyIrreducible (hU.fromSpec ≫ X ↘ Spec (.of k))) ∧
    (GeometricallyIrreducible (X ↘ Spec (.of k)) →
      ∀ (V : X.Opens), (V : Set X).Nonempty →
        GeometricallyIrreducible (V.ι ≫ X ↘ Spec (.of k))) := by
  sorry

end AlgebraicGeometry
