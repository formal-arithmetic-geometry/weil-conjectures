/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
module

public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance

/-! # Finite affine cover bound from local acyclicity

Source: Stacks Project, Tag 0A51, Mayer-Vietoris induction.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

open Scheme Etale

/-- Local acyclicity on the inverse images of affine opens gives a finite-cover
cohomological bound. No injectivity or torsion assumption is needed for this step.

Source: Stacks Project, Tag 0A51, final paragraph of the proof, with the affine
vanishing used there made an explicit hypothesis.
(blueprint: lem-weil-pbc-finite-affine-cover-restriction-bound)

Proof: induct on n, simultaneously for all schemes and sheaves satisfying hlocal.
For n = 0 the sole affine open is the whole scheme, so hlocal gives the result
through the pullback and inverse-image identity isomorphisms. For n+1, write the
cover as one affine open U and the union V of the remaining n+1 affine opens.
Since X is separated over an affine scheme, intersections of affine opens in X
are affine. Hence U ∩ V has a cover by n+1 affine opens. The hypothesis hlocal
is inherited on both V and U ∩ V: their affine opens are affine opens in X, and
composition and pullback comparisons identify the two restrictions. Apply the
induction hypothesis to these two covers. The restriction on U has no positive
cohomology by hlocal. Pulling back the cover along i gives a two-open cover of Z;
Mayer-Vietoris in degree q has outer terms the degree q-1 group on the inverse
image of U ∩ V and the degree q groups on those of U and V. If q > n+1 all
three groups vanish by the preceding bounds, so exactness kills the middle group.
The inverse-image composition and coefficient-forgetting isomorphisms identify
these groups with the expressions displayed here. This argument also works for
empty opens, repeated members of the cover, and an arbitrary morphism i. -/
theorem Etale.subsingleton_H_of_affine_local_acyclic
    (Λ : Type (u + 1)) [CommRing Λ] {A : Type u} [CommRing A]
    {X Z : Scheme.{u}} (f : X ⟶ Spec (.of A)) [IsSeparated f] (i : Z ⟶ X)
    (J : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (hlocal : ∀ (W : X.Opens), IsAffineOpen W → ∀ (q : ℕ), 0 < q →
      Subsingleton (Sheaf.H
        ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj
          ((pullback.fst W.ι i)^*[ModuleCat.{u + 1} Λ].obj
            ((W.ι)^*[ModuleCat.{u + 1} Λ].obj J))) q))
    (n : ℕ) (U : Fin (n + 1) → X.Opens) (hU : ∀ j, IsAffineOpen (U j))
    (hcov : ⨆ j, U j = ⊤) (q : ℕ) (hq : n < q) :
    Subsingleton (Sheaf.H
      ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj
        ((i)^*[ModuleCat.{u + 1} Λ].obj J)) q) := by sorry

end AlgebraicGeometry
