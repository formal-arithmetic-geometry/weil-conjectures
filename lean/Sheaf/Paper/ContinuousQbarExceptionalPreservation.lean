/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K8
-/
module

public import Sheaf.Paper.LocalizingExceptionalAdjoint
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Sheaf.Paper.CondensedConstantConstructibility
import Sheaf.Paper.LocalizingAdmissibleCoefficients

/-!
# Exceptional preservation for the all-continuous-map algebraic-closure coefficient

Source: blueprint main-20261015, sec-six-functors-basics/sk-thm-restriction,
first two proof paragraphs, with the coefficient convention of sk-def-localizing-closure.
This isolates the geometric preservation assertion; no restricted functor or adjunction
is constructed here.
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Scheme
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- The given localizing right adjoint preserves constructible finite-Tor complexes for
C(-, Qbar_ell), with all continuous maps for the induced ell-adic topology.
This assertion does not identify this coefficient with `Profinite.padicAlgClRingObj`.

Source: blueprint main-20261015, sk-thm-restriction.proof.md, first two paragraphs;
sk-def-localizing-closure, coefficient convention
(blueprint: lem-sfb-continuous-qbar-exceptional-preservation).

Proof in words:
Choose finite affine covers V of Y and U of their inverse images in X. A finite
presentation of each chart algebra gives a closed immersion U into affine d-space over
V; evaluation on generators is surjective and identifies the composite with f on U.
Open extension by zero and its pullback adjunction, composition of compact support,
and uniqueness of right adjoints identify the restriction of G K to U with i^! p^! v^* K.
These identifications use the supplied adjunction, so they apply to this G and to the
chosen compactification, not merely to an unspecified exceptional functor.

Compute the affine-space exceptional image by the relative purity calculation
p^! L = p^* L(d)[2d] for this continuous-function coefficient. Pullback carries a finite
constant scalar presentation to the same presentation, and the Tate line is locally
free of rank one. Thus boundedness, finite constant models, and finite Tor intervals
are preserved, with the degree interval translated by -2d. For the closed immersion,
identify i^! with the fiber of L -> Rj_* j^* L, restricted to the closed complement.
The rational open-direct-image calculation gives finite constant constructibility and
finite cohomological and Tor bounds for Rj_* j^* L. The support triangle therefore
gives those properties for i^! L. All of these calculations must use C(-, Qbar_ell)
itself; finite-subextension-valued coefficient statements cannot substitute for them.

The finitely many charts now give bounded constructible finite-Tor restrictions of
G K. Exact open restriction commutes with cohomology and derived tensor. Take a minimum
of the local lower endpoints and a maximum of the upper endpoints, separately for
cohomology and Tor; vanishing on the cover detects global vanishing. Add the closed
complements of the chart stratifications and take a finite common refinement. Every
nonempty refined stratum lies in a chart, where its cohomology has the restricted
finite constant models. This proves global constructibility and the global Tor bound.
When X is empty, the empty-cover sheaf axiom makes every module zero; no extrema are
needed. Zero complexes and empty strata are covered by the zero presentations.
Finally transport all constructions through the given condensed-ring isomorphism hΛ.
-/
theorem continuousQbarExceptional_preserves_constructibleFiniteTor
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))]
    [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
    (hΛ : Nonempty
      (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj (PadicAlgCl ℓ))))
    (c : Compactification.BoundaryCompactification f)
    (h : ∀ K, localizingClosureProEtale Λ X K → localizingClosureProEtale Λ Y
      ((rightDerivedLowerShriekOfCompactification Λ c.obj.obj).obj K))
    (G : (localizingClosureProEtale Λ Y).FullSubcategory ⥤
      (localizingClosureProEtale Λ X).FullSubcategory)
    (adj : localizingLowerShriek Λ c.obj.obj h ⊣ G) :
    ∀ K : (localizingClosureProEtale Λ Y).FullSubcategory,
      (constantModelBoundedConstructible Λ Y K.obj ∧
        DerivedCategory.finiteTorAmplitude _ K.obj) →
      constantModelBoundedConstructible Λ X (G.obj K).obj ∧
        DerivedCategory.finiteTorAmplitude _ (G.obj K).obj := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
