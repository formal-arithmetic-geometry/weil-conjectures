/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.FiniteEtale
public import WeilConjectures.ConstructibleSheaf.Defs
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtaleOver
public import Mathlib.AlgebraicGeometry.Cover.Sigma
/-!
# Assembly of the finite etale local representatives

Source: Stacks Project, Tag 03RV and Descent Tag 02W5.
(blueprint: lem-weil-pbc-finite-local-models-descent-datum-existence)
-/

@[expose] public section
universe u
open CategoryTheory Opposite
namespace AlgebraicGeometry.Scheme
/-- The coproduct of a cover admits a finite etale representative of the restricted sheaf.

Source: Stacks Project, Tag 03RV, assembly of the local representatives before descent;
Descent Tag 02W5, gluing the local representations.
(blueprint: lem-weil-pbc-finite-local-models-descent-datum-existence)

Proof: Choose Q_i and its representation isomorphism from hrep by choice. The equivalence
between the site localized at U_i and the small etale site of U_i transports each isomorphism
back to the localized site. Let U be the coproduct of the U_i, as in Cover.sigma, and let V
be the coproduct of the Q_i. The coproduct of their structure morphisms is a morphism V to U.
Each U_i is an open and closed component of U, and its inverse image in V is Q_i. Thus this
morphism is finite by target locality and etale by source locality. This gives Q in
U.FiniteEtale. To identify the presheaves, cover any etale W over U by the inverse images of
these disjoint components. The local representation isomorphisms identify the sections of
E on each piece with morphisms from that piece to Q_i. The sheaf axiom for E and the gluing
property of morphisms to a scheme glue both directions uniquely. Disjointness makes overlap
compatibility automatic; the empty intersections use the empty-cover sheaf axiom. Uniqueness
shows naturality and that the two maps are inverse. The site equivalence expresses the
result in the displayed localized-site form. If the original cover is empty, U and V are
empty; each etale W over U is empty, and the same empty-cover axiom proves the claim. No
uniform rank bound and no finite index set are used. -/
theorem finiteLocalModels_descentDatum_exists
    (T : Scheme.{u}) (E : Sheaf T.smallEtaleTopology (Type (u + 1)))
    (𝒰 : Cover.{u} etalePrecoverage T)
    (hrep : ∀ i, ∃ Q : (𝒰.etalePrecoverageToEtale i).left.FiniteEtale,
      Nonempty (((Etale.overSheafEquiv (𝒰.etalePrecoverageToEtale i)
        (Type (u + 1))).functor.obj (E.over (𝒰.etalePrecoverageToEtale i))).obj ≅
          uliftYoneda.{u + 1}.obj Q.obj)) :
    let U := 𝒰.sigma.etalePrecoverageToEtale default
    ∃ (Q : U.left.FiniteEtale),
      Nonempty ((E.over U).obj ≅ (Etale.overToEtale U).op ⋙
        uliftYoneda.{u + 1}.obj Q.obj) := by sorry
end AlgebraicGeometry.Scheme
