/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtaleOver
public import Mathlib.AlgebraicGeometry.Cover.Sigma
import Sheaf.AlgebraicGeometry.Sites.SmallEtaleRepresentablePresheafSheaf
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtaleDisjointCover

/-!
# Representations over disjoint components

Source: Stacks Project, Tags 03RV and 02W5, gluing local representations.
(blueprint: lem-weil-pbc-etale-coproduct-representation)
-/

@[expose] public section

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme

/-- Chosen etale representatives on a family of components represent the transported
restriction to their coproduct. Finiteness and joint surjectivity onto T are not needed.

Source: Stacks Project, Tag 03RV (lemma-characterize-finite-locally-constant), the
assembly of local representations; Tag 02W5 (lemma-descent-data-sheaves), the sheaf
identification in the effective case. This is the disjoint-cover instance of that argument.
(blueprint: lem-weil-pbc-etale-coproduct-representation)

Proof: Put B = coproduct U_i and V = coproduct Q_i, with the displayed structure map.
For an etale W over B, let W_i = W times_B U_i. The coprojections U_i to B are open
immersions, disjoint, and jointly surjective; their base changes give a disjoint etale
cover of W. Its component square with V is cartesian: the inverse image of U_i in V
is Q_i, as follows from disjointness and the coproduct universal property. A morphism
W_i to V over B therefore factors uniquely through Q_i over U_i. Under the localized
site equivalence, the restriction of the transported sheaf to W_i is the original
sheaf evaluated at W_i to U_i to T. Apply the given representation isomorphism on
each W_i. The disjoint-cover sheaf axiom identifies sections on W with the product
of the sections on W_i. Representable presheaves satisfy the same sheaf axiom, so
the local maps to Q_i glue uniquely to a map W to V over B. Applying the inverse
local isomorphisms and gluing sections gives its inverse. Both composites restrict
to the identity on every W_i, hence are identities by separatedness. For a morphism
W' to W over B, its pullbacks W'_i to W_i commute with restriction, and naturality
of the given local isomorphisms followed by uniqueness of gluing proves naturality
of the assembled maps. These maps are the claimed presheaf isomorphism. For an empty
index type B, V and every W are empty, and the empty-cover axiom makes the section
sets singletons; thus the same construction works. No bound on the index set or
on the ranks is used. -/
theorem etaleCoproduct_representation
    {ι : Type u} (T : Scheme.{u})
    (E : Sheaf T.smallEtaleTopology (Type (u + 1)))
    (U : ι → T.Etale) (Q : ∀ i, (U i).left.Etale)
    [Etale (CategoryTheory.Limits.Sigma.desc fun i ↦ (U i).hom)]
    [Etale (CategoryTheory.Limits.Sigma.map fun i ↦ (Q i).hom)]
    (hrep : ∀ i,
      Nonempty (((Etale.overSheafEquiv (U i) (Type (u + 1))).functor.obj
        (E.over (U i))).obj ≅ uliftYoneda.{u + 1}.obj (Q i))) :
    let B := Etale.mk (CategoryTheory.Limits.Sigma.desc fun i ↦ (U i).hom)
    Nonempty (((Etale.overSheafEquiv B (Type (u + 1))).functor.obj
      (E.over B)).obj ≅ uliftYoneda.{u + 1}.obj
        (Etale.mk (CategoryTheory.Limits.Sigma.map fun i ↦ (Q i).hom))) := by sorry

end AlgebraicGeometry.Scheme
