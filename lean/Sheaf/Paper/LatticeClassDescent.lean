/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B3
-/
module

public import Sheaf.Paper.LatticeSheafBasic

/-!
# Descent of integral lattice classes

Source: Bhatt--Scholze, Proposition 6.8.4(6), pp. 59--60
(blueprint: lem-weil-pbc-lattice-class-descent).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProEtale

/-- Integral lattice pairs admit an exact sheaf presentation by embedded images.
Source: Bhatt--Scholze, Proposition 6.8.4(6), descent of lattice pairs
(blueprint: lem-weil-pbc-lattice-class-descent).
Proof: quotient the lattice pairs over each object by intertwining integral isomorphisms.
Restriction is localization, with rationalization obtained by the sectionwise tensor
comparison on the slice. The injective coefficient inclusion makes the maps from
integral modules into the rational module injective. Thus intertwining isomorphisms
are unique and equivalent pairs are exactly those with equal embedded images.
A matching family of classes consequently supplies unique transition isomorphisms,
which satisfy the cocycle equation by uniqueness. Apply site-module-sheaf gluing
to the integral modules. Local finite bases give finite local freeness of the glued
module. The embeddings glue into the fixed rational module; the induced rationalization
and its local inverses glue, so it is an isomorphism. Uniqueness of the transition maps
makes the glued class unique. The resulting quotient presheaf is therefore a sheaf.
Its quotient maps are surjective, have the asserted exact kernel relation, and satisfy
the restriction clause because localization restricts precisely the embedded images.
No trivialization or fixed rank of the rational module is needed for this descent. -/
theorem exists_latticeClassPresentation (X : Scheme.{u})
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (L : SheafOfModules.{u + 1}
      (latticeModuleRing X (WithAbs (Padic.coefficientExtensionAbsoluteValue l E)))) :
    ∃ (F : Sheaf (Scheme.ProEt.topology X) (Type (u + 2)))
      (c : ∀ U : X.ProEt,
        IntegralLatticePair (integralLatticeCoefficientMap X l E) L U → F.obj.obj (op U)),
      IsLatticeClassPresentation (integralLatticeCoefficientMap X l E) L F c := by
  sorry

end AlgebraicGeometry.ProEtale
