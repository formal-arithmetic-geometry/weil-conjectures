/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.RingTheory.IsStrictHenselization
public import Sheaf.AlgebraicGeometry.EtaleResidueTriples

/-!
# Comparing two colimit presentations of strict henselization

Source: Stacks Project, Algebra, Tag 04GW, the pointed-algebra description of triples.
(blueprint: lem-sc-strict-henselization-triples-presentation).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme

namespace Algebra

/-- A strict henselization specified using pointed etale algebras is also a colimit
of residue triples, with exactly the original structural map from the base ring.
Source: Stacks Project, Tag 04GW, the identification of triples with pointed algebras.

Proof: Take the point `p` corresponding to the maximal ideal of `R`. Its scheme
residue field is canonically isomorphic over `R` to `R/m`. Transport the given algebra
structure and separable-closure structure on `K` along this isomorphism.
Send a residue triple to its etale `R`-algebra `B` with map to `K` given by evaluation
at its prime followed by its residue embedding. The compatibility equation makes
this an `R`-algebra map. Morphisms are precisely the algebra maps commuting with
these maps to `K`, so this functor is fully faithful. Conversely, for a pointed
etale algebra `B → K`, take the kernel prime. The map factors uniquely through
its residue field: first pass to the quotient by the kernel, then extend to its
fraction field, since every nonzero image in the field `K` is invertible.
The contraction of this prime is `m`, since the given map `R → K` factors through
the injective field map `R/m → K`. This constructs a triple and an isomorphism
back to the pointed algebra. The functor is therefore an equivalence, and it
identifies the underlying-ring diagrams and their structural maps from `R`.
Transport the universal cocone in `hC` along this equivalence and the given
isomorphism of its vertex with `C`. Forgetting the algebra structure preserves
this colimit: the triples category is filtered, hence nonempty and connected;
a ring cocone acquires a unique compatible `R`-algebra structure from the common
maps out of `R`. Thus the transported cocone is a ring colimit with vertex `C`.
Every leg is an `R`-algebra map, giving the final displayed compatibility.
(blueprint: lem-sc-strict-henselization-triples-presentation). -/
theorem IsStrictHenselization.triples_presentation
    (R K C : Type u) [CommRing R] [IsLocalRing R] [Field K]
    [Algebra (IsLocalRing.ResidueField R) K] [IsSepClosure (IsLocalRing.ResidueField R) K]
    [Algebra R K] [IsScalarTower R (IsLocalRing.ResidueField R) K]
    [CommRing C] [Algebra R C] (hC : IsStrictHenselization R K C) :
    ∃ (p : Spec (CommRingCat.of R)), p.asIdeal = IsLocalRing.maximalIdeal R ∧
      ∃ (a : Algebra ((Spec (CommRingCat.of R)).residueField p) K),
        letI := a
        IsSepClosure ((Spec (CommRingCat.of R)).residueField p) K ∧
        ∃ (ι : etaleResidueTriplesRingDiagram (CommRingCat.of R) p K
            (CommRingCat.ofHom (algebraMap ((Spec (CommRingCat.of R)).residueField p) K)) ⟶
            (Functor.const _).obj (CommRingCat.of C)),
          Nonempty (IsColimit (Cocone.mk (CommRingCat.of C) ι)) ∧
          ∀ t, t.α ≫ ι.app t = CommRingCat.ofHom (algebraMap R C) := by
  sorry

end Algebra
