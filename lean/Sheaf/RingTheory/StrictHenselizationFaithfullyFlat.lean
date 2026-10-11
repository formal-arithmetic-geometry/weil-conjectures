/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T1
-/
import Sheaf.RingTheory.StrictHenselizationTriples
import Mathlib.RingTheory.RingHom.FaithfullyFlat

/-!
# Faithful flatness of strict henselization

Source: Stacks Project, More on Algebra, Lemma Tag 07QM, part (1), using the
strict henselization of Algebra, Lemma Tag 04GP
(blueprint: lem-sc-strict-henselization-faithfully-flat).
-/

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- The canonical map from a local ring to the colimit of its etale residue triples,
pointed in a separable closure of its residue field, is faithfully flat.
Source: Stacks Project, More on Algebra, Tag 07QM (1), and Algebra, Tag 04GP.
(blueprint: lem-sc-strict-henselization-faithfully-flat).

Proof:
1. Apply lem-weil-pbc-strict-henselization-triples at the maximal ideal. Its colimit
is the strict henselization, and the compatibility of the structure maps identifies
`ρ` with the canonical map from `R` to this colimit. The chosen residue embedding
is the one specified by the algebra structure on `K`.
2. Each ring in the diagram is etale over `R`, hence flat by
lem-weil-pbc-etale-algebra-flat. The underlying module of the ring colimit is the
filtered colimit of these flat modules, so lem-weil-pbc-filtered-colimit-flat-modules
makes the colimit flat over `R`.
3. By lem-weil-pbc-strict-henselization-triples the colimit is local, and its maximal
ideal contracts to the maximal ideal of `R`. Thus `ρ` is a local ring map. A flat
local homomorphism of local rings is faithfully flat, by
lem-pc-local-flat-faithful-flat-reflects-surjective. -/
theorem strictHenselization_faithfullyFlat
    (R : CommRingCat.{u}) [IsLocalRing R] (p : Spec R)
    (hp : p.asIdeal = IsLocalRing.maximalIdeal R)
    (K : Type u) [Field K] [Algebra ((Spec R).residueField p) K]
    [IsSepClosure ((Spec R).residueField p) K]
    (c : Cocone (etaleResidueTriplesRingDiagram R p K
      (CommRingCat.ofHom (algebraMap ((Spec R).residueField p) K))))
    (hc : IsColimit c) (ρ : R ⟶ c.pt)
    (hρ : ∀ t : EtaleResidueTriples R p K
      (CommRingCat.ofHom (algebraMap ((Spec R).residueField p) K)),
      t.α ≫ c.ι.app t = ρ) :
    ρ.hom.FaithfullyFlat := by
  sorry

end AlgebraicGeometry.Scheme
