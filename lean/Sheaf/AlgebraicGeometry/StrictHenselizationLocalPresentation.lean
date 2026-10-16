/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U2, SHEAF group J4
-/
module

public import Sheaf.AlgebraicGeometry.StrictHenselizationStructuralMap
public import Sheaf.RingTheory.IsStrictHenselization
public import Mathlib.RingTheory.Localization.AtPrime.Basic
import WeilConjectures.AlgebraicGeometry.EtaleLocalRingTriples
import Sheaf.RingTheory.EtaleResidueTriplesLocalizedStrictHenselization

/-! # Geometric strict henselization as a local-base algebra

Source: Stacks Project, Tag 04HX (lemma-describe-etale-local-ring).
(blueprint: lem-sbc-geometric-strict-henselization-local-presentation)
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

set_option maxHeartbeats 800000 in
-- The nested representative, affine-chart and triple diagrams require extra elaboration.
set_option backward.isDefEq.respectTransparency false in
/-- The geometric strict henselization is an algebraic strict henselization of a prime
localization, compatibly with the given structural ring map. There is no divisor here.
Source: Stacks Project, Tag 04HX (lemma-describe-etale-local-ring), using Tag 04GW.
(blueprint: lem-sbc-geometric-strict-henselization-local-presentation)

Proof: Let q be the image of the geometric point, and put A = R_q. Its residue field is
canonically the residue field at q. Inside the geometric field take the relative separable
closure K of that residue field. Affine pointed etale neighbourhoods compute the geometric
strict henselization ring. By the affine neighbourhood/triples comparison their coordinate
ring diagram is equivalent to etale residue triples over R at q with embeddings into K.
Passing from R to A does not change its colimit: etale algebras and their finitely many
presentation equations descend from A to R after inverting one element outside q, and
these principal localizations are pointed etale neighbourhoods. The equivalence between
residue triples over the local ring A and etale A-algebras pointed in K identifies this
colimit with the diagram defining Algebra.IsStrictHenselization. Each element outside q
is a unit in the colimit, so the structural R-map extends uniquely to A. The comparison
preserves the maps from R; applying the faithful spectrum functor and hb identifies that
R-map with b. Transport the A-algebra structure through the colimit ring isomorphism;
its composite with R -> A is therefore b. All colimit identifications are characterized
by their legs, so no arbitrary algebraic object is chosen from mere existence. -/
theorem strictHenselizationRing_local_presentation
    (R : CommRingCat.{u})
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (barY : Spec (.of Ω) ⟶ Spec R)
    (b : R ⟶ strictHenselizationRing barY)
    (hb : Spec.map b = strictHenselizationStructuralMap barY) :
    ∃ (q : Ideal R) (_ : q.IsPrime)
      (K : Type u) (_ : Field K)
      (_ : Algebra (IsLocalRing.ResidueField (Localization.AtPrime q)) K)
      (_ : IsSepClosure (IsLocalRing.ResidueField (Localization.AtPrime q)) K)
      (_ : Algebra (Localization.AtPrime q) K)
      (_ : IsScalarTower (Localization.AtPrime q)
        (IsLocalRing.ResidueField (Localization.AtPrime q)) K)
      (_ : Algebra (Localization.AtPrime q) (strictHenselizationRing barY)),
      (∀ r : R, algebraMap (Localization.AtPrime q) (strictHenselizationRing barY)
        (algebraMap R (Localization.AtPrime q) r) = b.hom r) ∧
      Algebra.IsStrictHenselization (Localization.AtPrime q) K
        (strictHenselizationRing barY) := by
  sorry

end AlgebraicGeometry.Scheme
