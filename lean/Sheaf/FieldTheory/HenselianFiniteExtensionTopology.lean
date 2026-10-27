/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q110
-/
module

public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.RingTheory.Valuation.ValuationRing
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.Topology.Algebra.Valued.ValuationTopology
public import Mathlib.FieldTheory.Separable
public import WeilConjectures.Mathlib.RingTheory.Henselian
import Sheaf.RingTheory.IntegralComponentHenselianPermanence

/-!
# Finite extensions of a henselian valued field

Source: Illusie--Laszlo--Orgogozo, Travaux de Gabber, XX 4.4, printed p. 374,
valued-field preliminaries for the forms of Krasner's lemma, referring to Bourbaki,
Algèbre commutative VI §8 (blueprint: lem-per-henselian-finite-extension-topology).

We use Mathlib's multiplicative convention: zero has value zero, the valuation ring
is given by values at most one, and balls have the form `v (x - a) < γ`. This is the
node's additive convention after reversing the order and writing the group
multiplicatively. `subgroups_basis.topology` uses radii in the actual value group.
A valuation subring `W` carries its canonical surjective valuation `W.valuation`;
equality of valuation subrings is precisely equivalence of valuations.
-/

@[expose] public section

universe u v w

namespace Valuation

/-- A nontrivial henselian valuation has a unique prolongation, up to equality of
valuation subrings, to a finite field extension. The prolonged ring is henselian and
its topology restricts to the given topology. In a separable extension, every valuation
topology inducing the given base topology equals the prolonged topology; equality of
topologies does not assert equality of their valuation subrings.

Source: ILO, XX 4.4, printed p. 374, valued-field preliminaries for Bourbaki VI §8
(blueprint: lem-per-henselian-finite-extension-topology).

Proof plan:
1. Put V = v.valuationSubring and let C be its integral closure in E. By
   lem-per-valuation-normalization-localizations, C is an integral domain, integral
   over V, with fraction field E. Its only idempotents are zero and one, so
   lem-trf-integral-component-henselian-permanence (Stacks 092X) makes C henselian local.
   This uses integrality, without assuming C is module-finite over V.
2. Localizing C at its unique maximal ideal gives C itself. The two localization
   clauses of lem-per-valuation-normalization-localizations show that C is a valuation
   subring W restricting to V, and that every such subring equals W. Its canonical
   valuation is the quotient of E by the units of W, with zero adjoined. In additive
   notation, order the nonzero classes by [x] ≤ [y] iff y/x belongs to W. The valuation
   ring alternative proves totality; cancellation proves translation invariance;
   1 + y/x in W proves the valuation inequality. Restriction identifies the base
   quotient by V's units with its ordered value subgroup. Henselianity is Step 1.
3. For any valuation on E nontrivial on F, the torsion assertion of
   lem-per-algebraic-valuation-coarsening-correspondence makes the base value group
   cofinal in the extension value group. Additively, choose ε > 0 in the base group;
   for δ ≥ 0 choose n > 0 with nδ in that group and use nδ + ε > δ; for δ < 0 use ε.
   Comparing zero-balls and translating proves equality of the induced topology with
   the restricted valuation topology, in particular the asserted equality for W.
4. Suppose the extension is separable and T gives a valuation topology inducing the
   base topology. Its restriction U to F is nontrivial: otherwise the torsion assertion
   in Step 3 forces T's ordered value group to be zero and its topology discrete,
   whereas v is nontrivial and its topology is not discrete. Step 3 identifies the
   restricted topology with v's. By lem-per-valuation-topology-common-coarsening there
   is a proper common valuation overring R of V and U. It is henselian by
   lem-per-henselian-valuation-coarsenings applied to V contained in R.
5. The coarsening correspondence lifts R to proper valuation overrings of W and T,
   both restricting to R. Apply the already established Steps 1--2 over the henselian
   ring R: its integral closure is henselian local by the integral-component theorem,
   and the normalization-localization theorem makes its prolongation ring unique.
   Thus the two lifted overrings coincide. This does not use the topology conclusion.
6. The resulting proper common overring of W and T, and the nontriviality of both
   valuations, allow lem-per-valuation-topology-common-coarsening over E to identify
   their topologies. The proof works without separability, but the last clause keeps
   precisely the node's separability hypothesis. No rank or completeness is assumed. -/
theorem henselian_finite_extension_topology
    {F : Type u} {E : Type v} [Field F] [Field E] [Algebra F E]
    [FiniteDimensional F E] {Γ₀ : Type w} [LinearOrderedCommGroupWithZero Γ₀]
    (v : Valuation F Γ₀) [v.IsNontrivial] [HenselianLocalRing v.valuationSubring] :
    ∃ W : ValuationSubring E,
      W.comap (algebraMap F E) = v.valuationSubring ∧
      HenselianLocalRing W ∧
      (∀ W' : ValuationSubring E,
        W'.comap (algebraMap F E) = v.valuationSubring → W' = W) ∧
      TopologicalSpace.induced (algebraMap F E) W.valuation.subgroups_basis.topology =
        v.subgroups_basis.topology ∧
      (Algebra.IsSeparable F E →
        ∀ T : ValuationSubring E,
          TopologicalSpace.induced (algebraMap F E) T.valuation.subgroups_basis.topology =
              v.subgroups_basis.topology →
            T.valuation.subgroups_basis.topology = W.valuation.subgroups_basis.topology) := by
  sorry

end Valuation
