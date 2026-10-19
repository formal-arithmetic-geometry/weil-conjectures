/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q05
-/
module

public import Mathlib.FieldTheory.Separable
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.Topology.Algebra.Valued.ValuationTopology
public import WeilConjectures.Mathlib.RingTheory.Henselian

/-!
# Finite extensions of henselian valued fields

Source: Illusie--Laszlo--Orgogozo, Travaux de Gabber, Exposé XX, section 4.4,
printed page 374, valued-algebraic preliminaries for the forms of Krasner's lemma;
Bourbaki, Algèbre commutative VI, section 8
(blueprint: lem-per-henselian-finite-extension-topology).
-/

@[expose] public section

set_option autoImplicit false

universe u v w

namespace Valuation

/-- A nontrivial henselian valuation has a unique prolongation, up to equality of valuation
subrings, to a finite field extension. Its ring remains henselian, and its topology restricts
correctly. For a separable extension, any valuation topology with that restriction is the same
extension topology, even when its valuation ring differs from the prolonged valuation ring.

Source: ILO, Travaux de Gabber, Exposé XX, section 4.4, printed page 374, preliminaries for
Krasner's lemma; Bourbaki, Algèbre commutative VI, section 8.
(blueprint: lem-per-henselian-finite-extension-topology)

Mathlib uses multiplicative valuations: its zero corresponds to additive infinity, and
`v x ≤ 1` to additive `v(x) ≥ 0`. The topology `subgroups_basis.topology` uses the actual value
group. Every valuation subring has a canonical surjective valuation, so quantifying over
valuation subrings in the last clause includes all valuation topologies, in any value-group
universe. Equality of their topologies is deliberately distinct from equality of their rings.

Proof (the node's four steps):
1. Put `V = 𝒪_v` and let `C` be the integral closure of `V` in `E`. By
   [lem-per-valuation-normalization-localizations], `C` is a nonzero domain integral over `V`
   with fraction field `E`; a domain has only the idempotents `0, 1`, so
   [lem-trf-integral-component-henselian-permanence] makes `C` henselian local, with maximal
   ideal `𝔫`, and `C_𝔫 = C`. The normalization lemma makes `C` a valuation ring with
   `C ∩ F = V`; conversely every prolongation ring is `C_𝔪` for a maximal ideal `𝔪` of `C`, and
   locality forces `𝔪 = 𝔫`. This gives existence, uniqueness up to equality of valuation
   subrings, and henselianity of the prolonged ring.
2. Let `ṽ : E → Δ ∪ {∞}` be the valuation of `C`, with restricted value group `Γ`. By
   [lem-per-algebraic-valuation-coarsening-correspondence], `Δ/Γ` is torsion. Fix `ε ∈ Γ`,
   `ε > 0` (`v` is nontrivial). For `δ ∈ Δ` choose `n > 0` with `nδ ∈ Γ`; then
   `γ = n·max(δ, 0) + ε ∈ Γ` and `γ > δ`, so `Γ` is cofinal in `Δ`. Hence the `ṽ`-balls meet
   `F` in exactly the `v`-balls up to refinement, and the induced topology on `F` is the
   `v`-topology.
3. Let `w` be a valuation on `E` inducing the `v`-topology on `F`, `W = 𝒪_w`, `V_w = W ∩ F`.
   By [lem-per-algebraic-valuation-coarsening-correspondence] and the inequality of Step 2, the
   value group of `w|_F` is cofinal in that of `w`; `w|_F` is nontrivial, since otherwise `w`
   would be trivial and its restricted topology discrete. So the topology of `w|_F` is the
   `v`-topology, and [lem-per-valuation-topology-common-coarsening] gives a proper valuation ring
   `U ⊊ F` containing `V_w` and `V`; by [lem-per-henselian-valuation-coarsenings], `U` is
   henselian.
4. By [lem-per-algebraic-valuation-coarsening-correspondence], applied to `W` over `V_w` and to
   `C` over `V`, there are proper valuation overrings `U_W ⊇ W`, `U_C ⊇ C` of `E` with
   `U_W ∩ F = U_C ∩ F = U`. The integral closure `D` of `U` in `E` is a nonzero domain integral
   over `U` ([lem-per-valuation-normalization-localizations]), local by
   [lem-trf-integral-component-henselian-permanence], so the converse clause of the normalization
   lemma forces `U_W = D = U_C`. Thus the nontrivial `W` and `C` have a common proper valuation
   overring, and [lem-per-valuation-topology-common-coarsening] gives equality of their
   topologies on `E`. No completeness or rank restriction is used.
-/
theorem henselian_finite_extension_topology
    (F : Type u) (E : Type v) [Field F] [Field E] [Algebra F E]
    [FiniteDimensional F E] (Γ : Type w) [LinearOrderedCommGroupWithZero Γ]
    (vF : Valuation F Γ) [vF.IsNontrivial] [HenselianLocalRing vF.valuationSubring] :
    ∃ W : ValuationSubring E,
      W.comap (algebraMap F E) = vF.valuationSubring ∧
      (∀ W' : ValuationSubring E,
        W'.comap (algebraMap F E) = vF.valuationSubring → W' = W) ∧
      HenselianLocalRing W ∧
      TopologicalSpace.induced (algebraMap F E) W.valuation.subgroups_basis.topology =
        vF.subgroups_basis.topology ∧
      (Algebra.IsSeparable F E → ∀ U : ValuationSubring E,
        TopologicalSpace.induced (algebraMap F E) U.valuation.subgroups_basis.topology =
          vF.subgroups_basis.topology →
        U.valuation.subgroups_basis.topology = W.valuation.subgroups_basis.topology) := by
  sorry

end Valuation
