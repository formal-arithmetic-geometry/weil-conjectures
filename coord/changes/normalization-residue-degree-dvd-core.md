# AlgebraicGeometry.Scheme.normalization_residue_degree_dvd_core

## Reason

The old statement is false: G is unrelated to p and a. The existing degree-two/trivial-group
counterexample applies. Moreover a regular Cartier divisor alone does not make its ambient
stalk regular. Tag 09EB instead assumes a genuine Galois extension over a DVR.
Separate the actual Galois arithmetic from the root-chart geometry. The arithmetic now uses
Mathlib's more general finite flat domain identity and a stabilizer subgroup of G. A new
geometric model statement retains all the root-chart hypotheses; its witness is eliminated
only in a theorem proof, never chosen in a definition. This repairs an intermediate statement,
not a Challenge target. The caller's statement, visibility and existing docstring stay identical.

## Old

```lean
theorem normalization_residue_degree_dvd_core
    {N V P D : Scheme.{u}} (G : Type (u + 1)) [Group G] [Finite G]
    (p : P ⟶ V) [IsFinite p] (a : P ⟶ N) [QuasiCompact a] [QuasiSeparated a]
    (hEtale : Etale p) (hNorm : IsFinite a.fromNormalization)
    (j : D ⟶ N) (hD : IsRegular D) (hDi : IsIntegral D)
    (hj : IsEffectiveCartierCenter j)
    (O : N.Opens)
    (hcomp : ∀ z : N, z ∈ O ↔ z ∉ Set.range j)
    (η : D) (hη : IsGenericPoint η Set.univ)
    (x : a.normalization) (hx : a.fromNormalization x = j η) :
    letI := (a.fromNormalization.residueFieldMap x).hom.toAlgebra
    Module.finrank (N.residueField (a.fromNormalization x))
      (a.normalization.residueField x) ∣ Nat.card G
```

## New

```lean
theorem normalization_residue_degree_dvd_core
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    [IsDomain R] [IsDomain S] [Algebra R S] [Module.Finite R S] [Module.Flat R S]
    (G : Type w) [Group G] [Finite G] (T : Subgroup G)
    [MulSemiringAction T S] [IsGaloisGroup T R S]
    (q : Ideal S) [q.IsPrime] : q.inertiaDeg R ∣ Nat.card G
```

The old public imports of Mathlib.AlgebraicGeometry.Normalization,
Mathlib.AlgebraicGeometry.Morphisms.Finite,
WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.EffectiveCartier and
WeilConjectures.AlgebraicGeometry.Regular are removed. The core publicly imports
Mathlib.NumberTheory.RamificationInertia.Galois for its algebraic statement;
Mathlib.GroupTheory.Coset.Card is a private proof-only import used by the proof.
The sole direct importer independently imports its geometric signature dependencies,
so its signature needs no edits.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.Morphisms.NormalizationResidueDegreeDvdCore | K2 | Own corrected intermediate statement; proved without sorry. |
| Sheaf.AlgebraicGeometry.Morphisms.RootNormalizationGenericStalkResidueDegreeDvd | unclaimed | Forced proof adaptation: obtain the local Galois model, install its instances, transport its residue equality, apply the corrected core. Statement and visibility identical. |

The direct-use census is tools/downstream.py with --uses normalization_residue_degree_dvd_core.
No other module mentions the changed declaration. Transitive users retain the root-chart
caller's unchanged interface. Its original last exact application fails against the corrected
core; the adapted proof is checked against the same changed dependency. No extra lines of its
statement or docstring are changed.

## Status

landed 20261014T001725-L-2552030 2026-10-14 (merge of deliver/K2/Sheaf.AlgebraicGeometry.Morphisms.NormalizationResidueDegreeDvdCore)
