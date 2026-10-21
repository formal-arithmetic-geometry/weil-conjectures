# AlgebraicGeometry.Scheme.regular_divisor_strict_local_limit

## Reason

Complete the zero-hole retirement listed in `coord/retire-items.tsv`, row 2043,
under the human's 2026-10-20 retirement hand-off. The active Sheaf module duplicates
the proved upstream theorem. Its existential conclusion does not prescribe a
strict-henselization representative: using the upstream full affine-neighbourhood
colimit instead of the small colimit changes no hypothesis or conclusion.

## Old

In `Sheaf.AlgebraicGeometry.Morphisms.RegularDivisorStrictLocalLimit`:

```lean
theorem regular_divisor_strict_local_limit
    (R : CommRingCat.{u}) (g : R) [IsRegularRing R]
    (hg : IsSMulRegular R g) [IsRegularRing (R ⧸ Ideal.span {g})]
    (y : Spec R) (hy : g ∈ y.asIdeal) :
    ∃ (H : CommRingCat.{u}) (ι : R →+* H),
      ι.IndEtale ∧
      ∃ (hH : IsStrictlyHenselianLocalRing H),
        IsRegularLocalRing H ∧ IsRegularLocalRing (H ⧸ Ideal.span {ι g}) ∧
        IsSMulRegular H (ι g) ∧
        ι g ∈ IsLocalRing.maximalIdeal H ∧
        ∃ x : Spec H, (Spec.map (CommRingCat.ofHom ι)) x = y
```

The module also contains the proved private helper `small_regular_divisor_quotient`.
It transports the upstream quotient theorem through the canonical small/full
colimit comparison for the former proof's chosen witness.

## New

Withdraw the Sheaf module through `deleted.txt`; no declarations remain there.
Retain the existing theorem in
`WeilConjectures.AlgebraicGeometry.Morphisms.RegularDivisorStrictLocalLimit`:

```lean
theorem regular_divisor_strict_local_limit
    (R : CommRingCat.{u}) (g : R) [IsRegularRing R]
    (hg : IsSMulRegular R g) [IsRegularRing (R ⧸ Ideal.span {g})]
    (y : Spec R) (hy : g ∈ y.asIdeal) :
    ∃ (H : CommRingCat.{u}) (ι : R →+* H),
      ι.IndEtale ∧
      ∃ (_ : IsStrictlyHenselianLocalRing H),
        IsRegularLocalRing H ∧ IsRegularLocalRing (H ⧸ Ideal.span {ι g}) ∧
        IsSMulRegular H (ι g) ∧
        ι g ∈ IsLocalRing.maximalIdeal H ∧
        ∃ x : Spec H, (Spec.map (CommRingCat.ofHom ι)) x = y
```

The only signature-text difference is the unused existential proof binder name:
`hH` versus `_`. An independent Lean example checks the entire original signature
by applying the upstream theorem. The original universes, regular-ring instances,
nonzerodivisor and point hypotheses, and every existential conclusion are retained.
No statement, definition, attribute, public import, or proof in the adopted source
library is edited. No target definition changes and no target review is reopened.

Reattach the existing mathematical node to this upstream declaration, with its
verbatim signature. Its proof now records the actual full-colimit argument:
strictHenselizationResidue, upstream affine-chart ind-etaleness, the upstream
regular-divisor quotient theorem (at g and at 0), and flat transport of regular
multiplication. The small-colimit comparison, small-model local structure, and
small-model ind-etale dependency are unnecessary for this proof. Their general
statements and modules remain available to their other users.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.Morphisms.RegularDivisorStrictLocalLimit | A2 | Withdraw duplicate and its private transport helper; reattach the mathematical node to the upstream theorem. |
| WeilConjectures.AlgebraicGeometry.Morphisms.RootSplitCoverIndEtaleCharts | unclaimed | Sole current external caller; already imports and applies the retained upstream theorem. No edit required; validation recorded below. |

`tools/downstream.py` finds zero current importers of the Sheaf module. Exact import
and declaration-name scans of both Lean roots and `quarantine/` find no other
caller or archived import. The retirement inventory's Sheaf consumer is already
absent, with no rework row. Its node is attached to the upstream consumer, whose
proof still calls `regular_divisor_strict_local_limit` at R, g, hg, y, hy.

The single DAG parent `lem-sbc-root-split-cover-ind-etale-charts` keeps its
proof dependency and step unchanged: the required result is preserved, not
withdrawn mathematically. The unit `sk-prop-input-spreading` and its source route
are unchanged. No source node, archive, or upstream declaration is deleted.

Edge cases: the theorem retains the arbitrary universe, the prime y, and g ∈ y.
The zero ring has no such point; a unit g cannot lie in y; a regular zero divisor
parameter cannot satisfy these hypotheses in a nonzero ring. No extra restriction
is imposed on R or the residue field. No arbitrary data is selected from an
unproved existence theorem.

Validation: a scratch example at the complete original Sheaf signature applies
the retained theorem successfully. Its axiom report is exactly `propext`,
`Classical.choice`, and `Quot.sound`. The only first-run warning is the original
unused existential binder name. A scoped linter option silences that warning
in the scratch example; the delivered source library remains untouched.
The retained theorem and current consumer are also compiled from unchanged copies
through lcompile.py, with their final results recorded in report.md.

## Status

landed 20261021T161021-L-3955733 2026-10-21 (merge of deliver/A2/Sheaf.AlgebraicGeometry.Morphisms.RegularDivisorStrictLocalLimit)
