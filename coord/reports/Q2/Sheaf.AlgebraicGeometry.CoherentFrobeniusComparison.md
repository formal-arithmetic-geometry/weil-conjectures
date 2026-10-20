## What changed

Restored `lean/Sheaf/AlgebraicGeometry/CoherentFrobeniusComparison.lean` from
its assigned quarantine archive. Preserved the full signature of
`AlgebraicGeometry.Scheme.Modules.coherent_frobenius_comparison` and all three
public imports. Replaced the use of general coherent Frobenius pullback
naturality by a complete proof of the proper-case identity needed by this theorem.

Private proved helpers transport p-th powers through the existing canonical
structure-section additive equivalences and assemble their natural transformation.
The characteristic-p equation is pulled back from k to global sections on Y;
subsingleton section rings are handled before installing CharP. The adjunction,
hu, the sectionwise power formulas, and map_pow prove the coefficient square.
Cohomology naturality and the existing source and target coherent-power and
structural-pullback comparison squares prove the coherent naturality identity.
K-linearity of b and target semilinearity finish the tensor formula. No arbitrary
existence witness, new public definition, or new assumption is introduced.

Added private proof imports of
`WeilConjectures.AlgebraicGeometry.EtaleStructureSectionsEquiv` and
`Mathlib.Algebra.CharP.Lemmas`. Updated only proof, proof_deps and proof_origin
of `lem-weil-pbc-coherent-frobenius-comparison`; its statement, attachment and
unit route stay intact. No source-library or other group's module is changed.
Change record: `coord/changes/Q2-coherent-frobenius-comparison-rework.md`.

Validation: the cleaned replacement proof compiled in 22.6 seconds without
errors or warnings using lcompile.py. Its
signature matches the archive token for token. Every Lean line is at most 100
characters. Edge cases include p=2, q=0, zero section rings and empty schemes;
no perfectness of either field is used. The tensor equivalence is the supplied b,
identified with structural pullback by hb, not a substitute equivalence.

## Proved and sorry left

This is a quarantined repair with 0 original holes: 0 holes closed, 0 added,
0 split off, and 0 left in the restored module. The replacement proof of
`AlgebraicGeometry.Scheme.Modules.coherent_frobenius_comparison`, including its
private helpers, is complete. There are no declarations left with sorry in this
packet. The theorem still uses the existing declared
`coherentPowerComparison` and `coherentEtaleComparison_pullback` obligations;
this delivery does not claim to close their holes or the whole target closure.

## No longer needed

Removed the private proof import
`Sheaf.AlgebraicGeometry.CoherentFrobeniusPullback` and the corresponding
`new-coherent-frobenius-pullback` proof dependency from this item's node. The
proper-case naturality identity is now proved directly through etale coefficients
and the comparison squares. This is dependency pruning for this proof; the
general module and its declaration are not deleted or claimed globally unused.

No other archived import is removed. No module is withdrawn, no upstream
signature or declaration is removed, and no unit statement or proof step is
bypassed. The canonical section-naturality node is reused rather than duplicated.
The module remains required by its unfinished Artin-Schreier DAG parent, despite
zero current Lean importers. No top-level tool_uses approval is changed.

## Where the brief, the DAG or earlier work was wrong

The rework row preserves a genuine theorem with zero holes; its absence from
lean/ is a quarantine, not a withdrawal. The recorded missing compiled general
Frobenius-pullback module cannot simply be assumed available. Testing its current
source exposed a duplicate resolution-naturality declaration imported from the
Sheaf and source-library presentations. Rather than alter those held modules,
this delivery proves the required special case inside its own proof and removes
that import. No experimental dependency edits are included in the packet.

The former final DAG step cited stronger general naturality than necessary:
proper comparison on both sides and ordinary coefficient naturality suffice.
The revised node records this argument. The current blueprint Artin-Schreier
unit's coherent comparison and field-extension Frobenius step is preserved.

## Second reading by Q2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
