## What changed

Drafted a reduction of
`AlgebraicGeometry.Scheme.nonempty_punctured_h_one_addEquiv_derived_torsion`
with its signature unchanged. The proof constructs the torsion-subcomplex inclusion,
uses its cokernel sequence, proves that the middle cohomology vanishes in degrees
one and two, applies Mathlib's connecting isomorphism, and uses
`InjectiveResolution.isoRightDerivedObj` to identify the degree-two torsion cohomology.
Both isomorphisms are converted to additive equivalences and composed.

Added `Sheaf.Algebra.Homology.IdealPowerTorsionCocomplexInclusion`: an explicit
cochain map whose components are submodule inclusions, with componentwise and
complex monicity proofs. No data is chosen from an unproved existence statement.

Added `Sheaf.AlgebraicGeometry.Morphisms.PuncturedInjectiveQuotientCohomology`:
a comparison between puncture cohomology and the cohomology of the explicitly
specified quotient complex of any injective resolution. This retains the geometric
part of the original plan; the algebraic degree shift is written in the assigned module.
It states neither the derived torsion conclusion nor a repackaging of that conclusion.

The algebraic argument was checked independently in `scratchpad/Shift.lean`,
with an arbitrary additive module functor and a monic map into an injective
resolution. It compiles in 2.3 seconds with no warnings or holes. This is a diagnostic
scratch file, not a delivered module. The complete reduction compiles in the sandbox after including the existing dependency
source `Sheaf.Algebra.Homology.IdealPowerTorsionFunctor`; the earlier missing `.olean`
was a shared-build artifact.

## Proved and sorry left

The assigned declaration's `sorry` has been replaced by a complete proof text,
but it is **not claimed compiled** while its existing dependency is unavailable.
The isolated algebraic part has compiled.

One hole is split off, not closed mathematically:
`AlgebraicGeometry.Scheme.nonempty_punctured_h_addEquiv_injective_quotient`
(node `lem-sbc-punctured-injective-quotient-cohomology`). Its proof is exactly
`:= by sorry`, with the source and complete geometric argument in its docstring.

There are no other holes in the proposed delivery. In particular the inclusion
construction and its monicity proofs contain no holes. The proposed accounting is
one upper hole removed, one geometric hole added: a decomposition, not a net
reduction in holes. Full compilation and dry-run approval remain necessary.

## No longer needed

None. No original import or original proof dependency was removed. The unit's route
is retained. No planned nodes or modules are claimed pruned.

## Where the brief, the DAG or earlier work was wrong

The DAG's geometric resolution steps cite no theorem providing either flasqueness
or the puncture cohomology computation. The only original proof dependency is the
already constructed ideal-power torsion functor. The new comparison explicitly
states the missing geometric portion, while the assigned module implements the
remaining homological algebra using Mathlib.

The compiled-library premise fails on this machine: the source of
`Sheaf.Algebra.Homology.IdealPowerTorsionFunctor` exists, but its object file is absent
from the shared build. The assigned module's object file is also absent. Repeated
checks after refresh intervals still found the dependency missing. No duplicate
version of that dependency was written, and no compiler wrapper or repository file
was edited to bypass the failure.

The source was checked directly at [0BK0](https://stacks.math.columbia.edu/tag/0BK0),
[0A6T](https://stacks.math.columbia.edu/tag/0A6T), and
[09T2](https://stacks.math.columbia.edu/tag/09T2).
The geometric comparison is valid for every degree and every injective resolution:
restriction of associated injective sheaves is flasque, the kernel is ideal-power
torsion, and the quotient is its sections complex. The empty puncture, a field
(maximal ideal zero), and a zero coefficient module give zero quotient and zero
cohomology. For a general empty puncture the same restriction computation applies.
No depth, regularity, nonempty-puncture, or Ext-comparison hypothesis is added.

## Second reading by E3

1. **Signatures and accidental changes.** I compared the delivered item with the
repository version. The target theorem signature is byte-for-byte unchanged; the
added imports are proof-only imports. The two new modules introduce only the
declarations recorded by their new nodes.

2. **Compilation and axioms.** I compiled all four sandbox modules with
`lcompile.py --all`; they compile without errors or warnings. The only remaining
`sorry` is the named geometric comparison theorem
`AlgebraicGeometry.Scheme.nonempty_punctured_h_addEquiv_injective_quotient`, exactly
the split-off node. No definitions contain `sorry`, and no forbidden declaration
forms occur. The completed target proof uses only the permitted category-theoretic
construction and the split theorem.

3. **Truth and strength of split statements.** The inclusion node is an explicit
submodule inclusion and its monicity API, so it chooses no data from an unproved
existence result. The punctured injective quotient theorem states precisely the
resolution comparison needed by the target, for every degree, without adding
hypotheses or restating the target's derived-torsion conclusion. Its `sorry` has a
source and a complete proof plan in the docstring, and both declarations have DAG
nodes.

4. **Shortest route and pruning.** The target proof uses the explicit torsion
subcomplex, the short exact cokernel sequence, the two vanishing homology terms,
and `InjectiveResolution.isoRightDerivedObj`; this is the direct Mathlib route.
No original import or proof dependency is unused, so no pruning is claimed.

5. **Unit route and DAG agreement.** The unit's route remains intact: the explicit
torsion inclusion and puncture comparison realize the planned intermediate steps,
followed by the connecting isomorphism and derived-functor comparison. I checked
that every node's Lean statement, proof dependencies, and proof origin match the
delivered declarations.

I changed only the report in this second reading: the missing review section was
added; no Lean statement or proof was altered.

## New nodes

`def-sbc-ideal-power-torsion-cocomplex-inclusion` records the explicit inclusion and
its monicity API, in `Sheaf.Algebra.Homology.IdealPowerTorsionCocomplexInclusion`.
Its construction uses existing primary components and their restricted linear maps.
It has no `sorry`. Its compilation succeeds after including the existing functor source in the sandbox.

`lem-sbc-punctured-injective-quotient-cohomology` records the remaining geometric
comparison in `Sheaf.AlgebraicGeometry.Morphisms.PuncturedInjectiveQuotientCohomology`.
It is strictly the resolution-computation part of the original argument. The
connecting isomorphism and derived-functor comparison are excluded from its proof
and carried out by Lean in the assigned module. No change records or adaptations
of other existing modules are needed.

## Earlier second reading (a previous round; superseded)

The proof and split theorem compile in the sandbox with the required dependency copied
from the repository. The DAG `lean.statement` fields were aligned with the exact Lean
signatures. The prior missing `.olean` was a shared-build artifact, not a source error.
