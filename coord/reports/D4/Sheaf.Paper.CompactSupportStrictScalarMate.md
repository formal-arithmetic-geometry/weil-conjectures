## What changed

Proved `WeilConjectures.PurStrictScalar.factors_isIso` in
`Sheaf.Paper.CompactSupportStrictScalarMate`. It now follows from the existing
`proper_biproduct` and `strictProper_biproduct` identities, the proved open
normalizations, and finite integral and quotient bases. Moved it after those
identities so its proof can use them. Existing public signatures and definitions
are unchanged. Also simplified the two existing private proofs
`restrictionComposite_conservative` and `inverseDoubleMate_isIso`: their previous
whole-functor conversions were the full file's largest elaboration costs.
The new proofs compare underlying sheaf morphisms and use
`conjugateEquiv_symm_iso` directly. Factored the repeated exact-localization
mate calculation into the proved private helper `localizedInverseMate_eq`, used
by both open normalization proofs. Kept chosen comparison isomorphisms and
derived comparison constructions folded using local irreducibility attributes.
The evaluation identity helper now receives the actual section types and their
explicit carrier equality, avoiding repeated comparison of whole module
structures. The two balancing definitions have explicit annotations matching
their inferred result types; their choice expressions are unchanged.

Added proved private helpers for conservativity of exact derived functors,
constant and finite-quotient sheaf bases, and cancellation of the coordinate
isomorphisms in the two proper biproduct identities. Added private proof imports
of `CompletedIntegralFiniteFree`, `ConstantFiniteFreeSectionBasis`, and
`AdicBasisLimit`. Updated Step 4 and its dependencies in the existing node.

Validation: the complete module compiled through `lcompile.py` in 58.7 seconds
in the timing pass, within the 60-second limit. Profiling options were removed
for delivery. Import-direction and node-dependency checks passed.

## Proved and sorry left

Closed one of the six original holes:
`WeilConjectures.PurStrictScalar.factors_isIso`.
No holes were added or split off.

The five unchanged holes, all attached to
`lem-pur-compact-support-strict-scalar-mate`, are:

- `WeilConjectures.PurStrictScalar.finiteOrdinaryBalancing_existsUnique`
- `WeilConjectures.PurStrictScalar.pulledBasis_existsUnique`
- `WeilConjectures.PurStrictScalar.proper_biproduct`
- `WeilConjectures.PurStrictScalar.strictProper_biproduct`
- `WeilConjectures.PurStrictScalar.compactSupportStrictScalarMate`

The proved invertibility theorem still depends on the two named biproduct
identities and the pulled-basis obligation. It does not establish those identities
or the final evaluated-arrow normalization.

## No longer needed

None. No imports, modules, nodes, or unit steps were pruned. The proof implements
the existing finite-basis route, and the other obligations retain their dependencies.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement repair was needed. Exact restriction reflects derived
isomorphisms by homology; this is checked on the full derived tower category,
without inferring whole-tower invertibility from a family of evaluated arrows.
The integral basis descends to each quotient using ideal equality, so no equality
of chosen uniformizers is required. The generic cancellation argument also covers
rank zero and the zero object; quotient bases are used only at positive exponents.

## Second reading by D4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
