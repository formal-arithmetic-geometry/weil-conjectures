## What changed

Completed the listed retirement of Sheaf.AlgebraicGeometry.RawModuleScalarSourceFactors.
It is already a declaration-free reexport of the canonical construction. Withdraw it
and replace its source-prefix consumer's import with the historical derived-pullback
compatibility API import. The upstream prefix already supplies the canonical factors.

Also withdraw the unused combined RawModuleScalarPullbackFormulas and the duplicate
RawModuleScalarPullbackAbelianFormula. G2's concurrently landed retirement of the
composite/evaluation/source/target chain already replaced the combined formula's sole
parent by the canonical separate module factorization. Preserve those landed files
and nodes. Set the unused combined node's Lean attachment to null. Attach the abelian
node to its complete upstream theorem and associativity proof; rawAbelianClassMorphism
and the compatibility forget are identity presentations of the same morphisms.

All remaining mathematical parents and the unit route are preserved. No file under
WeilConjectures and no target is edited. Change record:
coord/changes/K4-retire-raw-module-scalar-source-factors.md.

## Proved and sorry left

The assigned item had zero declarations and zero sorries. Holes closed: 0 of 0;
holes added: 0; split off: 0. No sorry remains in the adapted prefix module or
any withdrawn module. This is retirement, not new theorem-hole progress.
The abelian formula remains fully proved as
AlgebraicGeometry.Etale.rawModuleScalar_pullback_abelian_formula upstream.

The prefix and unchanged transitive source-class reexport compile. The final packet
also runs the delivery's compile, axiom and independent-reader preflight checks.

## No longer needed

Withdrawn modules:

- Sheaf.AlgebraicGeometry.RawModuleScalarSourceFactors: declaration-free shim;
  the canonical three source factors remain attached and used upstream.
- Sheaf.AlgebraicGeometry.RawModuleScalarPullbackFormulas: unused conjunction;
  the composite needs only the separate module formula, already proved upstream.
- Sheaf.AlgebraicGeometry.RawModuleScalarPullbackAbelianFormula: duplicate equation;
  its node and canonical proof remain needed by the canonical target formula.

Remove the factor-shim import from the prefix. The other two live importers are
withdrawn. G2 already removed the former evaluation/composite import sites.
The combined formula's private abelian-copy import is removed with the module.
Its old native-class congruence machinery, raw-complex endpoint conversions and
conjunction are unnecessary on the canonical module-only composite route.
The abelian node no longer needs def-sbc-raw-class-native-morphisms as a proof
dependency. That compatibility module remains used elsewhere; no global pruning
of it is claimed. Only the combined formula node becomes unused. No unit step,
canonical factor definition or adopted source declaration is pruned.

## Where the brief, the DAG or earlier work was wrong

The live queue and retire-items table assign a retirement with zero holes. P2 had
already moved the definitions and source-factor node upstream; the remaining task
was removing the shim and migrating consumers.

Import-only migration exposed the existing kernel cost of native raw-class carrier
conversions: even the unmodified evaluation baseline exceeded 60 seconds. Profiling
isolated kernel checking rather than tactic elaboration. The same raw equations
were already proved upstream. G2's landing 20261025T060830-L-2376591 retired that
four-formula chain while this packet was being prepared. This packet was reconciled
against it: it neither restores those withdrawn modules nor overwrites their nodes.
It finishes the remaining factor-shim consumers and prunes the unused conjunction.
No proof is split for compilation and no time limit is raised.

## Second reading by K4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
