## What changed

Checked the assigned rework item against the current library and retained its complete
proof. In the private theorem `refine_residue_model`, replaced the hand-written
coproduct-comparison composite by Mathlib's `SheafOfModules.mapFreeIso`, using
`overMapUnitIso` to identify the restricted structure module. This constructs the
same required free-rank isomorphisms in every integer degree. Removed the redundant
private import `Mathlib.AlgebraicGeometry.AffineScheme`.

The node's third proof step and proof-origin explanation now describe this explicit
restriction proof. Its statement, dependencies, Lean attachment and unit route are
unchanged. Every public declaration signature and public import is verbatim. There
are no definition changes, source-library edits, new nodes or consumer adaptations.
The maintainer's independent review supplies the independent reader check.

Validation: the unmodified baseline compiled with `lcompile.py` in 22.3 seconds;
the revised module compiled in 31.3 seconds, without errors or warnings. All compilation
used the prescribed server workflow. LeanFinder, Loogle and grep searches were run
with `msearch.py` and recorded in `searches.jsonl`. They found no shorter geometric
theorem; the Mathlib free-sheaf search found the proved `mapFreeIso` API now used.

## Proved and sorry left

The current item already has zero holes. Its public theorem
`AlgebraicGeometry.Scheme.picard_h1_common_minimal_model` and the private proved
helpers `invertible_directImage_isPerfect` and `refine_residue_model` retain complete
proofs from existing declarations. Closed: 0 of 0. Added: 0. Remaining in the delivered
module: 0. No statement is split off. This is proof maintenance and import pruning,
not a claim of new hole closure or an audit of the axioms of the imported library.

The retained argument handles `n = 0` by the finite infimum being top and `m = 0`
by the unique empty coordinate function. Restriction retains boundedness and the
term-rank isomorphisms in all degrees, and its derived comparison has the same source
and target as before.

## No longer needed

Removed only the private direct import `Mathlib.AlgebraicGeometry.AffineScheme`;
its affine-neighbourhood theorem is already available through the existing public
import closure. Its module is not claimed to be globally pruned. The manually
assembled `sigmaComparison`/`Sigma.mapIso` expression is replaced by `mapFreeIso`.
All mathematical proof dependencies listed by the node are still used. No DAG node,
Sheaf module or source-library declaration is withdrawn or pruned from the targets.

## Where the brief, the DAG or earlier work was wrong

The assignment's rework row predates an already-landed repair. The current source
contains S2's explicit universe arguments on `overMap`, `overFunctor` and
`overFunctorMap`; `coord/ledger.md` records that repair at 2026-10-21 22:52. Thus the
initial compiler run succeeds, and restoring the archive or claiming a fresh
universe repair would be inaccurate. This delivery preserves that repair and makes
the concrete proof simplification and import removal described above. No false
statement, hollow definition or mathematical route defect was found.

## Second reading by G3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
