## What changed

The unchanged target conjunction is reduced to the existing finite-flat pushforward theorem,
Mathlib local constancy of `f.finrank`, and a strict intermediate about rank on a constant-rank
open. The unit's finite local freeness uses the affine criterion and the free rank-one section module. The only new
module is `Sheaf.AlgebraicGeometry.PushforwardRankOnOpen`; all proof-only imports are plain.

## Proved and sorry left

`AlgebraicGeometry.Scheme.Modules.isFiniteLocallyFree_pushforward_unit` has a complete reduction
and no local `sorry`. It is not axiom-free: its rank-on-open dependency remains open, and the
upstream finite-flat pushforward theorem can also depend on open statements.
The only delivered `sorry` is
`AlgebraicGeometry.Scheme.Modules.isFiniteLocallyFreeOfRank_pushforward_unit_over`, with node
`lem-sc-finite-pushforward-rank-on-open`. Thus one of one original declarations has its local
proof filled, with one strictly smaller intermediate split off; the target is not fully proved.

## No longer needed

Removed direct imports:
`Sheaf.AlgebraicGeometry.FiniteLocallyFreeDegreeLocallyConstant`,
`Sheaf.AlgebraicGeometry.FiniteLocallyFreeStructureSheaf`, and
`WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree`.
The old proof dependencies `def-pc-finite-locally-free`,
`lem-weil-pbc-finite-locally-free-degree-locally-constant`, and `lem-pc-flf-properties` are no
longer used by this proof. Their corresponding modules, where present, are no longer required
on this branch. This is a local dependency pruning, not a claim that other branches cease to
use them. The first worker's new `ExistsLocallyConstantPushforwardRank` module and its proposed
rank node were removed before delivery; the unit helper was inlined using the affine criterion.

## Where the brief, the DAG or earlier work was wrong

The first worker overlooked the already available local constancy of the explicit morphism
rank. Its report inaccurately called the target proved without identifying its remaining
axioms; its dependency union omitted the finite-flat pushforward theorem, and the proposed
rank theorem lacked a declaration docstring. These are repaired. The route changes only below
the unit: `sk-thm-picard-duality` and its `realized` record are untouched, and no realized unit
statement or step is bypassed.

## New nodes

`lem-sc-finite-pushforward-rank-on-open` states exactly that, on an open where `f.finrank = n`,
the structure-sheaf pushforward restricted to that open is finite locally free of rank `n`.
It records the complete affine argument, the required Mathlib search kinds (LeanSearch unavailable), verbatim Lean
signature, source and creation metadata. No statement or definition change record is needed.

## Second reading by K2

1. Compared the original module with the repository by `diff`: its sole declaration signature
   and docstring are byte for byte unchanged. No definition, target statement or public import
   was changed. The new intermediate's statement is strictly part of the rank argument.
2. Compiled both modules in import order with the permitted `lcompile.py` wrapper. There are
   no errors or additional warnings, and the sole `sorry` is in the named intermediate above.
   Checked all delivered declaration axioms using scratch `#print axioms` and delivery probes;
   only standard axioms and the permitted `sorryAx` from open dependencies occur. No forbidden
   declaration mechanism or hollow definition occurs.
3. Checked the intermediate in the identity case (rank one), empty source (rank zero), empty
   base/open (vacuous cover, all ranks), and disconnected bases of varying rank. It is true
   with exactly the needed hypotheses. Its attached docstring gives the complete affine
   proof, including empty and rank-zero cases. LeanSearch was attempted but unavailable (Internal Server Error). LeanFinder, Loogle,
   Mathlib grep and repository
   searches found local constancy and constant-degree pushforward APIs, but no exact over-open
   statement. Reviewed the actual upstream rank and finite-flat pushforward declarations, and verified
   [Stacks 02KB](https://stacks.math.columbia.edu/tag/02KB) and
   [Stacks 04MH](https://stacks.math.columbia.edu/tag/04MH) against the affine argument.
4. Used the affine unit proof, the upstream finite-flat pushforward proof and Mathlib's
   `Scheme.Hom.isLocallyConstant_finrank`; narrowed the remaining hole from the whole
   existential rank clause to restriction on a specified constant-rank open. Removed unused
   imports and listed every old proof dependency no longer used. The unit's existing route
   and `realized` record remain intact.
5. Checked node/Lean agreement: the original node's proof dependency union now includes all
   three used statements. The new node has the complete signature, provenance and searches,
   and its proof describes the intermediate's actual remaining argument.
   LeanSearch unavailability is recorded without a verdict, alongside the successful searches.

Changes by the second reader: replaced the existential-rank split by the smaller rank-on-open
split; inlined the unit helper; corrected imports, dependency unions, node metadata,
proof documentation, pruning list and the report's account of what remains open.
