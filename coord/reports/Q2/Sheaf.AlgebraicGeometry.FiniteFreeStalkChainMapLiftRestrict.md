## What changed

Replaced the hole in `AlgebraicGeometry.Scheme.Modules.restrict_chainMap_of_stalk_local`
with a proof using two fully proved private helpers: `pullback_triangle` and
`restrict_triangle`. The map on the smaller open is constructed through pullbacks,
using `restrictFunctorIsoPullback` to convert the source and target. Updated the
node proof to record this route. No signatures, definitions, visibility, or imports
changed.

## Proved and sorry left

The candidate closes the only original hole,
`AlgebraicGeometry.Scheme.Modules.restrict_chainMap_of_stalk_local`
(node `lem-pc-finite-free-stalk-chain-map-lift-restrict`), and adds no holes.
Both private helpers and the specialization of the complete statement with the
comparison definition unfolded compile against the existing Mathlib/upstream
snapshot. `#print axioms` for that specialization reports exactly `propext`,
`Classical.choice`, and `Quot.sound`. The module and its source dependency
validate with `lcompile.py --all`; the previously missing `StalkRestrictionComplexIso.olean`
is available after compiling the source dependency.
No missing declaration was recreated, and no dependency was adapted or included in
the delivery.

## No longer needed

No imports, nodes, or modules are pruned. The proof no longer uses the planned
`restrictFunctorComp` construction or its compatibility with
`restrictFunctorIsoPullback`; instead, all coherence comes directly from
`pseudofunctor_associativity`. The two recorded dependencies remain necessary.

## Where the brief, the DAG or earlier work was wrong

The planned calculation with restriction-composition comparisons was longer than
necessary. Constructing the local map through pullback composition eliminates it.
The statement and its edge cases are unchanged. The unit route is retained.
The comparison-definition dependency was initially absent from the local compiled
snapshot; compiling that existing source module resolved the tool issue.

The delivery dry run passes the compile and preflight checks when run with the
launcher compatibility shim for the repository's missing `refuse_missing` helper;
nothing was pushed.

## Second reading by Q2

1. Compared the complete delivered module with the repository version using diff,
   then checked the existing theorem signature byte for byte through `:= by`.
   Verdict: unchanged statement, docstring, visibility, definitions, and imports;
   only its proof and two fully proved private helpers are added. No change record
   is required.
2. Compiled the module with `lcompile.py --all` and independently compiled a scratch
   copy containing `#print axioms` for `pullback_triangle`, `restrict_triangle`, and
   `AlgebraicGeometry.Scheme.Modules.restrict_chainMap_of_stalk_local`.
   Verdict: all compile without warnings; each uses exactly `propext`,
   `Classical.choice`, and `Quot.sound`. No sorry, forbidden declaration, or hollow
   definition occurs in the delivered module. The smaller-open map is explicitly
   constructed by functorial images and conjugation, with no existence witness choice.
3. No statements were split off and no holes were added. Read both private helpers:
   the first is pullback associativity with transport, the second is its termwise
   lift combined with naturality and cancellation. The latter constructs a map
   using strictly the given scheme morphisms and equalities. Verdict: both are
   fully proved, with no finiteness or boundedness assumptions. For V=U and zero
   complexes, the same isomorphism cancellations apply; an empty neighbourhood
   cannot satisfy point membership.
4. Searched the library by pullback coherence and restriction-to-pullback names,
   inspected Mathlib's `pseudofunctor_associativity`, and ran a new Loogle query
   `"pullbackComp", "hom", "inv"` via msearch. The library's similar
   `compOfEq_assoc` helper is private to EtaleGeneratorsPullbackTargetComparison;
   the Loogle result concerns sheaves on over-sites, not scheme modules.
   Verdict: the direct associativity proof is appropriate. The sole public import
   is required by the theorem's signature. Both old proof dependencies are used,
   so the no-longer-needed list is complete (none). Read the unit record:
   its realized arrays are empty and unchanged; this local restriction argument
   retains the perfect-locus unit route. The referenced blueprint section source
   is not present on this machine; the unit's statement and steps are recorded
   in full in its JSON and were reviewed there.
5. Compared the node with its repository version and traced its proof step against
   the Lean construction, termwise triangle, naturality, and final specialization.
   Verdict: proof, proof_deps, and proof_origin agree with the implementation;
   statement and lean signature agree with the unchanged theorem. No new nodes
   are needed for fully proved private proof helpers.

Second reading changed the report only; the Lean proof and node route were correct.
The original docstring records the longer restriction-functor route; the implemented
shorter pullback route is documented in the node and this report.
