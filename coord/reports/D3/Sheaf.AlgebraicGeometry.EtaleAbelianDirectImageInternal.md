## What changed

Proved `AlgebraicGeometry.etaleAbelianDirectImageInternal` without changing its
signature or imports. The proof uses `sheavesAlgebraicStructuresAbelian` at the
two sites, constructs the equivalences using their strict inverse identities,
and constructs the comparison from the underlying isomorphisms. It proves the
product comparison is the identity by its projections, checks zero and addition
on sections, and uses `CommGrp.mkIso'` to lift the comparison. Naturality follows
by faithfulness and the two underlying naturality equations. Cancellation gives
the required displayed equation. Local Lean compilation is clean.

Searches: LeanFinder for internal commutative groups and pushforward returned
sheaf pushforward and module-sheaf comparisons, but no exact result. Loogle for
`CategoryTheory.CommGrp.mkIso` found the constructor used here. The grep search
for sheaf/CommGrp returned unrelated abelian-sheaf modules. Direct source reads
confirmed the constructors and finite-product comparison lemmas.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.etaleAbelianDirectImageInternal`
(node `lem-weil-pbc-etale-abelian-direct-image-internal`). No holes remain in the
item and no holes or declarations were added. This is a proof from the existing
named dependency `CategoryTheory.sheavesAlgebraicStructuresAbelian`, which still
contains its own previously existing sorry; it is not a claim that the full
transitive axiom closure is already sorry-free.

## No longer needed

None. All imports serve the statement, its instances, or the proof. The existing
DAG route is retained: sectionwise abelian identification, continuous direct image,
sectionwise products, and the natural comparison. No unit route is bypassed.
No dependency module is proposed for pruning.

## Where the brief, the DAG or earlier work was wrong

No mathematical error found. The inverse's preservation of operations need not
be checked separately: Mathlib's group-object isomorphism constructor derives it
from the forward monoid-homomorphism check. The local clone lacks the untracked
Stacks source files; the source proof and section formulas already recorded in
the item and its existing dependency were used, with the Mathlib implementation
checked directly. No new source-dependent statement was introduced.

## Second reading by D3

1. Signature safety: PASS. The full module diff changes only the body of
   `AlgebraicGeometry.etaleAbelianDirectImageInternal`. The existing signature,
   docstring, module header and imports are byte-for-byte unchanged. There are
   no added declarations, changed definitions or change records.
2. Proof and axioms: PASS. Compiled the delivered file locally with lcompile.py
   (21.0 seconds, no warnings or errors). A scratch copy with `#print axioms
   AlgebraicGeometry.etaleAbelianDirectImageInternal` compiled in 18.5 seconds
   and reported exactly `propext`, `sorryAx`, `Classical.choice`, `Quot.sound`.
   The previously open sectionwise equivalence dependency accounts for the
   remaining sorryAx; the delivered module contains no sorry and no prohibited
   axiom, unsafe, opaque, implementation override or hollow definition. The
   witnesses are used to prove an existential proposition, not to define data
   by choosing an arbitrary object from an unproved existence assertion.
3. Split-off statements: PASS, vacuous. No statements or holes were added.
   Read the imported sectionwise equivalence and its operation formulas; the
   proof checks zero and addition after cancelling the underlying isomorphism.
   Mathlib's `CommGrp.mkIso'` supplies inverse compatibility. The argument
   imposes no condition on f and also applies to identity maps, empty schemes
   and zero abelian sheaves. No new edge-case-sensitive lemma was introduced.
4. Route and pruning: PASS. Read the related proved
   `sitePullback_abelian_underlying`, and searched the library for the internal
   group/direct-image comparison and Loogle for `Functor.mapCommGrp` (a query
   different from the first reader's). The former contains a similar comparison
   inside an inverse-image proof with extra finite-limit hypotheses, not an
   applicable exported direct-image theorem; the search returned generic lifts,
   not this result. The present proof uses the shortest available sectionwise
   route and existing dependency. All public imports supply statement names or
   required instances (in particular Sites.Adjunction defines sheafForget);
   the equivalence dependency is correctly a plain proof-only import. No old
   proof dependency is unused: continuity and direct image come from the upstream
   Etale definitions, and sectionwise products from Mathlib's sheaf Cartesian
   structure. No modules are pruned. Read sk-def-exchange.json: its realized
   statement nodes are unchanged and no unit route is bypassed.
5. DAG agreement: PASS after clarification. Read the item's node and the
   continuity, objectwise-limit and sectionwise-equivalence dependencies.
   Retained proof_deps and the documentary proof_origin. Refined steps 2 and 3
   to name the actual projection argument proving the multiplication comparison
   is the identity, and the `CommGrp.mkIso'` lifting argument which derives
   inverse compatibility rather than separately checking it.

Second reading changed only the existing node's proof descriptions and this
report. No Lean repair was needed. One original hole closed; zero holes added;
zero split off. The transitive dependency remains open as already reported.
