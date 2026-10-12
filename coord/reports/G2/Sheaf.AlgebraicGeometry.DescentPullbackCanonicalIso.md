## What changed

Proved `AlgebraicGeometry.descent_pullback_canonical_iso` in
`Sheaf.AlgebraicGeometry.DescentPullbackCanonicalIso`, without changing its statement,
universes or visibility. The conservative command-scope check is documented in
`coord/changes/descent-pullback-private-proof-helpers.md`; no interface adaptation is
needed. Added a proof-only import of
`Sheaf.AlgebraicGeometry.DescentPullbackConstruction` and proved private helpers for
point projection, transport congruence, the comparison morphism and its inverse,
naturality, and composition of base-change transport.

The pullback construction is already proved. Its functor and projections are selected
from that proved result; no object is selected from an unproved existence theorem.
Comparisons are actual pullback lifts. The inverse and compatibility use the cocycle
and identity transport laws. Composition pastes pullback squares and compares the
direct and iterated pullbacks for the same map. Updated the original node's proof,
proof dependencies and proof origin to reflect this argument. No unit statement or
unit step is bypassed (`sk-prop-h2.realized` has no nodes for this item).

Read Stacks Tag 023Y directly online: its part (2) constructs precisely the transport
comparison, leaving the compatibility verification to the reader; that verification
is fully written in Lean here. Searches with the required msearch tools found the
Mathlib pseudofunctor comparisons, which use a different descent-data encoding, and
no exact transport-form comparison. Repository search found the existing proved
pullback construction, so no construction was restated.

The only linter setting is scoped to the existing public theorem: unused-variable
lint is disabled there because its unchanged signature names the proof argument
`hr` in the type of `pull` without referencing it in that function's result type.
All private helpers compile with lint enabled.

## Proved and sorry left

Closed the original one hole:
`AlgebraicGeometry.descent_pullback_canonical_iso`
(node `lem-galois-fpqc-pullback-canonical-iso`).

No sorry remains in the item and no sorry was added. This is a complete proof,
not a decomposition. Single-file compilation passes; `#print axioms` for the
public theorem reports exactly `propext`, `Classical.choice`, and `Quot.sound`.
All four clauses of the unchanged statement, including both canonical component
equations, are proved.

## No longer needed

Removed the redundant proof-only import
`WeilConjectures.CategoryTheory.Comma.Over.DescentDatum`: the definitions are already
publicly available through the existing category dependency. No DAG node is removed:
`def-pd-descent-datum` and `def-pc-fibre-product` are both used by the direct proof.
An experimental direct import of the Mathlib pullback-square Basic module was also
removed after verifying those APIs are already available.

The theorem `CategoryTheory.fpqc_singleton_pullback_fullyFaithful` is not used by this
proof. Its existing public module import is retained to preserve the established
public interface; it provides the category in the statement through its public
re-export. Thus no module is claimed pruned from the targets' import closure.
No other nodes, lemmas or modules in the original three-step plan are unused.

## Where the brief, the DAG or earlier work was wrong

The construction now exists and is fully proved in
`Sheaf.AlgebraicGeometry.DescentPullbackConstruction`; the original node predates
that result and did not list it as a proof dependency. Reusing it avoids rebuilding
the pullback functor here. The local literature copy is absent, so the cited source
was read at https://stacks.math.columbia.edu/tag/023Y. No mathematical statement
error was found. No statement or definition was changed, and no forced adaptation
was necessary.

## Second reading by G2

1. Interface: PASS. Compared the entire delivered module with the repository
   using `diff -u`, then compared the existing theorem signature byte for byte
   in Python. Its hypotheses, conclusions, universes and public visibility are
   identical. The only additional declarations are proved private helpers.
   The existing public import is unchanged; the new construction import is
   proof-only. The closed section and theorem-local linter setting have the
   supplied change record and introduce no downstream interface change.
2. Proof: PASS. Independently compiled the delivered file through lcompile.py
   (3.9 seconds, no errors or warnings). Scanned the text: no sorry, axiom,
   unsafe, opaque, implemented_by, extern or explicit sorryAx. Compiled a
   scratch copy with #print axioms for both the public theorem and the
   construction theorem: each uses exactly propext, Classical.choice and
   Quot.sound. Read every helper and the final proof. Projection equations
   establish descent compatibility, inverse identities, naturality and both
   canonical component formulas. All data choices come from proved theorems;
   comparison maps themselves are pullback lifts, not arbitrary witnesses.
3. Split statements: PASS, none added and no remaining holes. The private
   pullback_exists lemma is proved from the existing construction, not a new
   open restatement. Checked equal-map comparisons: transport_self gives the
   projection-preserving identity; reverse transport reduces to identity by
   transport_transport. Identity and empty-base cases require no extra
   assumption, since the argument uses only pullback universal properties.
4. Route and pruning: PASS. Read Stacks Tag 023Y(1)--(2) independently at
   https://stacks.math.columbia.edu/tag/023Y. The comparison is exactly its
   transported universal point, with the omitted checks proved here. Repeated
   leanfinder, loogle and grep searches with different queries and inspected
   Mathlib's pullFunctorIso and pullFunctorCompIso: these require the distinct
   pseudofunctor encoding and do not shorten this transport-form argument.
   Repository search confirms the existing construction is reused. The
   removed DescentDatum import is redundant; the retained public singleton
   import supplies the statement's category through its public re-export.
   Every old proof dependency is still used and No longer needed is complete.
   Read sk-prop-h2.json: its realized statement and step lists are empty, and
   this proof bypasses no realized unit step. No module is claimed pruned.
5. DAG: PASS. Compared the node JSON files: only proof, proof_deps and
   proof_origin change. The new construction dependency and four written
   proof steps match the Lean construction, cocycle/inverse verification,
   naturality and pasted-square composition argument. Their dependency union
   is exactly proof_deps. No new node, statement change or forced adaptation.

Second reading changed only this report by adding the independent review and
verification evidence. No mathematical or Lean repair was necessary. Closed:
AlgebraicGeometry.descent_pullback_canonical_iso (one original hole). Added:
none. No sorry remains in the delivered module.
