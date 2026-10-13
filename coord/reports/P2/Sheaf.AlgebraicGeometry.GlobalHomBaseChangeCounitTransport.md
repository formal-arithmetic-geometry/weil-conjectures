## What changed

Proved `AlgebraicGeometry.schemeGlobalHom_baseChange_counit_transport` in
`Sheaf.AlgebraicGeometry.GlobalHomBaseChangeCounitTransport` from the new
proof-only import `Sheaf.AlgebraicGeometry.GlobalHomBaseChangeExchange`.
The original signature, visibility, definitions and public import are unchanged.

The private helpers `homMap_comp`, `pullbackMate_naturality`,
`directImage_naturality` and `pullback_naturality` are fully proved. The latter two
use the existing evaluation-mate construction and the pinned tensor-Hom
naturality, respectively. The main proof applies the exchange square, composes
with Hom of the inverse base-change component and the composite of t with e',
uses the counit equation, and finishes by the two proved naturality equations
and scalar-square naturality. Updated the original DAG proof to match this route.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.schemeGlobalHom_baseChange_counit_transport`
(node `lem-sc-global-hom-base-change-counit-transport`). No sorry remains in the
item's module.

Added exactly one hole:
`AlgebraicGeometry.schemeGlobalHom_baseChange_exchange`
(node `lem-sc-global-hom-base-change-exchange`), in its own module.
This is a decomposition: one upper hole closed, one lower hole added, net zero.
The new statement is the unadorned exchange square: it has no E, K, t, e, e',
counit-square hypothesis, invertibility hypothesis, or inverse map. The remaining
naturality, substitution and cancellation are proved Lean code in the item.

Both modules compile with lcompile.py. The exchange statement was checked on
identity squares and zero objects: it reduces to ordinary naturality and the
zero-object map; it does not demand that base change be invertible. General
noninvertible components are retained in both Hom entries.

## No longer needed

None. No import was removed, and no existing proof dependency is bypassed.
The original public import is needed by the unchanged statement, and the new
proof import supplies the exchange square used by the proof. The unit route is
unchanged.

## Where the brief, the DAG or earlier work was wrong

The original proof plan's first step does not have a stated exchange-square
interface: its cited modules construct the maps but do not assert their exchange
identity. This delivery exposes that precise step as one new item and proves the
remaining step rather than moving the whole transport statement to a new name.

LeanSearch was unavailable (Internal Server Error); LeanFinder and the logged
Mathlib grep found no exact theorem. The whole-DAG global-Hom title search and
blueprint searches for global Hom and exchange found no independent statement
of this square.

WANTED: `literature/stacks-project/duality.tex`, Tag 0AA8 final commutative
diagrams, and `literature/stacks-project/cohomology.tex`, Tag 08I3, for
`lem-sc-global-hom-base-change-exchange`. These source files are absent on this
machine. The named source is inherited from the original node, while the
expanded proof sketch and updated proof_origin are explicitly agent-written.
No source download was attempted.

## New nodes

`lem-sc-global-hom-base-change-exchange` states the canonical exchange square
with base change in both Hom entries, before any counit transport or cancellation.
Its module is `Sheaf.AlgebraicGeometry.GlobalHomBaseChangeExchange`, its theorem
is `AlgebraicGeometry.schemeGlobalHom_baseChange_exchange`, and its source is
Tag 0AA8's final diagrams with the pinned evaluation-mate comparisons. The
natural-language proof, actual search results and Lean signature are recorded in
`dag/nodes/sec-picard-framework/lem-sc-global-hom-base-change-exchange.json`.
No interface change or forced adaptation was made; no change record is needed.

## Second reading by P2

1. **Unchanged interface: PASS.** Read the complete repository-to-sandbox diff.
   The existing public theorem signature is byte for byte identical (also checked
   by extracting the text before `:= by`). The public import, visibility, options,
   and all existing definitions are unchanged. The only new item import is plain
   `import`, used only by the proof. The new module has its required public import.
   No change record or forced adaptation is needed.

2. **Proof and axioms: PASS as a decomposition.** Both modules compile locally.
   Read all four private helper proofs and the main proof, including the direction
   of opposite composition and inverse cancellation. Only the named exchange
   theorem contains `sorry`; no forbidden declaration or hollow definition was
   introduced. A scratch copy with `#print axioms` for all five item declarations
   and the exchange theorem compiled: `homMap_comp` uses only `propext`, and the
   generic mate helper uses the three standard axioms. The scheme helpers and
   public theorems additionally use `sorryAx`, from still-open dependencies and
   the reported exchange theorem. No other axiom occurred. The scratch was removed.
   No data are chosen from the new unproved theorem. The reused chosen direct-image
   comparison is fixed by its evaluation-mate equation: putting the test object
   equal to its source and the test map equal to identity determines each component
   through the tensor-Hom bijection. The pinned tensor-Hom, tensor-pullback and Leray
   choices were also read with their representative or derived-unit equations.

3. **Split statement: PASS.** The exchange theorem is the first square in the old
   proof plan, before counit transport, naturality in t and e, or inverse cancellation.
   It is a proper intermediate assertion, not a renaming of the original theorem:
   E, K, t, e, e', the counit equation and IsIso hypothesis are absent. Both paths
   end at Hom(Lg* Rf*M, Rf'* LgX*N), with beta_M contravariant and beta_N covariant.
   For an identity square it is the identity/naturality square after the canonical
   unit identifications; a zero Hom input gives zero maps. A noninvertible beta
   poses no cancellation requirement, since neither side uses its inverse. Read
   the evaluation-mate docstring and node proof against the actual pinned base-change
   counit definition, tensor representative equations, and Leray unit equation.
   Independently read [Tag 0AA8](https://stacks.math.columbia.edu/tag/0AA8) and
   [Tag 08I3](https://stacks.math.columbia.edu/tag/08I3) online. The general exchange
   identity is an agent-written expansion of their comparison construction, not
   the literal proper/affine isomorphism statement of 0AA8. The missing local TeX
   sources are therefore no longer an obstacle to this source reading. Independent
   LeanFinder, Loogle and grep searches with different wording found only generic
   unit/counit identities and adjunction naturality already used here; the queries
   and results were appended to the new node. Closing the remaining square requires
   tensor-composition and Leray coherence, not a quick application of those lemmas.

4. **Route and pruning: PASS.** The main proof completes the old plan's naturality,
   counit substitution and cancellation steps and isolates only the original exchange
   step. Both imports are needed; every old proof dependency remains used, so
   `## No longer needed` is complete. Read `dag/units/sk-thm-picard-duality.json`:
   its `realized` entries are empty, and no existing realizing node or unit step
   is bypassed or changed. No shorter available theorem supplies this square.

5. **Nodes: PASS.** Both Lean signatures match their nodes verbatim; each
   `proof_deps` is exactly the union of the steps' `uses`. The existing node edits
   are confined to proof, proof_deps and proof_origin. The new node has its source,
   proof, searches, status, creation, blueprint, unit/chapter and Lean records.
   The new theorem has its source, blueprint marker and natural-language proof.
   The original four dependencies are retained, with the canonical tensor-Hom
   naturality dependency and the actual exchange-square dependency added.

Second-reading changes: removed the unused local abbreviation `SX`, corrected
indentation and one overlong proof line, and collapsed surplus blank lines.
No proof argument or statement was changed. Added independent search evidence
and this review. Accounting remains one original hole closed, one new hole added,
net zero; no module pruned.
