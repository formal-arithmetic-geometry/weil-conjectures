## What changed

Replaced the sorry in `AlgebraicGeometry.exists_open_generic_fibre_component_spread`
with a compiling reduction to two geometric shrinking statements. The signature,
visibility, definitions, and target statements are unchanged. The construction is
concrete: `A` is the ambient closure of the image of the chosen fibre component;
its complement component union is closed separately. No data is defined using
an unproved existence statement.

The proof establishes noetherianity and clopenness of the fibre component using
Mathlib and the proved source module `WeilConjectures.Mathlib.Topology.NoetherianSpace`.
It proves both closure traces using the subtype embedding, intersects the two
shrinking neighbourhoods, proves the traces complementary and clopen, and identifies
the chosen trace with `connectedComponentIn`.

Added proof-only imports for Mathlib fibre and noetherian scheme facts, the source
noetherian topology module, and the two new shrinking modules. Updated the item's
DAG proof and dependencies to match. The unit's realized lists are empty; this
refines its slicing/relative-connectedness route without bypassing a unit.

Validated the three modules together with `lcompile.py --all`; the parent theorem
has a complete proof with no local sorry. Sources read: Stacks Tags 055N, 054Y and
054W, including the non-noetherian-base argument of 054Y.

## Proved and sorry left

Closed: `AlgebraicGeometry.exists_open_generic_fibre_component_spread`
(node `lem-sbc-generic-fibre-component-spread`), one original hole.

Added and left:
- `AlgebraicGeometry.exists_open_generic_fibre_closed_cover`
  (node `lem-sbc-generic-fibre-closed-cover-spread`).
- `AlgebraicGeometry.exists_open_generic_fibre_closed_avoidance`
  (node `lem-sbc-generic-fibre-closed-avoidance`).

This is a decomposition, not an unconditional geometric proof: one hole closed,
two strictly smaller holes added. The parent still depends on sorry through these
two public theorems. No other holes were added or changed.

## No longer needed

Removed proof imports:
- `Sheaf.AlgebraicGeometry.GenericFibreComponentSpreadCore`, node
  `lem-sbc-generic-fibre-component-spread-core`.
- `Sheaf.AlgebraicGeometry.GenericFibreComponentSpreadTrace`, nodes
  `lem-sbc-generic-fibre-component-spread-trace` and
  `lem-sbc-generic-fibre-component-spread-trace-reverse`.

None of these declarations is used, directly or transitively through the new proof
imports. This is pruning of the item's route; whether other target paths still
need those modules is for the maintainer's import-closure ledger to determine.
No other module or node in the recorded plan is pruned.

## Where the brief, the DAG or earlier work was wrong

The old core theorem supplies `V = univ` and `A = univ`; this clopenness gives no
control of the chosen fibre component. The earlier trace repair correctly added
membership and preconnectedness assumptions. They cannot be deduced from the core.
The new proof avoids that gap by constructing the component closure and verifying
its trace, rather than identifying an arbitrary clopen trace with the component.

The source-based mathematical statement of the item is unchanged and is not
statement-disputed. The existing node's stale `reviewed_proof.sorry_after = []`
predates the forced reopening; no maintainer-owned field is edited in this delivery.

Edge cases checked for the new statements: empty `C`; empty `D`; empty generic
fibre; a disconnected fibre over a field; and a point `y` closed in `T`. In the
field case covering or avoidance is already global. In the closed-point case an
ambient `V = univ` restricts to the single-point base closure. Both new statements
allow arbitrary closed sets, and impose no noetherianity, flatness, section,
connectedness or nonemptiness assumption. Closed avoidance uses a closed subscheme,
which is finite type even for a non-finitely generated defining ideal. Closed-cover
spreading uses Tag 054Y rather than assuming the open complement is quasi-compact
on an arbitrary non-noetherian base.

## New nodes

`lem-sbc-generic-fibre-closed-cover-spread`:
`Sheaf.AlgebraicGeometry.GenericFibreClosedCoverSpread`, specializing Tag 054Y to
two closed subsets after base change to the reduced closure of `y`. It asserts
coverage only; it does not assert disjointness, clopenness, or a component trace.

`lem-sbc-generic-fibre-closed-avoidance`:
`Sheaf.AlgebraicGeometry.GenericFibreClosedAvoidance`, specializing Tag 054W to a
closed subset after the same base change. It asserts disappearance only; it does
not construct a component or any clopen subset.

Each module has one named public theorem with `:= by sorry`, source, full proof in
words, and blueprint tag. All three required search kinds were run and recorded;
LeanSearch returned an internal server error and is recorded as unavailable.
Searches of the entire imported blueprint for 054Y and 054W found no duplicate.
No change record or forced adaptation is needed.

## Second reading by E2

1. **Interface preservation — pass.** Diffed the delivered parent against the
   repository version. Its declaration signature and visibility, public imports,
   and existing documentation are byte for byte unchanged. Only proof imports and
   the proof body differ. The other two modules and their declarations are new.
   Read the landed trace-repair change record; this delivery repairs the reopened
   parent without changing its interface or adapting any other module.
2. **Kernel checks — pass as a decomposition.** Independently compiled all three
   modules in import order with `lcompile.py --all`, without errors or warnings.
   Compiled scratch copies with `#print axioms` for all three declarations: each
   lists only `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`.
   Text scan finds exactly the two reported named theorem holes, and no prohibited
   declarations or hollow definitions. The closures C and D are concrete; the
   existential neighbourhoods are eliminated only inside a proposition proof.
3. **Split statements — pass.** Read Stacks Tags 054Y, 054W, and 055N independently.
   Base change to the reduced closure of y justifies both statements. A closed
   immersion is finite type without a finite-generation assumption on its ideal.
   For coverage, Tag 054Y avoids the invalid assumption that the open complement
   is quasi-compact over an arbitrary base. Checked empty closed sets, empty fibre,
   a disconnected fibre over a field, and a closed base point. Coverage requires
   neither disjointness nor a component; avoidance requires neither coverage nor
   connectedness, so these are proper parts of the argument, not restatements.
   Repeated LeanFinder, Loogle, and grep searches with different wording and
   searched the upstream and Sheaf sources. No existing theorem closes either
   hole directly. Mathlib's constructible-image theorem requires locally finite
   presentation and a constructible subset, which the present hypotheses do not
   supply. Closing either geometric hole needs substantial further formalization.
4. **Route and pruning — pass.** Read the proof from the component construction
   downward: noetherian fibre, clopen component, exact closure traces, coverage
   and avoidance, then complementary closed traces and the component equality.
   Each proof import supplies an actual geometric or topological ingredient;
   statement imports remain public and new proof imports remain private.
   The report lists both retired imports and all three retired nodes. The old
   node's recorded proof_deps was empty, so no additional old dependency was
   omitted. Read sk-prop-normal-form's realized fields (empty statement list and
   two empty step lists); the slicing and relative-connectedness route is kept.
5. **DAG agreement — pass.** Diffed the parent node: changes are confined to proof,
   proof_deps, and proof_origin. The four steps describe the Lean reduction and
   name exactly the two geometric dependencies. Both new nodes have source,
   self-contained statement, proof in words, search records, split status,
   creation/blueprint/chapter/unit fields and verbatim Lean signatures.

Changed only this report by appending the independent review. No Lean or node
repair was needed. One original hole is closed by reduction and two lower holes
are added: net holes closed is -1 before any import-closure pruning is measured;
this is a decomposition, not a complete proof of the geometric result.
