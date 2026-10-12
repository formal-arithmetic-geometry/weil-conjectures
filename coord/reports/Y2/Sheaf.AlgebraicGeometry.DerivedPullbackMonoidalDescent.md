## What changed

Replaced the single `sorry` in
`Sheaf.AlgebraicGeometry.DerivedPullbackMonoidalDescent` with a complete proof that
assembles the natural tensor comparison, its associativity, and its unit laws into
`Functor.CoreMonoidal`. The two naturality fields are proved directly from the
naturality of the isomorphism of bifunctors using `NatTrans.congr_app` and component
naturality. The required K-flat equation follows by definitional reduction of the
constructed tensorator. The written theorem signature, its universes, its docstring, and
all existing instance declarations and their bodies are unchanged.

Added the public comparison import and two proof-only coherence imports,
each with one remaining public theorem:
`DerivedPullbackTensorComparisonDescent`, `DerivedPullbackTensorAssociativity`,
and `DerivedPullbackTensorUnit`. These separate the genuinely different tasks of
extending the tensor comparison, checking associativity, and supplying a coherent
unit. The first does not assume an underived monoidal structure or its summand
formula, and asserts no coherence. The other two take the resulting comparison
as an input and prove only their respective coherence statements. Neither is the
original existence of a strong monoidal model under another name.

The comparison module publicly imports Mathlib's multifunctor API because its
statement uses a natural isomorphism between the two curried tensor bifunctors.
It also contains fully defined local wrappers for the same concrete instances
used by the original module. The two coherence modules publicly import that
module for these wrappers and the statement vocabulary; their registrations are
local. The original theorem additionally selects these identical shared wrappers locally,
so applying the new lemmas does not repeatedly compare separate constructions.
This requires the comparison import to be public, as its wrappers occur in implicit
instance arguments of the theorem type. No new global instance is installed. No definition contains `sorry` or
selects arbitrary data from an unproved existence theorem. The original proof
uses existential elimination entirely within a proposition.

Updated the original DAG proof and dependencies to record this assembly, and
created the three matching nodes. All four files compiled without errors or warnings via `lcompile.py --all`:
comparison 20.0 s, associativity 14.0 s, unit 12.5 s, original theorem 40.7 s.
The first two dry runs later timed out on the original file. Selecting the shared
local wrappers before the theorem, while preserving every original instance body,
reduced its next single-file compile to 27.2 s. No time limit was changed and no
proof was split to accommodate the time limit.

The local instance selection and the public import are recorded in
`coord/changes/derived-pullback-descent-shared-comparison-instances.md`.

Final validation of the shared local selection: the entire four-module set compiled
without warnings (comparison 30.4 s, associativity 15.4 s, unit 14.6 s, item 35.9 s).
A scratch theorem with the original signature and only the original local instances
applies the delivered theorem unchanged; it compiled in 32.2 s. Thus the elaborated
interface matches the original, beyond the source-text signature check. The unchanged
`Sheaf.AlgebraicGeometry.DerivedPullbackMonoidalModel` source compiled against the
delivered output in 36.9 s, without adaptation. Scratch sources are under
`scratchpad/consumer/` and are not delivery modules.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.derivedPullback_monoidal_descent`
(node `lem-pc-derived-pullback-monoidal-descent`). No `sorry` remains in the item's
module. This is a decomposition, not a proof free of remaining dependencies:
one upper hole was closed and three strictly smaller holes were added.

The delivery leaves exactly these three new holes, each as a public theorem
whose proof is exactly `:= by sorry`, with source and full proof in words:

- `AlgebraicGeometry.derivedPullback_tensor_comparison_exists`, node
  `lem-pc-derived-pullback-tensor-comparison-descent`, module
  `Sheaf.AlgebraicGeometry.DerivedPullbackTensorComparisonDescent`.
- `AlgebraicGeometry.derivedPullback_tensor_associativity`, node
  `lem-pc-derived-pullback-tensor-associativity`, module
  `Sheaf.AlgebraicGeometry.DerivedPullbackTensorAssociativity`.
- `AlgebraicGeometry.derivedPullback_tensor_unit`, node
  `lem-pc-derived-pullback-tensor-unit`, module
  `Sheaf.AlgebraicGeometry.DerivedPullbackTensorUnit`.

## No longer needed

None. No existing import was removed. The original seven proof dependencies are
retained in the proof plans of the appropriate new nodes, rather than pruned:
`def-pc-derived-pullback`, `def-pc-kflat-complex`,
`def-pc-scheme-derived-tensor-structure`, `def-pc-tensor-complex-sheaves`,
`lem-pc-kflat-pullback-preservation`, `lem-pc-kflat-resolution`, and
`lem-pc-kflat-tensor-product`. The parent's direct proof dependencies now name
only the three statements that its Lean proof actually applies.
No module is claimed to leave the targets' import closure.

## Where the brief, the DAG or earlier work was wrong

The parent proof plan did not provide declarations for extending a comparison
of K-flat representatives to a natural isomorphism, or for either coherence
check. Those are substantial steps: the existing K-flat preservation,
resolution, and tensor-product declarations do not state them. This delivery
makes these steps explicit, preserving the original route.

The existing exact-functor comparison in
`WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Monoidal`
requires preservation of finite limits; arbitrary tensor pullback does not
satisfy that hypothesis. It therefore does not directly close this statement.
Searches of the library, Mathlib, and the imported blueprint found no exact
replacement for any of the three new statements. LeanFinder returned Tor,
projective-resolution, and cartesian-over-category results; grep found no
matching derived comparison/coherence statement. All three LeanSearch requests
were unavailable, and are recorded as unavailable, not as negative results.

Read Stacks `cohomology.tex`, `section-derived-pullback` and
`lemma-pullback-tensor-product` (079U), as well as
`lemma-tensor-product-K-flat` and `lemma-pullback-K-flat`, from the already
installed literature copy under `/home/ubuntu/work-bp/sheaf/literature/`.
Stacks states and proves the K-flat bifunctor comparison. The checks for the
supplied counit and the precise summand-level coherence equations are the
parent's agent-written argument, made explicit in the new docstrings and nodes;
they are not claimed to be verbatim extra clauses in 079U.

The inherited unit is `sk-thm-picard-duality`, whose statement and step records
are unchanged. Its `realized` lists are empty, so there is no separately bound
unit statement or step to bypass here. The inherited blueprint ancestor is
`lem-sc-finite-duality`, through the parent's recorded `blueprint.from` chain.
The generic ancestor command currently prints `None` because the parent's
`created.item` is a module name rather than a node id; the new records preserve
the explicit existing chain instead of inventing a different ancestor.

Edge cases were checked at the level of the argument: identity morphisms,
empty schemes and zero complexes use the same K-flat localization formulas;
no nonzero, flat-morphism, boundedness, or finite-rank assumption is introduced.
The tensor comparison alone may fail coherence without the summand formula,
so that hypothesis is used in the two coherence statements. They assert laws
for an already supplied natural tensor comparison, not existence of the whole
strong monoidal structure. The unit proof does not depend on derived
associativity, and the associativity proof does not require a derived unit.

## New nodes

`lem-pc-derived-pullback-tensor-comparison-descent` is the natural isomorphism
of bifunctors with the prescribed K-flat equation, without associativity or
unit data. It refines parent steps 1 and 2.

`lem-pc-derived-pullback-tensor-associativity` is only the associativity equation
for that natural comparison. The summand formula reduces it to associativity
of the supplied underived structure. It refines the associativity part of
parent step 3.

`lem-pc-derived-pullback-tensor-unit` supplies only a unit isomorphism and the
two unit laws for that comparison, without derived associativity. It refines
the independent unit part of parent step 3.

The public dependency and local instance selection change is recorded in
`coord/changes/derived-pullback-descent-shared-comparison-instances.md`.
There are no changed original definitions, statement corrections, or forced adaptations.

## Second reading by Y2

1. **Interface: pass.** Independently diffed the delivered item against the repository.
   The original theorem signature is byte-for-byte identical. All eight original
   instance declarations, bodies, universes, and visibility remain unchanged. The
   added public import and shared local registrations are declared in the change
   record. Recompiled `DescentOriginalSignatureCheck.lean` with only the original
   registrations: applying the delivered theorem proves the exact original type
   (32.7 s). The new wrappers use the same concrete constructions; their local
   registrations export no global instance. No target or existing definition changes.
2. **Proof and axioms: pass as a decomposition.** Independently compiled the four
   modules in import order with `lcompile.py --all`, without errors or warnings:
   comparison 19.8 s, associativity 16.2 s, unit 12.6 s, item 29.9 s. Read the
   `CoreMonoidal` construction field by field: naturality comes from the supplied
   bifunctor isomorphism, and the computation equation reduces to its component.
   Searched the delivered Lean for forbidden declarations/options and holes: precisely
   the three reported public theorem bodies contain `sorry`; no definition does.
   A scratch import file prints axioms for the parent and all three lower theorems:
   each uses only `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`.
   Existential elimination occurs inside a proposition; no arbitrary witness is
   selected into a new data definition. One original hole closes, three open holes
   are added, so the local net is minus two, not a completed mathematical proof.
3. **Lower statements: pass.** Read all three signatures and docstring arguments.
   Comparison existence omits both coherence conclusions; associativity assumes
   the comparison and proves one law; unit supplies its independent unit comparison
   and two laws. Each is strictly part of the original argument. The supplied
   left-derived counit can differ from the recorded one: uniqueness of derived
   functors transports its K-flat computation, and the same counit is consistently
   used in the comparison and unit construction. The summand hypothesis controls
   all terms of each total tensor map, so it determines the needed underived
   coherence. In the degree-zero identity case, a scalar rescaling of the counit
   rescales the tensor comparison and inversely rescales the unit; the laws still
   hold. Zero complexes and the empty scheme add no nonzero or boundedness
   requirement. The comparison alone need not satisfy coherence, which is exactly
   why the two coherence statements retain `mF` and `hφ`.
   Read the installed Stacks source at `lemma-pullback-tensor-product`,
   `section-derived-pullback`, `lemma-pullback-K-flat`, and
   `lemma-tensor-product-K-flat`. These support the resolving-class argument;
   the supplied-counit coherence checks are explicitly agent-written refinements.
   Repeated LeanFinder searches with localization/flat-object, derived-associator,
   and structure-sheaf/unit vocabulary, and searched repository, upstream, and
   Mathlib localization sources with `rg`. No exact replacement was found.
4. **Shortest route and pruning: pass.** Inspected
   `Localization.Monoidal.curriedTensorPreIsoPost` and
   `Localization.Monoidal.functorCoreMonoidalOfComp`: their localization functor
   must already be strong monoidal. The unrestricted derived localization here is
   only lax monoidal; applying those tools needs a separately constructed K-flat
   monoidal subcategory and its comparison with the recorded derived tensor.
   Also inspected upstream `Functor.OplaxMonoidal.ofLaxSquare` and its coherence
   lemmas. They can shorten later coherence proofs after constructing a monoidal
   complex functor and restricting the counit to K-flat objects, but require
   invertibility of every counit component in their source category. The present
   hypotheses give that on the resolving class, not on all complexes. These are
   useful future proof tools, not exact substitutes for the three lower statements.
   No lower hole can be closed by their direct application in a few minutes.
   The public comparison import is needed by wrapper values in the elaborated
   interface; associativity and unit imports are correctly proof-only. Every old
   direct proof dependency absent from the parent's new direct list is explicitly
   named under `No longer needed` and retained in the lower plans. None is claimed
   pruned from the target closure. Read the inherited unit record: its statement,
   steps, and empty `realized` lists are unchanged; the same ancestor route remains.
5. **DAG agreement: pass.** The parent changes only `proof`, `proof_deps`, and
   `proof_origin`; its three direct dependencies are exactly the three applied
   theorems. Checked each new node's statement against its Lean signature, including
   the dropped comparison-only assumptions and each law's direction. All four
   normalized `lean.statement` strings match their source declarations. Each new
   node has its source, complete proof steps with matching dependency union,
   origin, three search records (service failures recorded as unavailable), status,
   creation record, blueprint ancestry, chapter/unit, and complete Lean record.
   The original seven dependencies are all accounted for across the lower plans.

Second-reading changes: added this independent review and recorded the additional
localization and oplax-square search results and their unmet hypotheses. No Lean
proof, statement, import, definition, or node repair was necessary. Added only the
scratch axiom-check file outside the delivery source tree. The independent review
accepts this as a one-to-three decomposition with no pruning.
