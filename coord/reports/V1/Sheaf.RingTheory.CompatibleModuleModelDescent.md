## What changed

The signature and public imports of
`AlgebraicGeometry.exists_eventually_compatible_module_equiv` are unchanged.
Its proof now constructs the coefficient-ring system on the upper tail, proves
its ring-map laws, uses an elementwise colimit criterion, obtains a single-stage
comparison, and proves propagation to every later stage by tensor cancellation
and base change. The private, proved helper `cancel_comparison` handles both
coefficient actions and their scalar towers. A declaration-local linter option
suppresses the unused existential proof binder `hkj₀` in the original unchanged
statement; all delivered files compile without warnings.

Added proof imports:
`Sheaf.RingTheory.TensorTailColimitElementwise` and
`Sheaf.RingTheory.ElementwiseFpModuleEquivDescent`.
The former is proved in this delivery. The latter is the remaining split step.
The item's DAG proof now records the actual construction and these dependencies.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.exists_eventually_compatible_module_equiv`
(node `lem-pc-compatible-module-model-descent`). There are no sorries left in
that module, including its private helper.

Also proved `TensorProduct.tensorTailColimitElementwise`
(node `lem-pc-tensor-tail-colimit-elementwise`), including both representatives
and eventual vanishing for an arbitrary colimit cocone on a prescribed upper
cofinal tail, directly over a preorder.

Added exactly one hole:
`AlgebraicGeometry.exists_stage_equiv_of_elementwise_colimit`
(node `lem-pc-elementwise-fp-module-equiv-descent`), whose proof is exactly
`by sorry` in its own module. It isolates plan step 3 for two fixed finitely
presented modules over an arbitrary raw directed ring system. It has no tensor
model for that system, no auxiliary coefficient rings, and no eventual conclusion.
It does not restate the item: the item's ring-colimit criterion, finite-presentation
instances, changes of coefficient action, tensor transports and propagation are
real Lean proofs surrounding this remaining step.

This is a decomposition: one upper hole closed, one strictly lower hole added,
net zero holes closed. It is not a claim of an axiom-free proof of the item.
All three delivered modules compile locally with `lcompile.py --all`.

The remaining statement was checked on singleton systems (ordinary scalar
extension), zero rings, zero modules and empty finite presentations. No
nontriviality, flatness, injectivity of structure maps or finite presentation
of rings is assumed. Its distinguished index supplies nonemptiness; preorders
are handled by inverse maps between mutually comparable indices. The two module
universes, the ring universe and the index universe are independent.

## No longer needed

Removed the redundant public import `Mathlib.LinearAlgebra.TensorProduct.Tower`
from the new `ElementwiseFpModuleEquivDescent` module: its signature already has
tensor products through `Mathlib.Algebra.Module.FinitePresentation`.

No original imports were removed: all three public Mathlib imports still provide
the unchanged statement's types and structures. No whole module is claimed to
be globally unreachable or pruned.

As direct dependencies of this item's proof, these old planned edges are no
longer needed:

- `lem-weil-pbc-directed-colimit-base-change-elementwise`, module
  `Sheaf.Paper.DirectedColimitBaseChangeElementwise`: the new proved lemma uses
  the same direct-limit argument but handles the specified cocone and the tail
  above k directly. The old module was not imported by this item.
- `lem-weil-pbc-filtered-colimit-modules-criterion`: no categorical module-colimit
  recognition step is needed; the proof constructs the module direct-limit
  equivalence explicitly.
- `lem-pc-fp-module-map-descent-affine`, module
  `Sheaf.Algebra.FinitePresentationColimit`, is no longer a direct dependency
  of the item. It remains a planned dependency of the new lower descent node,
  so it is moved downward rather than globally pruned.

`lem-pc-fp-module-base-change` remains used through Mathlib's finite-presentation
instances. No blueprint unit statement or realized proof step was bypassed;
this is below-unit work, and the unit's `realized` lists are empty on the base.

## Where the brief, the DAG or earlier work was wrong

No false statement or mathematical source error was found. The named existing
map-descent theorem has a narrower formal interface: a partial order, the
canonical categorical colimit, and module universes containing its ring universe.
It cannot directly instantiate this item's preorder, arbitrary cocone and
independent tensor universes. The new lower statement documents the poset
reflection and universe transport still needed to use that interface, as well
as the two inverse identities. This is an interface/glue split, not a claim that
an unproved dependency prevents use of the stage-3 plan.

The existing tensor-colimit proof supplied the shorter direct-limit route for
step 1. Its Mathlib ingredients were reused directly and its argument generalized
in the sandbox; the existing module was not adapted.

The local path named by the sources, `literature/stacks-project/algebra.tex`,
is absent on this machine. The source statements were read at
[Stacks 05N7](https://stacks.math.columbia.edu/tag/05N7),
[Stacks 00DD](https://stacks.math.columbia.edu/tag/00DD), and
[Stacks 02JO](https://stacks.math.columbia.edu/tag/02JO).
The new nodes record real LeanSearch, LeanFinder and source-grep searches through
`msearch.py`; LeanSearch was unavailable with an Internal Server Error. LeanFinder
and grep found component lemmas but no exact raw-system isomorphism-descent theorem.
Whole-blueprint searches for module equivalence and tensor colimit found no match.

## New nodes

`lem-pc-tensor-tail-colimit-elementwise`:
`lean/Sheaf/RingTheory/TensorTailColimitElementwise.lean`, declaration
`TensorProduct.tensorTailColimitElementwise`. This proved auxiliary statement
supplies plan step 1 over the actual cocone and upper tail. Its proof uses existing
Mathlib-leaf nodes for filtered ring representatives/equality, tensor colimits and module
representatives/eventual zero.

`lem-pc-elementwise-fp-module-equiv-descent`:
`lean/Sheaf/RingTheory/ElementwiseFpModuleEquivDescent.lean`, declaration
`AlgebraicGeometry.exists_stage_equiv_of_elementwise_colimit`. This is the one
remaining hole for plan step 3. Its complete natural-language proof explains
ring-colimit recognition, the poset and universe transport, descent of the two
maps, and descent of their inverse identities.

No definitions or existing statements changed; no change record or forced
adaptation is required.

## Second reading by V1

1. **Existing interfaces — pass.** Read the full three modules and the diff against
   the repository. Independently extracted the entire existing theorem signature,
   from `theorem exists_eventually_compatible_module_equiv` through its conclusion:
   it is byte-for-byte identical. Its public imports and docstring are unchanged.
   There is one new private proved helper, two proof-only imports, and no changed
   definition, target statement, forced adaptation or change record.

2. **Proof and axioms — pass as a decomposition.** All three modules compiled
   cleanly with `lcompile.py --all`. Scratch-copy `#print axioms` checks gave only
   `propext`, `Classical.choice`, `Quot.sound` for
   `TensorProduct.tensorTailColimitElementwise`; the private `cancel_comparison`
   uses only `propext` and `Quot.sound`. The main theorem and the explicitly open
   `exists_stage_equiv_of_elementwise_colimit` additionally use `sorryAx`, as
   declared. The latter is the only delivered sorry and is exactly `:= by sorry`.
   No forbidden declaration, hidden proof hole, hollow definition or arbitrary
   data selected from an unproved existence theorem occurs. Destructuring the
   lower existence statement takes place only inside the main theorem's proof.

3. **Split statement — pass.** Read [Stacks 05N7 (2), (3)](https://stacks.math.columbia.edu/tag/05N7),
   [00DD](https://stacks.math.columbia.edu/tag/00DD), and the final paragraph of
   [02JO (3)](https://stacks.math.columbia.edu/tag/02JO).
   The lower statement fixes two finitely presented modules and concludes at one
   stage: it omits the original item's tensor coefficient-ring construction,
   its two different coefficient actions, and propagation to all later indices.
   Those parts are proved in the main file; this is a strict argument step, not
   relabelling the item. Its representative/zero assumptions yield equality at a
   later common stage by subtracting representatives. Descend the equivalence
   and inverse using 05N7 (2), then descend their inverse identities using (3).
   Finite presentation survives each extension; flatness is unnecessary.
   Checked singleton systems (the hypotheses force the cocone map to be an
   isomorphism), zero modules, zero coefficient rings, and the case C=0 (eventual
   vanishing of 1 forces a zero later ring). For distinct mutually comparable
   indices the system laws make the two transition maps inverse. No hidden
   nonempty assumption is needed because the chosen index supplies it.
   The complete docstring and matching node include universe transport.
   Independent LeanFinder search with “lift an invertible linear map and its
   inverse to a common finite stage”, msearch grep, and source searches for
   isomorphism/equivalence descent found components but no exact replacement.
   Read `FinitePresentationColimit` and `FinitePresentationMapCanonical`: the
   former has a partial-order/canonical-colimit interface and the latter still
   needs a canonical colimit and equal module/ring universes. Closing the raw
   preorder/arbitrary-cocone/universe transport is not a few-minute repair.

4. **Route and pruning — pass after removing one unused import.** Checked the
   tensor representative proof: the upper tail is directed and nonempty;
   `g` is an explicit module-direct-limit map, with injectivity from eventual
   equality and surjectivity by moving representatives above k. Tensoring its
   proved equivalence and applying `directLimitLeft` gives exactly the displayed
   maps; `zero_exact` proves the second clause. In the main proof, `hqC` supplies
   the Q scalar tower, right inclusion supplies the B tower, finite-presentation
   instances apply at k, and tensor cancellation transports both the descended
   comparison and its later base changes. No shorter complete route was found.
   Removed the unused public `TensorProduct.Tower` import in the new lower
   module; no proof-only dependency is publicly imported. The report names all
   three removed old proof-dependency edges, distinguishing the map-descent edge
   moved downward from global pruning. Read `sk-thm-picard-semicon.json`:
   `realized.statement` and its sole `realized.steps` entry are empty, and no
   realized unit statement or route step is removed. No original module pruned.

5. **DAG agreement — pass after citation repair.** Compared the original item
   node with its sandbox version: only `proof`, `proof_deps`, and `proof_origin`
   differ. Its four steps follow the actual Lean constructions and uses. The
   two new nodes have the prescribed source, search, creation, blueprint,
   chapter/unit and verbatim Lean-signature records. In the tensor-tail node,
   replaced the equality-only dependency
   `lem-weil-pbc-filtered-colimit-rings-zero` with the existing Mathlib leaf
   `lem-pc-filtered-colimit-commrings-elementwise`, whose clauses give both
   `Concrete.isColimit_exists_rep` and eventual equality. This corrects the
   missing representative citation without introducing a new node. The module
   and tensor-colimit dependencies otherwise agree with the proof. The lower
   node's two descent steps cite the map and equality clauses of the existing
   finite-presentation descent node, and its base-change step cites the existing
   finite-presentation base-change leaf.

Second reading changed only the redundant import, the tensor-tail node's ring
representative/equality citation and matching dependency list, and this report.
One original hole is closed and one lower hole added: net zero, decomposition.
