## What changed

Replaced the one whole-proof sorry of
`AlgebraicGeometry.Scheme.perfectUniversalLowestCohomology_pullback` by a compiling reduction
of the existing matrix-chart plan. Its signature, universes, public imports and existing
public declarations are unchanged.

The proof obtains local zero-bottom-differential models for `Lh*E`, applies the generic
bottom-cohomology comparison to these models, then maps the existing derived composition
isomorphism `(c g h).app E` through the degree-a homology functor and composes the two
isomorphisms. This last transport is actual Lean, not an assumed identification of endpoints.

Added two separate theorem modules and their nodes. The first isolates the geometric
normal-form argument (original steps 1–2); the second isolates termwise computation and
overlap gluing (original step 3). The original node now records these two dependencies and
the actual composition theorem used in Lean. Neither intermediate restates the target:
the first concludes existence of local chain models and no cohomology comparison;
the second assumes those chain models for an arbitrary derived object, with no perfectness,
Tor-amplitude, rank or universal-freeness hypotheses, and compares successive pullback.

## Proved and sorry left

Closed the item's one textual hole:
`AlgebraicGeometry.Scheme.perfectUniversalLowestCohomology_pullback`
(node `lem-sc-perfect-universal-lowest-cohomology-pullback`). The item has no sorry left.

Added two named whole-theorem holes, each in its own public module:

- `AlgebraicGeometry.Scheme.perfectUniversalLowest_zero_model`
  (`lem-sc-perfect-universal-lowest-zero-model`), in
  `Sheaf.AlgebraicGeometry.PerfectUniversalLowestZeroModel`.
- `AlgebraicGeometry.Scheme.localZeroBottomModel_pullback`
  (`lem-sc-local-zero-bottom-model-pullback`), in
  `Sheaf.AlgebraicGeometry.LocalZeroBottomModelPullback`.

This is a decomposition, not a completed proof without sorry dependencies: one hole closed
and two added, before considering existing dependencies. Existing dependencies remain
unproved where they were already unproved. No definitions or arbitrary data are introduced.
The local model witnesses remain under existential quantifiers in propositions; the proof
introduces no definition choosing a model from the unproved existence statement.

All three modules compile together through lcompile.py. The public signature of the original
theorem was checked against its unchanged source signature. The delivery dry run also checks
all new declarations and their axiom dependencies.

## No longer needed

Removed these direct proof imports from the item:

- `Sheaf.AlgebraicGeometry.PerfectFiniteFreeResidueModel`
- `Sheaf.AlgebraicGeometry.FlatComplexDerivedPullback`
- `Sheaf.AlgebraicGeometry.PerfectJumpLoci`

They are needed by the normal-form or model-comparison steps and now occur in those modules.
Consequently no original node or module is claimed globally pruned. In particular the
square-injective-matrix leaf remains needed by the first new theorem. The item's remaining
original direct proof import, `DerivedPullbackComposition`, is explicitly used.
No unit statement or realized unit step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The existing proof dependencies give a residue model, fibre Betti base change, flat-complex
pullback and composition, but do not directly state the conclusion of the square-kernel
argument on the pulled-back charts, or the descent of the bottom comparison. The two new
interfaces make those missing glue steps explicit. The square matrix result is a Mathlib
composite, not a Sheaf module to import.

Existing `PerfectUniversalH0LocalChainModel` is related but requires a specified truncation
arrow, a perfect object on the current base with localized-site derived instances, and
universal negative vanishing, all in degree zero. It cannot be applied directly to this
arbitrary-degree, pulled-back-object interface. `BottomChainModelPullbackTransport` also
requires that specified arrow and only transports its homology square.
`DerivedOpenPullbackHomology` handles open inclusions, not the arbitrary g in the target.

Checked the sources at Stacks Tags 0BDL, 0BCD and 0EWY. The two new statements retain the
matrix-chart route. Checked empty T and empty source, rank zero, zero complex, a single
finite free module in degree a, identity g, arbitrary a (including negative a), and
nonreduced bases. The square-cokernel argument uses zero dual, not invertibility of the
square injection, and therefore does not assume the base reduced. The Tor interval need
not be ordered: if b<a all fibre terms vanish; on a nonempty T universal freeness forces
r=0. The local-model comparison only needs the displayed lower vanishing and bounded-above
finite free models, not a global bound or separatedness.

Mathlib searches were performed with LeanFinder, Loogle and grep; LeanSearch was tried for
both new statements but returned Internal Server Error. Search results and the precise
unavailability are recorded in the new nodes. Blueprint searches for zero bottom differential
and lowest cohomology pullback gave no duplicate. Generic zero-differential homology lemmas
exist, but no complete scheme-level theorem with either interface was found.

## New nodes

`lem-sc-perfect-universal-lowest-zero-model` records the local normal form under the original
universal-rank hypotheses. Its source is the 0BDL matrix-chart argument, 0BCD residue models,
and 0EWY zero-dual cokernel argument. Its proof includes the Tor-amplitude-to-fibre step and
retains the existing residue, fibre, termwise pullback and composition dependencies.

`lem-sc-local-zero-bottom-model-pullback` records the homological consequence of that model
condition for any derived object. Its source is 0BDL's pullback clause and the flat-complex
counits. Its proof spells out the canonical zero-differential homology identification,
termwise pullback, overlap compatibility via affine chain-map representatives, and sheaf gluing of maps
and inverses. The condition is stated using modules on `U.toScheme`, so it introduces no
additional derived-category instances for localized sites of T or its source.

No existing interface was changed, no adaptation was required, and no change record is needed.

## Second reading by W2

1. **Interface and accidental changes — pass.** Compared the delivered item with the repository version: the theorem signature and all existing declarations are byte-for-byte unchanged. The two additional modules contain only the split interfaces recorded by their nodes.
2. **Compilation and proof hygiene — pass.** Compiled all three modules with `lcompile.py --all`; there are no undeclared `sorry`s outside the two named split theorems, no unsafe or opaque declarations, and no hollow definitions. The item theorem itself is axiom-clean apart from its explicitly imported split theorem holes.
3. **Statements and new nodes — pass.** Checked both split statements against their docstrings, source tags, edge cases (empty schemes, rank zero, arbitrary degree and nonreduced bases), and DAG records. Each is strictly simpler than the item and introduces no arbitrary witness or weakened target.
4. **Pruning and route — pass.** The item uses the zero-model, local pullback, and derived-composition declarations exactly as its proof; removed direct imports are now confined to the split modules. The unit route and realized steps remain intact, and no shorter existing theorem was found by the recorded searches.
5. **DAG agreement — pass.** Verified each node's declaration, statement, proof steps, proof dependencies, source, and `lean` record against the delivered Lean files. The proof dependency graph matches the imports and theorem applications.

I added this second-reading record; no Lean declarations, statements, definitions, or imports were changed during review.
