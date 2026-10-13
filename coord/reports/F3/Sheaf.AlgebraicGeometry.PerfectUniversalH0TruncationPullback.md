## What changed

Replaced the sole sorry in
`AlgebraicGeometry.Scheme.perfect_universalH0_truncation_pullback_isIso` by a compiling
reduction to two structural lemmas. The existing declaration, universes, hypotheses,
conclusion and public imports are unchanged. Added only proof imports to the item:
`Sheaf.AlgebraicGeometry.PerfectUniversalH0LocalChainModel`,
`Sheaf.AlgebraicGeometry.BottomChainModelPullbackTransport`, and
`Sheaf.Topology.SheafIsomorphismLocalOpenCover`.

The private, fully proved `bottom_homologyMap_isIso` uses
`ShortComplex.LeftHomologyMapData.ofZeros` and its homology-map equation to identify the
map on bottom homology with the invertible middle component. The main proof transports
that isomorphism across the supplied local square, chooses an open containing each point
of Y, proves that their supremum is top, and applies open-cover detection. No data definition
or existing interface was changed. Updated the parent DAG proof to this actual reduction.

Both new public lemmas have exactly `:= by sorry`, a source, a complete proof in their
docstring and an individual DAG node. One constructs the source chart and representative;
the other computes the pullback of an already supplied representative. Neither restates
the global theorem. In particular the second has no universal freeness or perfect-object
hypothesis and does not assert the final global isomorphism.

Sources read: Stacks [0BDL](https://stacks.math.columbia.edu/tag/0BDL), matrix-chart proof
and canonical pullback clause; [0BCD](https://stacks.math.columbia.edu/tag/0BCD),
finite-free residue model; [0EWY](https://stacks.math.columbia.edu/tag/0EWY), square
injective map; [06YJ](https://stacks.math.columbia.edu/tag/06YJ), common natural derived
counit; [08DW](https://stacks.math.columbia.edu/tag/08DW), restriction compatibility.
Read the existing finite-free residue model, affine chain representative, flat-complex
comparison, localized perfect-model comparison and open-cover detection interfaces.
The latter perfect-model comparison only supplies object isomorphisms, so it does not
by itself supply the square for the specified arrow required here.

## Proved and sorry left

Closed the item's one hole:
`AlgebraicGeometry.Scheme.perfect_universalH0_truncation_pullback_isIso`
(node `lem-sc-perfect-universal-h0-truncation-pullback`). No sorry remains in that module.
Its private helper `bottom_homologyMap_isIso` is fully proved from Mathlib.

Added two holes:

- `AlgebraicGeometry.Scheme.perfect_universalH0_local_chain_model`
  (node `lem-sc-perfect-universal-h0-local-chain-model`).
- `AlgebraicGeometry.Scheme.bottom_chain_model_pullback_transport`
  (node `lem-sc-bottom-chain-model-pullback-transport`).

This is a decomposition, not a sorry-free proof of the whole argument: one upper hole
closed, two strictly simpler structural holes added, net minus one before any pruning.
All three sandbox modules compile through lcompile.py, including their import order.
The second reading compiled all three modules independently in import order and checked
all four declarations with explicit `#print axioms` in temporary scratch copies.
The private helper uses only `propext`, `Classical.choice`, and `Quot.sound`; the
three public theorems additionally use `sorryAx`. No other axiom was reported.

Edge cases checked mathematically: rank zero gives zero first terms, and the square-matrix
argument applies to the 0-by-0 map; nonreduced bases use the zero-dual-cokernel argument,
not a full-rank direct-summand assertion; empty S gives an empty Y under any k, and the
point-indexed cover proof works with an empty index type; P and Q may have arbitrary
higher terms, since only their incoming and outgoing differentials at zero enter the
proved calculation. The transport lemma must use one natural counit, not independently
chosen existential object isomorphisms. No witness from an unproved mere-existence
theorem is used in a definition; the main proof eliminates existential witnesses only
while proving a proposition.

## No longer needed

No existing imports were removed: all three original public imports are needed by the
unchanged statement. The new proof imports are all used.

The parent's old direct dependencies on
`lem-sc-perfect-finite-free-residue-model`
(`Sheaf.AlgebraicGeometry.PerfectFiniteFreeResidueModel`),
`lem-sc-square-injective-free-map-dual-coker-zero` (Mathlib matrix lemmas), and
`lem-pc-perfect-affine-map-representative`
(`Sheaf.AlgebraicGeometry.PerfectAffineMapRepresentative`) are now needed in the first
new node. `lem-pc-flat-complex-derived-pullback`
(`Sheaf.AlgebraicGeometry.FlatComplexDerivedPullback`) is now needed in the second.
These are moved dependencies, not pruned theory.

`lem-pc-ringed-spaces-derived-pullback-composition`
(`Sheaf.AlgebraicGeometry.DerivedPullbackComposition`) is no longer a direct dependency
of this argument: use the natural open-restriction comparison instead. This does not
claim that the module has become unreachable from every other target route.
The existing open-cover detection node and module remain directly used. No unit
statement or realized unit step was bypassed or changed.

## Where the brief, the DAG or earlier work was wrong

The old DAG plan describes the correct matrix-chart route, but its primitive declarations
do not directly expose either the simultaneous local chain representative with a square
for a, or the natural cohomology square after pullback. In particular, the existing
localized perfect-model theorem's separate object isomorphisms do not imply naturality
for the specified morphism. The new lemmas isolate these missing composites. No existing
statement is disputed and no signature adaptation is needed.

## New nodes

`lem-sc-perfect-universal-h0-local-chain-model`, in
`dag/nodes/sec-abelian-varieties/lem-sc-perfect-universal-h0-local-chain-model.json`,
is stated in `PerfectUniversalH0LocalChainModel.lean`. It packages steps 1 through the
chain-representative part of step 3 of the old plan, with an actual commuting square.

`lem-sc-bottom-chain-model-pullback-transport`, in
`dag/nodes/sec-abelian-varieties/lem-sc-bottom-chain-model-pullback-transport.json`,
is stated in `BottomChainModelPullbackTransport.lean`. It packages termwise pullback and
exact-restriction transport of a supplied local representative. Its conclusion records
zero bottom differentials, the invertible bottom component and the homology square;
the item proves invertibility of that homology map and performs global gluing.

Blueprint searches for lowest cohomology, chain representative and termwise pullback
found no duplicate blueprint node. Mathlib searches are recorded from actual msearch.py
calls; LeanSearch returned Internal Server Error and is recorded as unavailable.
No change record is needed because every existing statement and definition is unchanged.


## Second reading by F3

1. **Visible declarations unchanged — PASS.** Compared the delivered parent module
   against the repository with `diff -u`, and compared its existing theorem signature
   byte for byte through the `:=` delimiter. Its signature, universes, hypotheses,
   conclusion, docstring, namespace, and three public imports are unchanged. There
   are only three new plain proof imports, a private proved helper, and the replacement
   proof. The two other modules are new; no definition or existing interface changes,
   and no change record is required. The existing node changes only `proof`,
   `proof_deps`, and `proof_origin`.

2. **Kernel proof and remaining holes — PASS as decomposition.** Ran `lcompile.py
   --all` on the three delivered modules: all compile without errors or warnings.
   Temporary copies with explicit `#print axioms` verified the parent theorem, the
   private helper, and both split statements. The helper has only the permitted
   three axioms; the other three declarations also have `sorryAx`, as expected for
   open dependencies. There are exactly two textual holes, each the whole proof
   of its public named split theorem. There is no new data definition, forbidden
   declaration, hidden hole, or choice of an arbitrary existence witness in data.
   The parent eliminates the local existential witnesses only to prove `IsIso`.

3. **Split statements — PASS.** Read both statements, docstring proofs, nodes,
   finite-free residue model, affine arrow representative, localized pullback
   model, flat-complex counit, and universe-aware restriction comparison. Checked
   Stacks Tags 0BDL, 0BCD, and 0EWY directly. The local-model statement isolates
   the matrix-chart construction and specified arrow; it does not assert any
   pullback conclusion. The transport statement starts with a supplied model
   and square and requires no universal freeness or perfect-object hypothesis.
   Neither simply renames the item. Rank zero, empty schemes, nonreduced bases,
   and unrestricted higher differentials within the bounded perfect model cause
   no exceptional case. In particular, zero dual cokernel forces each coordinate
   of the first differential to vanish without claiming the kernel inclusion
   splits. Naturality must use a common derived counit, as the docstring requires.
   The target-side localized derived category may be chosen standard internally;
   the transport conclusion itself uses ordinary homology and does not need a
   supplied derived-category instance on every open of Y.

   Repeated independent searches using different words: LeanFinder query
   `bounded finite projective complex base change natural cohomology comparison
   lowest degree` returned group-cohomology tools, not either interface; Loogle
   query `"homologyMap", "IsIso"` returned generic short-complex isomorphism tools;
   msearch grep query `localizedPullback|mapDerivedCategoryFactors|finiteFreeResidueModel`
   and repository `rg` searches found the existing model/comparison ingredients.
   Also inspected `PerfectUniversalLowestCohomologyPullback`,
   `PerfectLowestMatrixClosedLocus`, `PerfectCommonAffineModels`, and
   `SingleComplexBaseChangeCriterion`. Object isomorphisms there do not supply the
   specified-arrow square here. Neither remaining hole has a short direct proof
   from an already stated composite theorem; both need the constructions described
   in their docstrings.

4. **Top-down route and pruning — PASS.** The private helper reduces bottom homology
   directly to Mathlib's `LeftHomologyMapData.ofZeros`; the main theorem conjugates
   this isomorphism by the supplied comparisons and proves the point-indexed cover
   is top before using open-cover detection. All added proof imports are used,
   and all public imports occur in the statements. `No longer needed` accounts
   for all six old direct dependencies: four move into the two structural nodes,
   open-cover detection stays, and composition is replaced by open restriction.
   This is not a claim of a globally unreachable module. Read
   `dag/units/sk-prop-av-cube.json`: its pre-existing `realized.statement` and sole
   `realized.steps` entry are empty. The delivery does not alter them or bypass
   any named realized unit step; it retains the parent's matrix-chart route below
   the unit level. One closed hole and two added holes remain a decomposition,
   not a net proof gain.

5. **DAG matches Lean — PASS.** Checked every node's recorded Lean signature against
   its file, the existing node's field diff, and the equality between each new
   `proof_deps` set and the union of its proof-step `uses`. The parent names exactly
   the two structural lemmas and open-cover detection used in its actual proof;
   its elementary step describes the fully proved Mathlib calculation. New nodes
   include source, complete proof plan, searches, provenance, creation, blueprint,
   chapter, unit, and Lean records. Their sources and proof plans match the two
   named holes, and their statements are strictly parts of the original argument.

Second-reading changes: corrected the stale pending-review sentence in this report,
recorded the explicit axiom checks and independent searches, and appended this review.
No Lean proof, statement, definition, import, or DAG repair was necessary. Temporary
axiom-check source files were removed before the delivery checks.
