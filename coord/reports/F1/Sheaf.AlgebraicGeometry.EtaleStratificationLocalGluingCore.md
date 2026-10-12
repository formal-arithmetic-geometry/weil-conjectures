## What changed

Proved `AlgebraicGeometry.Scheme.exists_global_stratification_factoring_local` in
`Sheaf.AlgebraicGeometry.EtaleStratificationLocalGluingCore`, without changing its signature
or public imports. No new modules or declarations.

The proof orders the charts. For each local stratum in chart a it removes all earlier
charts by pulling back the closed subscheme on their open union's complement. These
pullbacks are immersed in X and their first projections give actual factorization maps
into the local representatives. Their images are constructible, pairwise disjoint, and
cover X: every point belongs to its least containing chart and then to a local stratum.
The finite dependent sum of local indices is reindexed using `Fintype.equivFin`.
The DAG proof, dependencies and proof origin now record this construction. The existing
declaration docstring retains the earlier proof plan; the node gives the implemented route.

Lean Finder found affine cover/refinement tools but no finite immersed partition theorem;
Loogle had no hit for `Topology.Stratification`. The grep search confirmed the Mathlib
constructible open-image, closed-subscheme image, and pullback image lemmas. The source
refinement module was read: its existing `Scheme.Stratification.exists_refines` acts on
global stratifications and uses a different structure. The direct construction avoids
both the conversion and repeated intersections.

Local compilation passed without warnings (2.4 seconds). The delivery dry run passed the
axiom probe, independent server compile and static preflight. Its only pending check is
the second reading, which the next worker supplies; nothing was pushed. Mathematical edge cases are covered in
the proof: empty base, zero charts, empty local index sets, repeated charts and empty
pieces need no special hypotheses. The factorization equality is `rfl`.

## Proved and sorry left

Proved `AlgebraicGeometry.Scheme.exists_global_stratification_factoring_local`
(node `lem-weil-pbc-etale-stratification-local-gluing-core`): one of one original sorries.
No sorry remains in the module, and none was added elsewhere. No intermediate theorem
was split off.

## No longer needed

No base import was removed; all three existing public imports retain the interface and
supply the stratification, quasi-separatedness and constructibility declarations used
by the statement and proof. Trial proof imports
`Mathlib.AlgebraicGeometry.PullbackCarrier` and
`Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion` were removed after a clean compile:
the existing imports already expose every required Mathlib declaration.

The following original proof dependencies are unnecessary for this theorem:

- `lemma-constructible-common-refinement`, module
  `WeilConjectures.ConstructibleSheaf.Refinement`: the ordered pieces already form a partition.
- `lem-weil-pbc-constructible-in-retrocompact-open`, module
  `Sheaf.Topology.ConstructibleInConstructible`: the special open-image result
  `lem-weil-pbc-constructible-image-retrocompact-open` is exactly what is needed.
- `lem-weil-pbc-qcqs-scheme-spectral`: compact affine opens and quasi-separatedness suffice.
- `def-weil-spectral-space`, module `Mathlib.Topology.Spectral.Basic`: no spectral-space
  construction is needed.

These are pruned from this node's proof dependencies, not claimed globally unreachable:
other targets or nodes may still use them. No UNIT statement or realized proof step is
bypassed; this core is below the unit level of `sk-thm-p1`.

## Where the brief, the DAG or earlier work was wrong

The original plan was mathematically viable but unnecessarily long. Ordered chart
subtraction removes the need to extend every partition, iterate common refinements,
discard empty parts and then choose charts for those parts. The partition structure
allows empty strata, so retaining them is sufficient. No statement correction was needed.

The repository does not contain the cited Stacks tex files on this machine. The source
was read through the official Stacks pages for Tags 03S0 and 09YD. Tag 03S0 leaves the
locality reduction implicit; the ordered disjointification is our formalized elaboration
of that reduction. The needed scheme and topology lemmas were read in the pinned Mathlib.

## Second reading by F1

1. Interface preservation: PASS. Diffed the sole delivered Lean module against the
   repository version. Only the body replacing the original `sorry` differs; the existing
   theorem signature, declaration docstring, universes, namespace and public imports are
   byte-for-byte unchanged. There are no definition changes, new declarations, adapted
   modules or change records.
2. Proof and trust: PASS. Independently compiled the delivered file locally without errors
   or warnings. A scratch copy with `#print axioms
   AlgebraicGeometry.Scheme.exists_global_stratification_factoring_local` reports precisely
   `propext`, `Classical.choice`, and `Quot.sound`, with no `sorryAx`. Read the whole proof:
   no `sorry`, prohibited declaration or hollow definition occurs. Pullback first projections
   supply the factorization maps, and their required composition equality is definitional.
3. Split statements and edge cases: PASS. No statement is split off and no new node is
   introduced. Checked empty X, zero charts, empty local index sets, repeated charts and empty
   strata: coverage supplies a chart only when a point exists; the least containing chart
   avoids earlier charts; the finite dependent sum may be empty; empty pieces are allowed by
   the actual partition structure. No nonemptiness or reducedness of local representatives
   is assumed. Independently searched with msearch grep for `finite partition affine open
   cover immersion` and with local rg for global stratification and refinement declarations.
   Read the existing common-refinement result: it starts with global stratifications and
   does not provide this affine-local factorization construction.
4. Route and pruning: PASS. Ordered chart subtraction directly gives the required partition;
   a conversion to the existing global common-refinement structure would add unnecessary
   work. Read the actual partition structure and the Mathlib constructible-image,
   retrocompact-open, immersion-base-change and pullback-image declarations. The imports
   expose notions needed by the unchanged statement; no proof-only public import was added.
   Compared old and new proof dependencies: all four removed nodes appear under
   `## No longer needed`. Read `dag/units/sk-thm-p1.json`, including `realized`: this core is
   below the unit level, and no realized statement or proof step is replaced or bypassed.
5. Node consistency: PASS. Compared the delivered node with the repository node: only
   `proof`, `proof_deps`, and `proof_origin` change. Each step matches the Lean construction;
   the union of step `uses` is exactly `proof_deps`. Checked the retained dependencies'
   Lean/Mathlib matches against the construction, including closed-subscheme existence,
   image of pullback, immersion composition and base change, and constructible open images.
   The node's Lean statement remains identical to the theorem signature. No new-node fields
   are required.

Second reading changed only this report, adding the independent review. The proof and node
needed no repair. Scratch axiom-check material is outside the delivery's lean/ directory.
