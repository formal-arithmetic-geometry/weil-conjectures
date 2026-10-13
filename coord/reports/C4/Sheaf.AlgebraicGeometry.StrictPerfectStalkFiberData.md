## What changed

Replaced the sole sorry in
`Sheaf.AlgebraicGeometry.StrictPerfectStalkFiberData` by a complete Lean proof from two
strictly smaller intermediate theorems. All existing signatures, universes, visibility,
public imports and definitions remain identical.

The first new module, `Sheaf.AlgebraicGeometry.LocalStrictPerfectStalkProjectiveModel`,
contains the geometric construction of a bounded finite-projective stalk representative.
It has no residue-field or fibre-finiteness assumptions and asserts no fibre comparison.
The original proof uses its upper bound, converts its projective terms to flat terms by
Mathlib's `Module.Flat.of_projective`, then to free terms with
`Module.free_of_flat_of_isLocalRing`, and constructs the pseudo-coherence witness itself.

The second new module, `Sheaf.AlgebraicGeometry.StalkFreeResidueCohomologyComparison`,
compares the residue homology of an arbitrary bounded-above free stalk representative
with the derived fibre. It does not construct a representative or assert pseudo-coherence,
finiteness, or Betti-number equality. It needs neither hlocal nor hfin and allows infinite-rank
free terms. The original proof extracts the bounds and comparison for `Classical.choose hK`,
applies this equivalence in each degree, transports hfin with `Module.Finite.equiv`, and
proves the Betti equality by `LinearEquiv.finrank_eq`. An explicitly typed local finiteness
instance handles the definitionally equal scheme and ring residue fields.

Both new statements have source references, complete proof arguments in their docstrings,
matching DAG nodes, and proofs exactly `:= by sorry`. The original node's proof and dependencies
now describe the Lean combination. No data definition was introduced or changed.

Validation: all three modules compile in import order through lcompile.py. The final dry run
uses deliver3.py with --no-push; this worker does not deliver. The second reader's section is
intentionally left to the second reader.

## Proved and sorry left

Closed: `AlgebraicGeometry.Scheme.strictPerfect_stalk_fiberData`
(node `lem-sc-strict-perfect-stalk-fiber-data`), 1 of 1 original holes.
There is no sorry left in the assigned module.

Added and left:

- `AlgebraicGeometry.Scheme.exists_localStrictPerfect_stalk_projective_model`
  (node `lem-sc-local-strict-perfect-stalk-projective-model`).
- `AlgebraicGeometry.Scheme.nonempty_stalkFree_residueCohomology_linearEquiv`
  (node `lem-sc-stalk-free-residue-cohomology-comparison`).

This is a decomposition: one upper hole closed and two strictly smaller holes added;
the local net is minus one. Neither helper is the original theorem under a new name.
The first constructs only a projective model; the second computes cohomology of a model
already supplied as input. The conversion to finite-free pseudo-coherence and the transport
of the original two conclusions are proved in the assigned module.

## No longer needed

Removed from the assigned module:

- `Sheaf.Algebra.Homology.ModuleStalkExact`, node `lem-weil-pbc-module-stalk-exact`:
  still needed in the new construction and comparison modules, so relocated, not pruned.
- `Sheaf.Algebra.Homology.BoundedFlatKFlat`, node `lem-pc-module-bounded-flat-kflat`:
  still needed by the new comparison's proof plan, so relocated, not pruned.
- `Sheaf.AlgebraicGeometry.AffineDerivedPullbackModuleModel`,
  node `lem-pc-affine-derived-pullback-module-model`: pruned from this argument.
- `Sheaf.AlgebraicGeometry.DerivedPullbackComposition`,
  node `lem-pc-ringed-spaces-derived-pullback-composition`: pruned from this argument.

The comparison uses K-flat resolutions, K-flatness of stalks, and the direct tensor-pullback
stalk formula (0098). It need not pass through an affine presentation or compose derived
pullbacks. Neither of the pruned modules is imported by a new helper. This is pruning of
this proof route; other paths in the five targets may still need these modules.

The remaining public imports supply the existing signatures and retain their visibility.
The old proof dependencies `def-pc-perfect-complex` and
`def-pc-module-stalk-functor` are no longer direct proof dependencies of the assigned
node: they remain statement dependencies, public imports, and dependencies of the
new construction. They are retained, not pruned. All eight old proof dependencies
are thus accounted for: these two and the two relocated tools remain below the
helpers, pseudo-coherence and fibre Betti remain direct, and the two geometric
comparison modules above are pruned from this route.
The unit record sk-prop-av-cube has no realized entry for this helper; its theorem-of-cube
route is preserved, and no unit statement or step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The original dependency declarations do not directly state either geometric interface:
exact stalks alone do not supply the over-site local strictly perfect representative;
bounded-flat K-flatness alone does not identify its residue homology with the scheme fibre.
The affine model assumes affine source and target and quasi-coherent cohomology, and the
composition declaration requires a derived-category instance for every scheme. Neither
can be applied directly with this theorem's local data. The new comparison uses the
pointwise pullback-stalk formula instead, with no such added hypotheses.

No statement was disputed or corrected. No adapted module or change record is needed.

Mathlib and project search: LeanFinder and Loogle found K-projective, ordinary stalk,
localization and tilde-stalk results, but no theorem with either required signature.
Mathlib's local-ring freeness theorem is reused directly. Searches of all DAG nodes and
blueprint_refs found no duplicate of either new statement; the closed-pushforward stalk
model is restricted to a closed immersion and a degree-zero unit pushforward, whereas
this argument concerns arbitrary E and arbitrary derived representative G. Existing
KFlatResolution, KFlatStalkCriterion and Modules.TensorPullbackStalk are used in the
new comparison's proof plan, rather than restated. LeanSearch returned Internal Server
Error for both queries; this is recorded as unavailability, not an absence verdict.
All three search kinds are recorded by msearch.py in searches.jsonl and the new nodes.

Sources were read online because this machine's literature directory contains only the
tracked lists, not the Stacks source checkout:
[00A0](https://stacks.math.columbia.edu/tag/00A0) for open restriction,
[01AG](https://stacks.math.columbia.edu/tag/01AG) for exact stalks,
[06YB](https://stacks.math.columbia.edu/tag/06YB) for K-flat stalks,
[064K](https://stacks.math.columbia.edu/tag/064K) for bounded-above flat K-flatness,
and [0098](https://stacks.math.columbia.edu/tag/0098) for the tensor-pullback stalk formula.
The node proof_origin is marked agent for the explicit assembly of those source arguments.

Edge cases checked in words: the zero strict complex supplies zero finite-projective
terms and a zero stalk model; arbitrary bounds do not affect the upper-bound conversion.
A point cannot lie in an empty neighbourhood, and an empty scheme has no x, so neither
statement loses an empty-space case. For the residue comparison, the residue spectrum is
one point, so sections are exact for all module sheaves, without a quasi-coherence assumption.
A complex unbounded below remains K-flat when bounded above and free. No finite-rank
assumption is needed for this comparison. A different free model is allowed because the
comparison is on derived residue tensor, not on individual terms. The two derived morphism
universes need not agree: only the represented isomorphisms are compared.

The generic nodes from other units are used as tools for exact stalks, resolutions, K-flatness
and module pullback; they replace no step of sk-prop-av-cube. The local-ring freeness node
is a Mathlib leaf. The maintainer can record these tool uses at review if needed.

## New nodes

`lem-sc-local-strict-perfect-stalk-projective-model`:
`lean/Sheaf/AlgebraicGeometry/LocalStrictPerfectStalkProjectiveModel.lean`.
Splits original steps 1-2 at the finite-projective stalk construction, before local-ring
freeness. It records open-neighbourhood cofinality, finite-free sheaf retracts, and exact
stalk transport through localization.

`lem-sc-stalk-free-residue-cohomology-comparison`:
`lean/Sheaf/AlgebraicGeometry/StalkFreeResidueCohomologyComparison.lean`.
Splits the geometric comparison part of original step 3, independently of local perfection
and finite-dimensionality. It records K-flat resolution and stalk comparison, derived
invariance of residue extension for bounded-above free representatives, and linearity of
the resulting homology comparison. No affine derived-pullback model or composition theorem
is needed. Both nodes inherit the item's chapter, unit and blueprint ancestry.


## Second reading by C4

1. PASS. Compared the delivered existing module with the repository by `diff`.
   Its sole declaration's signature, universes, visibility, definitions and public
   imports are unchanged byte for byte. Only proof imports, the proof body and its
   explanatory docstring change. There are no adapted modules or change records.
2. PASS as a decomposition. Compiled all three modules in import order using
   lcompile.py, including after the import cleanup. A scratch-copy `#print axioms`
   checks all three declarations; only propext, Classical.choice, Quot.sound and
   sorryAx occur. The assigned module has no sorry. The two new named theorems
   each have exactly `:= by sorry`, a source, a complete proof docstring and a node.
   No forbidden declarations or hollow definitions occur. Existential witnesses
   are eliminated inside a propositional proof; no data definition chooses an
   arbitrary object from an unproved existence assertion.
3. PASS. Read both helper signatures, proof arguments and matching nodes. The
   first asserts bounded finite-projective stalk construction without residue
   comparison; the second compares a supplied bounded-above free model without
   constructing it or asserting finiteness. Neither restates the original theorem.
   Checked zero representatives, empty schemes (no point), bounds with a > b
   (all terms vanish), unbounded-below free representatives and infinite ranks.
   Read Stacks 00A0, 01AG, 06YB, 064K and 0098 online. On Spec of a field, sections
   equal the unique stalk, so are exact without quasi-coherence. Independently
   searched LeanFinder for finite-projective germ complexes, Loogle for
   `Module.Free, CochainComplex` (zero hits), and grep for residue homology and
   projective stalks. Also searched Sheaf and upstream WeilConjectures. The nearby
   StrictPerfectClosedPushforwardStalkModel has a closed-immersion, degree-zero
   hypothesis and cannot replace either helper. No full match was found. Neither
   geometric interface can be closed in a few minutes with the available lemmas.
4. PASS. The main proof uses the two interfaces, Mathlib local-ring freeness,
   Module.Finite.equiv and LinearEquiv.finrank_eq directly. Existing dependency
   declarations do not already give the interfaces. Removed three redundant public
   imports from the new comparison module and recompiled. Proof-plan imports of
   still-open helpers remain as required by the stage contract. Expanded
   `No longer needed` to account for every old proof dependency. The two pruned
   modules are not imported by either helper. Read sk-prop-av-cube's realized
   record (statement and step lists empty): no realized node is bypassed or altered.
5. PASS. Existing node changes are exactly proof, proof_deps and proof_origin.
   All three node signatures equal the Lean signatures verbatim, and every
   proof_deps list is the union of the steps' uses. New nodes contain the required
   source, search, creation, blueprint, chapter, unit and Lean fields.

Changes by this reader: corrected the main theorem's stale affine/composition
proof sketch to describe the K-flat stalk/tensor-pullback route; removed redundant
public imports of ModuleCat.Free, DerivedCategory.TStructure and
LocalRing.ResidueField.Defs from the new comparison module; completed the old
dependency accounting and recorded this independent review. No proof body or
statement changed. Closed one of one original holes; added two smaller holes;
net minus one, a decomposition rather than a completed axiom-free proof.
