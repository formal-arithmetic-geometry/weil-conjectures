## What changed

Completed the original statement of
`AlgebraicGeometry.Scheme.Modules.exists_integral_ideal_comparison_filtrations`.
The nonzero branch uses the new common-submodule lemma, forms its canonical
cokernel short exact sequences, and filters both cokernels. A proved private helper
places each nonzero integral-ideal factor's closed image inside the ambient
cokernel support, using stalk injectivity/surjectivity, its nonzero generic stalk,
and closedness of coherent support. Transitivity gives strict containment in i(W).

The existing coherent integral-filtration theorem cannot be imported: its import
closure reaches this item. Instead use the existing finite-presentation filtration
and `CategoryTheory.finite_filtration_refinement`. The proved private helpers
`ideal_bot_isZero` and `exists_finitePresentation_nonzero_integral_filtration`
remove zero-ideal factors by substituting empty filtrations before refinement.
No extra filtration theorem with sorry is needed.

Added only the module `Sheaf.AlgebraicGeometry.IntegralIdealCommonSubmodule`.
Its theorem supplies monomorphisms from a common module, coherent finitely
presented cokernels and strictly smaller supports, but no short exact sequences
or filtrations. This isolates the generic inclusion/intersection part of Tag 01YH;
the remaining construction and filtration/support argument are proved in Lean.
The new node's statement and Lean record now include finite presentation explicitly.
Existing signatures and public imports are unchanged. All new proof imports are
non-public; no existing dependency module is adapted.

## Proved and sorry left

Closed the original hole:
`AlgebraicGeometry.Scheme.Modules.exists_integral_ideal_comparison_filtrations`
(node `lem-pc-v3-integral-ideal-comparison-filtrations`). The item's module contains
no sorry. Its three private helpers are also completely proved.

Added one hole:
`AlgebraicGeometry.Scheme.Modules.exists_integral_ideal_common_submodule`
(node `lem-pc-a2-integral-ideal-common-submodule`), in
`Sheaf.AlgebraicGeometry.IntegralIdealCommonSubmodule`. This is the only sorry in
the delivered Lean files; its proof is exactly `by sorry`, with its source and
construction in the docstring and node.

One upper hole closed and one strictly smaller hole added is a decomposition,
not a complete sorry-free proof. The previous attempt's second hole,
`exists_finitePresentation_nonzero_integral_filtration`, has been removed from
the new module and fully proved as a private helper in the item. It was never
part of the repository baseline and is not counted as a baseline hole closed.

Both modules compile locally through lcompile.py. The final delivery gate is
`deliver3.py A2 Sheaf.AlgebraicGeometry.IntegralIdealComparisonFiltrations --no-push`.

## No longer needed

Removed these original proof imports from the item's module:
- `Sheaf.Algebra.Homology.ModuleStalkExact`: the completed support proof instead
  uses Mathlib's abelian-group stalk functor and the existing forgetful-functor lemma.
- `Sheaf.AlgebraicGeometry.CoherentKernelCokernelLocallyNoetherian`: only the
  postponed common-submodule construction needs this coherence argument.
- `WeilConjectures.AlgebraicGeometry.Cohomology.Affine.AffineMorphism`: only the
  postponed common-submodule construction needs closed-pushforward coherence.

The main proof no longer needs
`lem-weil-pbc-coherent-filtration-integral-subschemes` or its module
`Sheaf.AlgebraicGeometry.CoherentFiltrationIntegralSubschemes`. It instead uses
`lem-pc-e2-finite-presentation-integral-filtration` and
`lem-pc-s3-finite-filtration-refinement`, with a proved removal of zero factors.
This is a local dependency reduction; no claim is made that these modules become
unreachable from every other target import.

The generic inclusion, intersection, stalk exactness and coherence construction
nodes remain needed under the new common-submodule node, so are not claimed
pruned from the whole argument. The directly used generic-stalk, closed-pushforward,
closed-support, coherent/finite-type and forgetful-functor nodes remain in the main
proof dependencies. No UNIT statement or realized step is bypassed: the unit
`sk-thm-picard-coherence` has empty realized statement and step lists.

## Where the brief, the DAG or earlier work was wrong

The previous sandbox report said there was only one new sorry, but its new module
actually held a second, undocumented filtration theorem without a node. That hole
is now eliminated by a real proof from the existing filtration and refinement lemmas.
The common-submodule node's Lean record also omitted the finite-presentation
conclusions present in its theorem; the node and record now agree.

The earlier report claimed the existing coherent filtration supplied nonzero
factors directly. Its signature does, but importing it here creates this cycle:
CoherentFiltrationIntegralSubschemes -> CoherentSupportUnionExactSequence ->
CoherentSupportPowerIdealKills -> CoherentFormalModule -> ModuleSupportProperOverBase ->
ClosedImmersionPushforwardAnnihilated -> AffinePushforwardBaseChange ->
WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.AffineMorphism ->
WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.FiniteFreeComplex ->
IntegralIdealProperCohomology -> IntegralIdealComparisonFiltrations.
The finite-presentation filtration and categorical refinement do not reach this
item, as checked with tools/import_direction.py. No dependency is copied or edited.

Checked the mathematical construction against Stacks Tags 01YH and 01YF.
The zero ideal is handled by the original first disjunct; zero cokernels admit
empty filtrations; on an integral one-point support the strictly smaller cokernels
are zero. For nonzero ideals, the intersection is nonzero because nonzero affine
sections have nonzero product in a domain. Generic rank one forces exactly one
summand in the generic ideal inclusion. The new statement asserts strictly less
than the original comparison theorem: it neither constructs the two short exact
sequences nor their filtrations, and the main proof combines those parts explicitly.

## New nodes

`lem-pc-a2-integral-ideal-common-submodule`, in
`dag/nodes/sec-picard-framework/lem-pc-a2-integral-ideal-common-submodule.json`,
is the generic ideal inclusion and intersection construction of Stacks Tag 01YH.
It retains the original hypotheses and asserts only a common source of two
monomorphisms with coherent finitely presented cokernels of smaller support.
Its source, proof steps, searches and exact Lean signature are recorded. The
existing comparison node's proof and proof dependencies follow the completed Lean
argument, including zero-factor removal. No change record or forced adaptation
is needed: all existing interfaces are unchanged.

## Second reading by A2

1. **Comparison with the repository.** I diffed the delivered comparison module
   against the repository version. The target theorem's signature and every
   existing declaration are byte-for-byte unchanged; only proof imports and proof
   bodies changed. The added common-submodule module is a new declaration and is
   recorded by its new DAG node.

2. **Compilation and axioms.** I compiled both delivered modules with
   `lcompile.py --all`; compilation succeeds. The comparison theorem and its
   private helpers contain no `sorry`. The sole remaining `sorry` is the named
   common-submodule theorem, exactly as listed above. No axiom, unsafe, opaque,
   extern, or implemented-by declaration was added. The split theorem is a real
   public theorem with a source docstring and matching node.

3. **Statements and new node.** I checked the common-submodule statement against
   the generic ideal-inclusion/intersection argument in Stacks Tags 01YH and 01YF.
   Its hypotheses and conclusions are exactly those needed by the comparison
   proof: two monomorphisms, coherent finitely presented cokernels, and strict
   support containment. It does not restate the comparison target or assert the
   later filtrations. Small edge cases (zero ideal and zero cokernel) are handled
   explicitly in the comparison proof, while the split theorem assumes the
   pushforward is nonzero.

4. **Pruning and route.** The proof uses the finite-presentation filtration and
   categorical refinement, deleting zero factors by empty filtrations. This keeps
   the unit route and removes only imports and nodes no longer used by the written
   proof. The removed imports and dependencies are listed under “No longer
   needed”; no target statement or definition was altered.

5. **DAG agreement.** The comparison node's `proof`, `proof_deps`, and
   `proof_origin` match the Lean proof, and the new node has its required source,
   statement, proof steps, Lean record, and blueprint/unit/chapter metadata. The
   node and module agree on the finite-presentation conclusions and on the exact
   theorem signature.

I changed only the proof imports and proof of the comparison module, added the
common-submodule theorem/module and node, removed the undocumented intermediate
filtration hole by proving it privately, and added this second-reading record.
