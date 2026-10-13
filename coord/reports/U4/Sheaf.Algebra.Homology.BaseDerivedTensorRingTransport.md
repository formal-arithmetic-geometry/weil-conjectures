## What changed

Repaired the returned cycle
`BaseDerivedTensorRingTransport -> BaseDerivedTensorRingIsoNaturality ->
BaseDerivedTensorRingTransport`. The transport module now imports only its
unchanged public model dependency and two new proof modules. No existing
signature, definition, visibility, or other group's module is changed.

The transport proof lifts alpha and tau to semilinear module-complex
isomorphisms. One new ordinary-comparison theorem supplies the tensor-ring
isomorphism, its ordinary chain coordinates, and the cohomology square, allowing
the original independent derived-category universes. Tensor induction proves
compatibility with the fourth-ring maps and the ordinary-to-localized chain
square. A new, fully proved general semilinear scalar-extension homology lemma
extends that square. Finally the proved exact restriction/forgetting homology
coherence and naturality give exactly the original additive square.

Updated the item node's proof, proof_deps and proof_origin. Added nodes for the
ordinary-comparison theorem and the proved scalar-extension lemma. All belong
to sk-thm-picard-semicon and refine its ordinary-comparison argument. Its realized
statement and steps are unchanged. There are no forced adaptations and no
change record is needed.

## Proved and sorry left

Closed the one original hole:
`ModuleCat.exists_baseDerivedTensor_ring_transport`
(node `lem-pc-base-derived-tensor-ring-transport`). No sorry remains in the item.

Added one hole:
`ModuleCat.exists_baseDerivedTensor_ordinary_ring_comparison`
(node `lem-pc-base-derived-tensor-ordinary-ring-comparison`), in its own new module.
Its complete proof in words is in the docstring and DAG node. This theorem is
strictly the ordinary derived tensor part: its conclusion involves neither
extension to the fourth rings nor localizedComparison or ordinaryToLocalized.
Although C0,C remain model parameters, no coefficient isomorphism between them
or chain isomorphism of localized targets is an input. It therefore does not
restate the transport theorem. It combines coefficient and localization-universe
transport before scalar extension. This is a decomposition: one original hole
closed and one smaller hole added, with net zero holes from this delivery.

Also fully proved `ModuleCat.exists_scalarExtension_homology_square`
(node `lem-pc-semilinear-scalar-extension-homology-square`), with no sorry.
Its module imports only Mathlib. Its private helpers construct the tensor
isomorphism, prove restriction/forgetting homology coherence and prove homology
naturality. The public theorem combines the ordinary square, additive chain
square, and adjoint equations, then tests on unit tensors using
ExtendScalars.hom_ext. Its axiom check shows only propext, Classical.choice,
and Quot.sound. Every helper in the transport module is also proved.

All three delivered modules compile in dependency order without warnings.
The statements impose no flatness, boundedness or invertibility assumptions on
the comparison maps, and permit zero rings and zero complexes. Identity
coefficient maps recover the ordinary naturality square. The source tensor
isomorphism is explicitly constructed in Lean from the supplied ring and
cohomology isomorphisms; no arbitrary data construction from an existence hole
is added.

## No longer needed

Removed the returned proof import of
`Sheaf.Algebra.Homology.BaseDerivedTensorRingIsoNaturality` and its node
`lem-pc-base-derived-tensor-ring-iso-naturality` from this item's proof route.
That module is a downstream consequence of this item and cannot be a dependency.
It remains in the library for its other users; no global pruning is claimed.

Removed the returned delivery's new
`Sheaf.Algebra.Homology.BaseDerivedTensorUniverseComparison` module and
`lem-pc-base-derived-tensor-universe-comparison` node from the delivery. The new
ordinary coefficient comparison handles the original universes directly, so
no canonical standard models, separate universe bridge, or localized universe
comparison helper is needed.

Removed the original redundant proof import
`Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex`, already available
through the unchanged public model import. No original project proof dependency
is pruned: `def-pc-base-derived-tensor-cohomology-model` remains needed.
The existing `Sheaf.Algebra.Homology.ScalarExtensionHomologySquare` gives a
comparison square for one common target coefficient ring. The proved new lemma
handles two target rings identified semilinearly, and is not an adaptation or
replacement of that existing module.

## Where the brief, the DAG or earlier work was wrong

The returned proof reused a theorem that was already proved by applying this
very item. Compilation against cached imports concealed that circular route.
The repair removes the import and DAG dependency instead of modifying the
other module or assuming its conclusion. The old second-reading section was
removed because it certified this invalid route; the repaired delivery needs a
fresh independent reading.

The original statement infers separate derived-category universes for its two
models. The replacement ordinary theorem explicitly allows both universes;
no common-universe assumption or standard-model workaround is used.

Lean's semilinear LinearEquiv construction requires explicit inverse ring-hom
instances. The scalar-extension proof supplies these from RingHomInvPair's
ring-equivalence lemmas and constructs TensorProduct.congr. Forgetting after
restriction has definitionally identical underlying additive maps, but local
functor abbreviations require explicit change steps before rewriting.

Read Stacks Tag 06Y6 (Lemma 15.61.1) for independence of derived tensor choices,
and Tag 05G3 (Section 10.14, Lemma 10.14.3) for the scalar-extension adjunction.
The ordinary lemma's coefficient-equivalence and universe formulation is an
explicit refinement of that source, not a verbatim quoted theorem. LeanSearch
was unavailable; LeanFinder, Loogle and source grep found the generic components.

## New nodes

`lem-pc-base-derived-tensor-ordinary-ring-comparison`, in
`lean/Sheaf/Algebra/Homology/BaseDerivedTensorOrdinaryRingComparison.lean`:
the remaining ordinary comparison transport, before any fourth-ring extension.
It records the coefficient equivalences, localization uniqueness, universal
counit identification, tensor-action compatibility and ordinary comparison square.
It is the sole new sorry and has a source and complete proof in words.

`lem-pc-semilinear-scalar-extension-homology-square`, in
`lean/Sheaf/Algebra/Homology/SemilinearScalarExtensionHomologySquare.lean`:
a fully proved algebraic lemma extending an ordinary cohomology square across
compatible ring isomorphisms. It contains no derived category and no sorry.
It records the explicit tensor isomorphism, homology coherence and unit-tensor
argument. No existing module is adapted and no change record is required.

## Second reading by U4

1. **Interface and accidental changes.** Compared each delivered module with the repository versions. The existing transport theorem signature and all declarations from the repository are unchanged; the imports changed only to add the two new proof modules and remove the redundant proof-only import. The two additional modules are new nodes explicitly listed in this report.

2. **Compilation and proof hygiene.** Compiled all three modules in dependency order with `lcompile.py --all`; compilation succeeds without warnings. Searched the delivered Lean files for forbidden declarations and `sorry`: the transport and semilinear modules contain none; the sole remaining `sorry` is the named split theorem `ModuleCat.exists_baseDerivedTensor_ordinary_ring_comparison`. No definition contains `sorry`, and no `axiom`, `unsafe`, `opaque`, `extern`, `implemented_by`, or `debug.skipKernelTC` occurs. The proved semilinear theorem uses only the permitted foundational axioms.

3. **Statements and split-off nodes.** Read both new statements against their docstrings and DAG nodes. The ordinary comparison theorem is a strict lower-level decomposition: it stops before fourth-ring extension and localization, while retaining the ordinary comparison square needed by the transport proof. The semilinear scalar-extension theorem is fully proved and has no sorry. Neither restates the transport target, and both statements allow zero rings and zero complexes without extra hypotheses.

4. **Proof route and pruning.** Checked the proof against the node steps and `proof_deps`. The route uses the ordinary comparison node, then the fully proved semilinear square, followed by explicit tensor induction and homology coherence. The cyclic `BaseDerivedTensorRingIsoNaturality` dependency and the unused universe-comparison module are removed; the unit's ordinary-comparison and scalar-extension route remains represented in the DAG. The removed ShortComplex import was already available through the public model dependency.

5. **DAG and unit agreement.** Verified that the item's node, both new nodes, their Lean declarations, statements, proof dependencies, origins, chapter, and unit agree with the delivered files. No existing target statement or definition was changed, and no forced adaptation or change record is required.

I changed only the delivery report by adding this second-reading record and created the required `coord/reports/U4/Sheaf.Algebra.Homology.BaseDerivedTensorRingTransport.md` copy for the delivery tool.
