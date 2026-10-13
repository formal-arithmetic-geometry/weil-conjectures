## What changed

Repaired D1 by removing the unlanded theorem
`AlgebraicGeometry.standard_flat_single_baseChange_iso_hom` and its node and
change record. Its assertion was equivalent to the target, as the reviewer said.

Added `Sheaf.AlgebraicGeometry.StandardSingleBaseChangeMap`, containing the actual
construction `standardSingleBaseChangeMap` from the canonical base-change mate
followed by direct image of the existing pinned termwise single map
`Scheme.picardTermwiseSingleMap`. This reuses the library notion rather than
duplicating it. The definition has a complete Lean body. The second reader moved the
`DirectImage.Basic` public import (replacing it with the narrower
`Mathlib.AlgebraicGeometry.Fiber`, needed for `HasPullback`) from this construction module to the two
cohomological theorem modules, whose signatures use `IsFlatOver`. Neither chooses data from a new
existence theorem. They require no relative flatness, quasi-coherence or qcqs
hypotheses, and assert no invertibility.

Added separate theorem modules `StandardFlatSingleBaseChangeMono` and
`StandardFlatSingleBaseChangeEpi`. Their statements assert only monicity,
respectively epicity, of the explicitly constructed map on cohomology in one
specified integer degree. Each is strictly a part of the argument: neither
supplies an isomorphism, the complementary property, or any other degree.

The original theorem now combines these two results in each degree, uses balance
of the abelian category of module sheaves, and applies
`DerivedCategory.isIso_iff` to construct and invert the resulting isomorphism.
Its signature and the three public imports are unchanged. The two new proof
imports are private. Updated the target node to this actual route.

Repaired H8 by restoring a declaration docstring immediately before the target,
naming Stacks Tag 0A1D, describing every step of this proof route, and carrying
`(blueprint: lem-pc-standard-flat-single-base-change)`.

All four delivered modules compile together through `lcompile.py --all`, with
no warnings. New statements were checked on zero modules, empty schemes, and
negative cohomological degrees; the construction makes sense in every case.
No separatedness, intrinsic flatness of M, or flatness of g was added.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.standard_flat_single_baseChange` (one of one original holes).
Its proof is complete, conditional on the two new cohomological lemmas.

Added exactly two named holes, each in its own new module:

- `AlgebraicGeometry.standard_flat_single_baseChange_homology_mono`, node
  `lem-pc-standard-flat-single-base-change-mono`;
- `AlgebraicGeometry.standard_flat_single_baseChange_homology_epi`, node
  `lem-pc-standard-flat-single-base-change-epi`.

This is a decomposition, not a sorry-free proof of flat base change. Relative
to the original item it closes one hole and adds two, a net of minus one.
The construction module contains no holes, and the target module has none.
The rejected equivalent helper is absent, not counted as a newly proved hole.

## No longer needed

Removed the rejected helper and its prospective node
`lem-pc-standard-flat-single-base-change-iso-hom`; it was never landed and is
not part of this repaired packet. No existing library import is removed and no
existing library module is claimed pruned. All three original public imports
are still required by the target signature. Each new proof import is used.

The original stalkwise flatness, localized comparison, qcqs induction and
quasi-coherent kernel/cokernel ingredients remain prospective proof dependencies
of the two cohomological obligations. None is falsely reported as pruned merely
because it has moved below those obligations. The three new modules are needed.


The following old direct proof dependencies are no longer used directly by the
parent proof (they remain statement dependencies or prospective ingredients below
the new obligations, so this does not prune their modules):

- `lem-pc-rf-single-complex-qcqs-induction`;
- `lem-pc-counit-stalk-condition-from-localized-comparison`;
- `lem-pc-relative-flat-module-stalk`;
- `lem-pc-pullback-stalk-tensor-flat`;
- `lem-pc-flat-base-derived-tensor-comparison`;
- `lem-pc-module-bounded-flat-kflat`;
- `def-pc-derived-pullback`;
- `def-pc-module-pullback`;
- `lem-weil-pbc-quasi-coherent-module-kernel`;
- `lem-weil-pbc-quasi-coherent-module-cokernel-closure`;

## Where the brief, the DAG or earlier work was wrong

D1: The old report incorrectly called existence of an IsIso morphism strictly
weaker than Nonempty of an isomorphism. These propositions are equivalent.
The repaired packet uses an explicit map and two separately stated cancellation
properties in each degree; the proof combines both properties and all degrees.

H8: The delivered target lacked a declaration docstring. The repaired theorem
has its own source, complete proof route and blueprint identifier immediately
before its declaration.

The old second-reading section endorsed the rejected equivalence. It has been
removed so that a new independent reader can assess this repaired packet.
No second-reading assessment is supplied by this worker.

The repository's `SingleComplexQcqsInduction` already imports a path reaching
this item. `tools/import_direction.py may` refuses its use here as cyclic,
even though its DAG dependencies have no path back to this item. Therefore the
current proof cannot simply import that general criterion. The new obligations
retain the source's affine and Mayer--Vietoris argument as their proof plan;
a future proof using the existing general criterion must first resolve its
import route. No unheld module was adapted or copied to bypass the check.

## New nodes

`def-pc-standard-single-base-change-map`, implemented in
`Sheaf.AlgebraicGeometry.StandardSingleBaseChangeMap`, records the composite of
the existing pinned single-module pullback map with the canonical derived
base-change mate. No duplicate single-pullback notion is introduced.

`lem-pc-standard-flat-single-base-change-mono`, implemented in
`Sheaf.AlgebraicGeometry.StandardFlatSingleBaseChangeMono`, records the monicity
half of the degreewise canonical comparison, with its relative-flat stalk and
qcqs gluing proof plan.

`lem-pc-standard-flat-single-base-change-epi`, implemented in
`Sheaf.AlgebraicGeometry.StandardFlatSingleBaseChangeEpi`, records the epicity
half of that comparison, with the same source calculation and its surjectivity
conclusion only. These are separate properties of one fixed constructed map,
not existence statements for arbitrary witnesses.

Each node records the actual searches run with `msearch.py`: LeanSearch was
unavailable; LeanFinder and Loogle had no exact geometric match; grep found only
unrelated scalar-extension declarations. There is no change record because no
existing signature, definition, visibility or public import was changed.

## Second reading by U2

1. **Interfaces: pass.** Compared the delivered target module with the repository
   using `diff -u` and separately compared its declaration signature as bytes:
   identical. Only its proof, docstring and two private proof imports changed.
   The other three modules and their nodes are new; there are no adaptations or
   changes to existing definitions, statements, visibility or public imports.
2. **Proof and construction: pass, conditional.** Compiled all four modules in
   import order using `lcompile.py --all`. Inspected every delivered declaration:
   exactly the two reported public theorem bodies contain `sorry`, and none of
   the prohibited declarations or attributes occurs. An independent scratch
   probe printed the axioms of both definitions, both obligations and the target.
   Both definitions use only `propext`, `Classical.choice`, `Quot.sound`;
   the three theorems additionally use `sorryAx`, as reported. The new definitions
   construct composites of the existing universal counit, single-complex map and
   adjunction mate; they do not choose arbitrary existence witnesses.
3. **Split statements: pass as a decomposition.** Each statement asserts only one
   cancellation property on cohomology of the fixed constructed map. Neither
   alone restates existence of the target isomorphism. Both are true by the
   degree-zero specialization of Stacks [0A1D](https://stacks.math.columbia.edu/tag/0A1D)
   and the qcqs induction in [0DJ9](https://stacks.math.columbia.edu/tag/0DJ9).
   Read these primary sources and the local definitions of relative flatness,
   the derived mate and its universal counit. Checked zero modules and empty
   schemes (zero comparison), identity base change (invertible comparison),
   and all integer degrees. Negative degrees need not vanish globally after
   derived pullback; the argument uses comparison in all degrees, not an
   incorrect global vanishing assertion. Both holes have source/proof docstrings
   and matching nodes. Independent LeanFinder search for derived direct image,
   relative flatness and base extension found only tensor injectivity lemmas;
   Loogle `"homologyFunctor", "isIso_iff"` returned no hits. Additional `rg`
   searches inspected the existing canonical module comparison and relatively
   flat complex results. The former assumes separatedness; the latter and the
   general qcqs criterion have the documented cyclic import route. Neither hole
   has a direct few-minute closure from these available declarations.
4. **Route and pruning: pass.** The parent uses both obligations in every degree,
   abelian balance, joint reflection by cohomology, and inversion of `asIso`.
   Confirmed the import-cycle refusal with `tools/import_direction.py may`.
   The unit `sk-thm-picard-coherence` has empty `realized.statement` and step
   entries; this below-unit reduction neither changes nor bypasses its route.
   Listed every old direct proof dependency displaced from the parent, while
   distinguishing that from actual pruning. No existing module is pruned.
   Original public imports remain unchanged, and the two proof imports are
   private. Replaced the construction's broad `DirectImage.Basic` import with
   `Mathlib.AlgebraicGeometry.Fiber`, which supplies its required `HasPullback`
   instance. Imported `DirectImage.Basic` directly in the two theorem modules
   whose signatures require relative flatness.
5. **DAG: pass.** The existing node differs only in `proof`, `proof_deps` and
   `proof_origin`. Its new route agrees with the Lean proof. Each new node has
   source, search history, creation, blueprint ancestry, chapter, unit and Lean
   records. All four `proof_deps` sets equal the union of their step `uses`.
   New theorem signatures match their node records. The construction node
   records both definitions; the two open nodes retain the geometric proof plan.

Changes by this reader: narrowed the construction import to `Mathlib.AlgebraicGeometry.Fiber`
and imported `DirectImage.Basic` directly in the theorem modules, made the old direct-dependency accounting explicit, and added this
independent assessment. No mathematical statement or proof body changed.
The accepted result is a decomposition: one original hole closed, two added,
net minus one; it is not a sorry-free proof of flat base change.
