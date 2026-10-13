## What changed

The signature and public imports of `Sheaf.AlgebraicGeometry.ProperDirectImageFiniteTor`
are unchanged. Its single theorem now has a complete Lean proof from the existing
bounded-coherent direct-image theorem and quasi-coherent Tor-test criterion, the new
proved general upper tensor bound, and one new lower-bound statement.

`Sheaf.AlgebraicGeometry.DerivedTensorUpperBound` proves
`AlgebraicGeometry.schemeDerivedTensorCohomologyVanishes_of_upper_bound`.
It represents an upper-bounded derived object by an upper-bounded complex, applies the
existing flat replacement, obtains K-flatness, and uses the existing termwise tensor
bound and homology vanishing. This works for every module test, without properness,
coherence, quasi-coherence or a finite-Tor hypothesis.

`Sheaf.AlgebraicGeometry.ProperDirectImageTensorLowerBound` isolates the source's
projection-formula lower-bound argument for quasi-coherent tests. It asserts only
one-sided lower vanishing, with no upper bound or arbitrary-module extension.
The parent proof combines that bound with the direct image's upper cohomology bound,
uses `[a,max a b]` to ensure ordered endpoints, and extends the resulting interval to
all modules using `torAmplitude_of_quasiCoherent_tests`.

The resumed worker independently rechecked all three sandbox modules in import order
with `lcompile.py --all`: each compiled without errors or warnings. The delivery dry run
printed OK, with only the second reading outstanding as expected; nothing was pushed.
The resumed worker also reread Tag 08EV and the supplied signatures: the source explicitly
separates the upper bound from the projection-formula lower bound used here.
No existing statements, definitions, universes, visibility or public imports changed.
Both new statements were checked mathematically for the zero complex, zero test module,
identity morphism, empty scheme and shifted complexes. The upper statement excludes
only degrees strictly above b, retaining possible nonzero H^b. The final max endpoint
also handles an upper bound b smaller than the lower bound a.

The route follows the actual [Stacks Tag 08EV proof](https://stacks.math.columbia.edu/tag/08EV),
read online because the checkout has only the literature lists. Its upper-bound argument
uses boundedness of Rf_*E, without the DAG's uniform cohomological-dimension estimate.
The unit `sk-thm-picard-duality` has no realized statement or step nodes; its route is
unchanged. Existing node edits are restricted to proof, proof_deps and proof_origin.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Scheme.hasFiniteTorDimension_schemeDerivedDirectImage_of_bounded_coherent_support`
(node `lem-pc-proper-direct-image-finite-tor`). No holes remain in the item's module.

Also proved the new theorem
`AlgebraicGeometry.schemeDerivedTensorCohomologyVanishes_of_upper_bound`
(node `lem-pc-derived-tensor-upper-bound`) from the existing flat replacement,
bounded-above K-flatness and source tensor-bound declarations. Its module has no hole.

Added exactly one hole:
`AlgebraicGeometry.Scheme.exists_schemeDerivedDirectImage_tensor_lower_bound`
(node `lem-pc-proper-direct-image-tensor-lower-bound`). Its proof is exactly `by sorry`;
its docstring and node carry the source and full lower-bound argument.

This is a decomposition: one existing hole closed and one strictly smaller hole added,
net zero new reductions in the hole count. The main theorem still depends on the existing
holed direct-image and Tor-test declarations and their dependencies. No definitions with
postponed data or proof holes were added.

## No longer needed

Removed these eight direct proof imports from the item:

- `Sheaf.Algebra.Homology.BoundedAboveFlatRingedSpaceKFlat`
  (`lem-pc-bounded-above-flat-kflat`): now used in the upper-bound module and planned
  lower-bound argument, rather than directly by the parent.
- `Sheaf.Algebra.Homology.BoundedFlatReplacement`
  (`lem-pc-kflat-bounded-flat-replacement`): likewise.
- `Sheaf.Algebra.Homology.KFlatPullback`
  (`lem-pc-kflat-pullback-preservation`): retained only in the lower-bound argument.
- `Sheaf.AlgebraicGeometry.DerivedDirectImageUniformTruncationBound`
  (`lem-pc-derived-direct-image-uniform-truncation-bound`): unnecessary for the tensor
  bound, since boundedness of Rf_*E already supplies the upper endpoint.
- `Sheaf.AlgebraicGeometry.DerivedPullbackTensorQCoh`
  (`lem-pc-derived-pullback-tensor-qcoh`): retained only in the lower-bound argument.
- `Sheaf.AlgebraicGeometry.DirectImageQCSupportReduction`
  (`lem-pc-direct-image-qc-support-reduction`): retained only in the lower-bound argument.
- `Sheaf.AlgebraicGeometry.FlatComplexDerivedPullback`
  (`lem-pc-flat-complex-derived-pullback`): retained only in the lower-bound argument.
- `WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Sections`
  (`lem-pc-projection-formula`): the recorded declaration is an unusable specialization
  for this argument, so the lower-bound module does not import it either.

The parent node no longer has any of those eight nodes as direct proof dependencies,
nor `def-pc-derived-direct-image` as a direct proof dependency; the latter is still
needed by its signature and lower-bound argument. No claim that these whole modules
leave the target import closure is made: several are still reachable via other imports,
and the uniform truncation bound remains in DirectImageBoundedCoherent's dependencies.
The lower-bound mathematical plan still requires the general derived projection formula,
not the recorded invertible-module specialization. No unit-level result was bypassed.

## Where the brief, the DAG or earlier work was wrong

The DAG planned an upper bound b+N-1 using the uniform direct-image truncation bound.
The source's simpler argument first obtains boundedness of Rf_*E and then observes
that tensor with a degree-zero module preserves its upper bound. The new proved
upper-bound module formalizes precisely that argument, using the existing flat resolution.

Two interfaces prevent direct transcription of the remaining lower-bound plan:

1. `AlgebraicGeometry.directImage_qc_support_reduction` requires derived-category
   instances for every scheme in the same universe. The parent theorem supplies
   instances only for X and S. Its geometric conclusion is suitable, but the current
   interface cannot simply be applied. The lower-bound worker must localize on the open
   subscheme and compare that chosen localization to the given ones, or obtain a suitably
   polymorphic restriction/reduction interface; the parent statement was not strengthened.
2. The DAG attaches `lem-pc-projection-formula` to
   `AlgebraicGeometry.Scheme.Modules.nonempty_higherDirectImage_tensorObj_pullback_iso`
   in Sections. That theorem states only higher direct images of module sheaves twisted
   by an invertible module. It does not provide the derived projection formula for an
   arbitrary quasi-coherent test module, which the lower-bound proof needs.

LeanSearch returned Internal Server Error for both new-node searches; the records say
unavailable. LeanFinder, Loogle and Mathlib grep searches were run and logged. Their
results give generic bounds and truncations, with no exact existing sheaf-derived-tensor
upper theorem or proper-support lower theorem. Blueprint searches for the bound phrases
and 08EV found no additional blueprint statements to reuse.

## New nodes

`lem-pc-derived-tensor-upper-bound`, in
`dag/nodes/sec-picard-framework/lem-pc-derived-tensor-upper-bound.json`, is the generic
upper-bound lemma just proved in `Sheaf.AlgebraicGeometry.DerivedTensorUpperBound`.
It has no new hole and uses the existing bounded flat replacement and K-flatness nodes.

`lem-pc-proper-direct-image-tensor-lower-bound`, in
`dag/nodes/sec-picard-framework/lem-pc-proper-direct-image-tensor-lower-bound.json`,
is the remaining one-sided quasi-coherent lower-bound argument from Tag 08EV.
It is strictly weaker than finite Tor dimension: it supplies neither an upper bound
nor vanishing against arbitrary module sheaves. Its module is
`Sheaf.AlgebraicGeometry.ProperDirectImageTensorLowerBound`.

No change records or forced adaptations are needed.


## Second reading by C2

1. Interface preservation: PASS. Compared the delivered item with its repository
   counterpart using a file diff and an exact signature comparison. The existing
   theorem signature is byte for byte identical, including hypotheses, universes and
   conclusion. All original public imports and visibility remain unchanged. The other
   two modules are new; there are no definitions, changes to targets or forced adaptations.
2. Proof and trust: PASS. Independently compiled all three modules in import order,
   without errors or warnings. The item and upper-bound module contain no sorry; the
   lower-bound module contains exactly its one named theorem proved by `by sorry`.
   No forbidden axiom, unsafe, opaque, implemented_by, extern or kernel-skip declaration
   occurs. Scratch copies with `#print axioms` check the three delivered theorems;
   only the permitted standard axioms and sorryAx from open dependencies occur.
   There is no construction of arbitrary data from an unproved existence theorem.
3. Split statements: PASS. Read the definitions of the tensor-vanishing predicate and
   finite relative Tor dimension, the full new docstrings and nodes, and independently
   reread https://stacks.math.columbia.edu/tag/08EV. The remaining lower statement is
   true and strictly narrower than the original finite-Tor result: it only controls
   degrees below a for quasi-coherent tests. The upper statement handles arbitrary
   module tests and is proved. Checked zero objects/tests, the empty scheme, identity
   maps and shifted complexes; neither endpoint asserts vanishing at the endpoint.
   A missing ordering hypothesis in the lower statement's boundedness premise is
   harmless: if its endpoints are reversed, the premise forces E to be zero.
   Independent LeanFinder search used right t-exactness and pushforward terminology;
   Loogle searched tensorObj with IsStrictlyLE; Mathlib grep and repository searches
   found no duplicate of either new statement. The existing pinned projection formula
   in RightAdjointTensorComparisonProjection requires properness, extra instances and
   monoidal/adjunction data, so it cannot close this lower statement in a few minutes.
4. Route and pruning: PASS. The parent really combines the existing bounded-coherent
   direct-image and quasi-coherent Tor-test theorems with separate lower and upper
   bounds, using max to keep the endpoints ordered. The upper proof uses Mathlib
   truncation and the upstream termwise tensor-bound theorem directly. The report's
   No longer needed section accounts for every removed old proof dependency, including
   the retained signature dependency def-pc-derived-direct-image. Removed direct imports
   are not claimed as modules pruned from the entire target closure. The unit record
   sk-thm-picard-duality has empty realized arrays, so no realized unit step is bypassed.
5. DAG consistency: PASS. Existing node edits are exactly proof, proof_deps and
   proof_origin. For each delivered node, proof_deps is precisely the union of uses
   in its proof steps. Both new nodes have source, full proof plans, three search kinds,
   creation/blueprint/chapter/unit metadata and exact multiline Lean statements.

Second-reading repair: added the proof-only import
Sheaf.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian to the lower-bound module,
matching its planned coherence-to-quasi-coherence step and recorded proof dependency.
No mathematical statement or proof body changed. Added this review and independent
search evidence. The delivery remains a decomposition: one original hole closed,
one smaller hole added, net zero; the new upper theorem adds no hole.
