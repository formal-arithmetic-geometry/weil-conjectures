## What changed

Reduced `AlgebraicGeometry.Scheme.exists_tensorModel_restriction_adjunction` to
coherent tensor-model object comparisons and the existing canonical tensor-Hom
family. Two proved private helpers specialize adjunction naturality and transport
Hom equivalences through isomorphisms. The target constructs both transposition
families and proves their restriction and precomposition equations. Its signature
and existing docstring are unchanged.

Added `Sheaf.AlgebraicGeometry.TensorModelRestrictionComparisons` for the geometric
comparison step. Updated both DAG proof records to match the reduction. Repaired
the earlier attempt's incomplete signature, missing search records, circular
statement dependency, and non-self-contained statement in the new node.

## Proved and sorry left

Closed the sole original hole,
`AlgebraicGeometry.Scheme.exists_tensorModel_restriction_adjunction`
(node `lem-sc-tensor-model-restriction-adjunction`). No sorry remains in the item.
The private `tensorHom_precomp` and `transport_tensor_adjunction` are fully proved.

Added one hole:
`AlgebraicGeometry.Scheme.exists_tensorModel_restriction_comparisons`
(node `lem-sc-tensor-model-restriction-comparisons`). This is a decomposition,
with one hole closed and one added, not a net reduction in holes. The new theorem
states coherent object isomorphisms and evaluation compatibility; it does not
state the final transposition equivalences or their precomposition law.

## No longer needed

Removed the direct proof import `Sheaf.AlgebraicGeometry.DerivedInternalHomAdjunction`;
node `lem-sc-derived-internal-hom-adjunction` is not needed by this reduction.
The fixed canonical family already provides the required adjunction and naturality.
No claim is made that this module is absent from every other target branch.

The following direct proof imports moved from the item into the comparison module,
and remain needed by that intermediate argument:
`Sheaf.AlgebraicGeometry.OpenRestrictionKFlatModel`,
`Sheaf.AlgebraicGeometry.OpenRestrictionTotalTensor`,
`Sheaf.AlgebraicGeometry.KFlatDerivedTensorComparison`,
`Sheaf.Algebra.Homology.HomComplexRestrictOpen`,
`Sheaf.Algebra.Homology.KInjectiveRestrictOpen`, and
`Sheaf.Paper.DerivedInternalHomRestrictOpen`.
Their nodes remain dependencies of the new comparison node, so they are not pruned.
The comparison module also imports `Sheaf.Algebra.Homology.KInjectiveHomComplex`
and `Sheaf.AlgebraicGeometry.DerivedTensorSymmetry`, the named results used to
justify the arbitrary-source representative argument and the tensor ordering.

## Where the brief, the DAG or earlier work was wrong

The existing object-comparison lemmas do not state the evaluation coherence needed
by the target. The new comparison statement isolates this missing geometric step.
The old sandbox supplied a genuine transport argument but did not simplify the
internal-Hom map of the pair of identities, and its new node lacked the full Lean
signature, search records, and a self-contained statement. Its statement dependency
on the target would also have produced a DAG cycle; that dependency is removed.

The comparison was checked on zero complexes, the empty open, and arbitrary
non-K-flat second complexes. No inversion of a map depending on K-flatness of J is
used. K-flatness is imposed solely on P; maps from Q(J) are handled by the
K-injective Hom model in the geometric comparison argument. The unit record
`sk-thm-picard-duality` has empty realized lists, and this reduction keeps the
same tensor-model route below that unit.

WANTED: `literature/stacks-project/cohomology.tex`, Tags 08DJ and 08DL (and 06YH),
for `lem-sc-tensor-model-restriction-comparisons`. The local clone contains the
citation records but not this source text. The proof in words follows the existing
node's sourced argument and is marked agent-written.

## New nodes

`lem-sc-tensor-model-restriction-comparisons`, in
`dag/nodes/sec-picard-framework/lem-sc-tensor-model-restriction-comparisons.json`,
is stated by `exists_tensorModel_restriction_comparisons` in the new module
`lean/Sheaf/AlgebraicGeometry/TensorModelRestrictionComparisons.lean`.
It records the tensor comparison, RHom comparison, and local evaluation argument,
including coverage of arbitrary derived morphisms by a K-injective Hom model.
No definitions, existing public signatures, or target statements changed; there
are no forced adaptations or change records.


## Second reading by N2

1. Compared the complete delivered item with the repository version using diff.
   The existing theorem signature and docstring are unchanged; restored the single
   space before its proof delimiter for byte-for-byte signature preservation.
   Only proof code and proof imports change. The comparison module is new;
   no existing definition or interface is changed and no change record is needed.
2. Both modules compile locally through lcompile.py, with no compiler errors or
   warnings. Scratch copies with #print axioms for both public theorems report
   exactly propext, Classical.choice, Quot.sound and sorryAx. The item has no sorry;
   the comparison module has precisely the one reported named theorem with sorry.
   There are no definitions, axiom, unsafe, opaque, implemented_by or extern in
   the delivery. The private transport and naturality helpers are actual proofs.
3. Read the full comparison statement, its proof docstring and its node. It
   isolates the geometric object and evaluation comparisons; it does not restate
   the final Hom equivalences or their precomposition law. The categorical part
   is proved independently in the item. Checked zero P and J, the empty open,
   U = X, and non-K-flat J: no extra invertibility of J is needed, since maps
   into Hom(P,I) are represented by chain maps using its K-injectivity.
   Read Stacks Tags 08DJ, 08DL and 06YH online, and the library's canonical-family,
   K-flat tensor comparison, K-injective Hom and RHom restriction declarations.
   The chosen comparisons can be taken from the same representative construction,
   so the evaluation equation holds after passage to homotopy and localization.
   Searches with leanfinder for "open restriction strong monoidal derived closed
   functor evaluation compatibility", loogle for Functor.map_homCongr, and rg for
   tensor/restriction and evaluation/uncurry found no full comparison theorem.
   Mathlib's MonoidalClosedFunctor comparison uses Cartesian monoidal categories,
   so it does not apply to this sheaf tensor. Existing derivedTensor_openRestriction
   isomorphisms give object comparisons, without the needed evaluation equation.
   This hole cannot be closed by those results alone in a few minutes.
4. The proof takes the canonical adjunction and genuine Iso.homCongr transport
   directly. The new module's CanonicalDerivedTensorHom public import is required
   by its signature; all its geometric imports are plain proof imports. Removed
   its redundant public DerivedInternalHom import: CanonicalDerivedTensorHomModel
   already exports that signature dependency through CanonicalDerivedTensorHom.
   The original item's public imports remain unchanged. All old proof dependencies
   absent from its new proof_deps are accounted for below. The unit
   sk-thm-picard-duality has empty realized lists; no realized unit step is bypassed.
5. The existing node differs only in proof, proof_deps and proof_origin, and those
   follow the transport proof. The new node has the complete Lean statement,
   source, dependency union, searches, creation record, blueprint origin, chapter,
   unit and Lean record. Its statement dependencies are acyclic. Its sole sorry
   is exactly the named comparison statement; there is no arbitrary witness
   selected into a definition. Verdict: valid decomposition, zero net holes closed.

Second reading changed only signature whitespace, the redundant public import
in the new module, and this report. No mathematical proof repair was necessary.
The source text is available at https://stacks.math.columbia.edu/tag/08DJ,
https://stacks.math.columbia.edu/tag/08DL and
https://stacks.math.columbia.edu/tag/06YH; the local cohomology.tex remains wanted.

For completeness, old direct proof_deps moved to the comparison node are
lem-pc-kflat-derived-tensor-comparison, lem-pc-open-restriction-kflat-model,
lem-pc-open-restriction-total-tensor, lem-sc-derived-internal-hom-restrict-open,
lem-sc-hom-complex-restrict-open and lem-sc-derived-k-injective-restrict-open.
Only lem-sc-derived-internal-hom-adjunction is no longer used by this reduction.
The redundant public import removed from the new module prunes no extra node.
