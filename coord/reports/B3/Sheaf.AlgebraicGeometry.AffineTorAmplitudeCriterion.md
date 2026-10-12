## What changed

Proved AlgebraicGeometry.affine_torAmplitude_iff in the assigned module, without changing
its signature, public imports, or any definition. Added proof-only imports of
Sheaf.Algebra.Homology.BoundedFlatKFlat,
Sheaf.AlgebraicGeometry.AffineDerivedTildeHomologyComparison,
Sheaf.AlgebraicGeometry.KFlatDerivedTensorComparison, and
WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle.
The private helper isZero_derivedTensor_homology_of_vanish unpacks the vanishing predicate
and uses the existing K-flat tensor comparison on constant singleton families.
The forward implication uses the stated bounded flat model and its associated-sheaf
K-flatness. The converse tests associated module sheaves, transports tensor and cohomology
comparisons, and uses full faithfulness of tilde to detect zero modules.
The original nonempty-interval hypothesis and both independent derived-category universes
are preserved. The unit realization has no additional binding steps at this node.

## Proved and sorry left

Closed: AlgebraicGeometry.affine_torAmplitude_iff
(node lem-pc-affine-tor-amplitude-criterion), the only original sorry.
The private helper is fully proved. No sorry remains in the delivered module;
no new sorry or Lean module is added. This is a proof from the existing declarations,
not a decomposition. Any existing dependency holes are unchanged. In the current repository,
DerivedCategory.module_torAmplitudeIn_iff_exists_flat_model is already proved.
The two new DAG records point to already proved source declarations.

## No longer needed

No original module import is removed; all original proof modules are used.
No module is claimed pruned from the targets' import closure.
The direct dependency lem-weil-pbc-spec-tilde-stalk-localization is replaced by
new-affine-derived-tilde-homology-comparison. Stalk localization remains a transitive
ingredient of existing dependencies, so this does not claim that its module is pruned.
No separate bounded-above free resolution or extra affine cohomology-reflection lemma
needs to be stated or proved. The generic source tensor and resolution tools already exist.

## Where the brief, the DAG or earlier work was wrong

The original plan omitted the interface between the existential K-flat vanishing predicate
and cohomology of the actual derived tensor. The private helper proves this interface using
lem-pc-kflat-derived-tensor-comparison. The bounded-flat K-flatness lemma must also be
used before applying isKFlat_tilde. The existing affine cohomology comparison supplies
exactness of tilde without rebuilding the stalk-localization argument here.
The earlier sandbox attempt did not compile: the tensor notation namespace was missing.
Opened MonoidalCategory, fixed definitional comparisons with declaration-scoped
transparency options, and made the final zero-object goal explicit. The resulting
proof compiles locally within the single-file limit.
No mathematical statement was disputed or changed. The missing local literature files
were checked against the official Stacks pages for Tags 08E9, 06Y4 and 06YH.

## New nodes

lem-pc-source-module-kflat-resolution records the existing proved generic declaration
CochainComplex.exists_quasiIso_flat_kFlat in
WeilConjectures.CategoryTheory.DerivedCategory.FlatModel, specialized to modules.
It adds no Lean declaration and no hole. Zero rings and zero complexes are included,
and unbounded complexes are allowed by the filtered flat-resolution construction.

lem-pc-source-kflat-module-tensor-model records the existing constructed isomorphism
DerivedCategory.QObjTensorQObjIsoOfKFlatLeft in the same source module. It computes tensor
on an arbitrary K-flat first model and arbitrary second complex, including the zero
complex and unbounded cases. It adds no Lean declaration and no hole. Searches for both
records are in searches.jsonl; LeanSearch was unavailable and is recorded as such.
There are no change records or forced adaptations.

## Second reading by B3

1. Compared the delivered module with the repository version. The theorem signature and all
   existing declaration signatures are unchanged; only proof imports, the private helper, and
   the theorem proof differ.
2. Compiled the module with `lcompile.py`; it succeeds with no errors. The theorem contains no
   `sorry`, axiom, unsafe, opaque, extern, or implemented_by declaration. The proof uses only
   existing declarations and the two source records, whose data is constructed by proved
   source definitions.
3. Checked the helper and theorem route against the DAG statements. The helper is a local
   reduction of the vanishing predicate, and the two added records document existing proved
   source declarations rather than introducing new holes. No statement was weakened or given
   extra hypotheses.
4. Checked pruning and imports. The added proof-only imports are all used by the proof; no
   original public import was removed, and the unit route through the affine equivalence,
   tensor comparison, and homology comparison is retained.
5. Checked the DAG node proof steps, dependencies, origins, and Lean records against the
   proof text. They agree, and the source records identify the existing declarations they use.

Changed during second reading: added this review record only; no Lean or DAG repair was needed.
