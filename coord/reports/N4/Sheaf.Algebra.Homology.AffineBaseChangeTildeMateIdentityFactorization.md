## What changed

Reduced AlgebraicGeometry.exists_affineBaseChangeTildeMateIdentityFactorization to
an equation in the derived category and the independent homology normalization of
its explicitly constructed raw arrow. Added AffineTildeDerivedTensorMate and
AffineTildeDerivedTensorHomologyCoordinates as proof dependencies. The exact-tilde
derived functor, source cohomology iso, complex coefficient map and raw derived
arrow are real constructions; no data is chosen from either new hole.
The existing target signature and docstring are unchanged.

## Proved and sorry left

Closed the single original hole in
AlgebraicGeometry.exists_affineBaseChangeTildeMateIdentityFactorization by a
complete composition proof. This is a decomposition, not a sorry-free proof.
Added two holes:

- AlgebraicGeometry.exists_affineTildeDerivedTensorMate
  (lem-pc-affine-tilde-derived-tensor-mate).
- AlgebraicGeometry.affineTildeDerivedTensorToPushforward_homology
  (lem-pc-affine-tilde-derived-tensor-homology-coordinates).

All four new definitions have complete bodies. The source cohomology iso uses the
existing proved exact-functor homology comparison. Neither new statement is the
original theorem renamed: the first concerns an arrow before homology, with no
degree or module comparison map; the second computes homology of the raw arrow
without a base-change mate, K-flatness, quasi-coherence or pullback counit.

## No longer needed

No original public imports removed. No transitive mathematical dependencies are
claimed pruned: the original plan's affine resolution, pullback, acyclic
pushforward and pinned-unit calculations remain needed by the derived mate node.
The original direct proof dependencies have been routed through the two new
intermediate nodes; this is decomposition, not removal of those dependencies.
No unit statement or realized step was bypassed.

The following old direct proof dependencies are now indirect through the new nodes;
none is claimed mathematically pruned:

- def-pc-affine-base-change-tilde-coordinates
- def-pc-base-derived-tensor-cohomology-model
- def-pc-derived-base-change-map
- lem-pc-affine-derived-pullback-tensor-tilde
- lem-pc-affine-morphism-hi
- lem-pc-affine-tilde-pushforward-cohomology-normalization
- lem-pc-derived-base-change-unit-compatibility
- lem-pc-source-module-kflat-resolution
- lem-sc-qcoh-acyclic-derived-pushforward-cohomology
- lem-weil-pbc-tilde-pullback-base-change

## Where the brief, the DAG or earlier work was wrong

The stated dependencies do not include a normalized affine comparison between the
universal module derived scalar-extension functor and the sheaf derived
pullback of affine pushforward. They provide the general tools and mate unit
equation. The new derived node isolates that missing calculation, and the new
homology node isolates the exact-coordinate normalization.
The first dry run also flagged a file-local attribute as an interface change.
It was removed. Transparency control now stays inside the proof, with a proved
private categorical composition lemma; no public interface or file-level command
changes are required. The delivery wrapper explicitly permits the missing
second-reader section during a worker dry run when it is the sole finding.

LeanSearch returned Internal Server Error; the other search services and local
source search were available. The nearest imported blueprint ancestor is absent
from this legacy node's created.item chain, as blueprint_refs.py ancestor reports;
the new nodes keep its chapter and unit, record the parent argument and searched
same_as results, and do not change blueprint units.

## New nodes

lem-pc-affine-tilde-derived-tensor-mate: derived-category source iso and mate
factorization through the universal scalar-extension counit and the actual
coefficient-complex map. It includes the concrete definitions used by both parts.
The proof follows the common K-flat resolution and pinned-unit mate calculation.

lem-pc-affine-tilde-derived-tensor-homology-coordinates: homology normalization of
that raw arrow for any tensor model, without geometric mate assumptions. Its
proof follows exact-functor homology naturality and m.comparison_eq.

## Second reading by N4

1. **Statements and signatures.** I compared the item's Lean declaration byte for byte with
`sheaf-dag`; its hypotheses, lets, conclusion, and docstring are unchanged. The two split
node statements match their Lean declarations, including the ring maps, derived-category
objects, and homology degree. Verdict: unchanged and correctly attached.

2. **Proof and axioms.** All three delivered modules compile locally. The four definitions have
real constructions. The parent proof is a categorical composition reduction; the two remaining
`sorry`s are exactly the named split theorems. The axiom probe reports only the permitted axioms
plus `sorryAx` for those two open statements and the parent that depends on them. Verdict: clean
for the claimed decomposition.

3. **New statements and searches.** The derived mate statement is strictly before homology and
the coordinate statement is its fixed-degree homology calculation; neither renames the parent.
I checked Mathlib/source search, including `mapDerivedCategoryHomologyFunctorIso_hom_app_Q` and
`ShortComplex.mapHomologyIso_hom_naturality`; no existing declaration states either result.
Verdict: both splits are true, needed, and strictly simpler, with source docstrings and nodes.

4. **Pruning and route.** The only proof-only import added to the parent is the homology-coordinate
module, and it is plain `import`. The original affine resolution, pullback, acyclic pushforward,
and pinned-unit dependencies remain represented indirectly by the new derived mate node; none
was silently claimed pruned. The unit and its route are unchanged. Verdict: route preserved.

5. **DAG and report.** The parent node's proof and `proof_deps` now follow the two applications;
the new nodes record their declarations, sources, searches, chapter, and unit. This report names
the closed parent hole and both split holes and documents the decomposition. Verdict: metadata
agrees with Lean.

Changed in this second reading: corrected the two new node `lean.statement` fields to the
verbatim theorem signatures, expanded the dependency-routing note, and added this review.
