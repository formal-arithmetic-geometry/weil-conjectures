## What changed

Reduced `AlgebraicGeometry.exists_affineBaseChangeSourceModel` to the affine
calculation on a termwise tilde K-flat module complex, and representative
independence of the source-only stalk comparison. The assembly constructs a
module representative through the affine derived equivalence, maps the actual
functorial flat-resolution augmentation isomorphism through the module-derived
equivalence, proves that tilde of the resolution is K-flat, obtains the invertible universal pullback counit, and
composes the local additive equivalences. It does not assume that the supplied
sheaf complex P is termwise quasi-coherent.

The affine equivalence is used with its specified natural comparison with
termwise tilde; all chosen representatives are pinned by derived isomorphisms.
No arbitrary object is selected from an unproved mere-existence assertion.

The source-only definition is relocated to a publicly re-exported support module
so that the two new dependencies can mention it without an import cycle. Its
morphism type is explicitly annotated with the same inferred source and target,
avoiding reduction of its long composite during source-carrier inference.
See `coord/changes/affineBaseChangeIntoPullback-location.md`.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.exists_affineBaseChangeSourceModel`
(node `lem-pc-affine-base-change-source-model`). There is no sorry in the item.

Added exactly two holes, each in a public theorem whose body is `by sorry`:

- `AlgebraicGeometry.exists_affineBaseChangeTildeSourceModel`
  (`lem-pc-affine-base-change-tilde-source-model`). This computes the comparison
  for a genuine termwise tilde of a module K-flat complex. It does not cover
  arbitrary sheaf representatives, which is handled separately.
- `AlgebraicGeometry.exists_affineBaseChangeIntoPullback_representativeIso`
  (`lem-pc-affine-base-change-source-representative-iso`). This identifies the
  source-only stalk comparisons of two K-flat representatives on arbitrary
  schemes. It asserts no global module source or affine direct-image model.

This is a decomposition, not a completed sorry-free proof: one hole closed and
two added, with net minus one before any closure pruning. The item still depends
on existing named open results through the imported library.

## No longer needed

Removed the item's direct proof import of
`Sheaf.Algebra.Homology.AffineDerivedBaseChangeComparison`: the module calculation
now belongs to the tilde-computation node. Its comparison/localization node is
still needed there; it is not claimed pruned from the mathematical argument.

Replaced the item's proof import
`Sheaf.AlgebraicGeometry.AffineQCohDerivedEquivalence` with
`Sheaf.AlgebraicGeometry.AffineQCohDerivedEquivalenceCore`; the representative
construction does not need the shift-normalization conclusion.
The core node `new-affine-qcoh-derived-equivalence-core` is used directly.

Removed the item's proof import
`Sheaf.AlgebraicGeometry.AffineDerivedPullbackTensorTilde`, replacing it with the
smaller `Sheaf.AlgebraicGeometry.Modules.IsKFlatTilde` interface and the proved
module K-flat acyclicity criterion. The open-restriction and derived-tensor
formulas in that large module are unused by the assembly. The affine pullback
formula remains needed in the new tilde-computation node's planned proof.

The former public SingleComplexBaseChangeStalkCondition import is retained
transitively through the new public support module, and imported with `all` for
the existing proved counit helper. No mathematical dependency or unit realization
is claimed globally pruned; the unit's realized statement/steps are empty and
are unchanged.

The old direct `proof_deps` no longer used by the assembly are
`def-pc-base-derived-tensor-cohomology-model`,
`def-pc-derived-base-change-map`,
`lem-pc-affine-derived-base-change-comparison-map`,
`lem-pc-affine-derived-cohomology-presentation`,
`lem-pc-affine-derived-pullback-tensor-tilde`,
`lem-pc-affine-qcoh-derived-equivalence`,
`lem-weil-pbc-localization-module-exact`, and
`lem-weil-pbc-spec-tilde-stalk-localization`.
Statement dependencies and dependencies used in the lower computation nodes
remain; this list records direct proof-dependency removal, not global pruning.

## Where the brief, the DAG or earlier work was wrong

The existing ring comparison statements do not by themselves identify the
scheme-derived mate and its source-only localized stalk map. The DAG described
those identifications in prose; the new nodes isolate the two missing interfaces.
No statement is disputed or weakened. The large affine-pullback module and full
affine-equivalence shift clause are unnecessary for the representative assembly.

The source text is not present under literature in this clone. Consulted the
official Stacks pages for Tags 0DJ8, 06Z0, 06Y6, 08DV and 08IB. Search through the supplied
msearch tooling used LeanFinder, Loogle, grep, and LeanSearch. LeanSearch returned
Internal Server Error, recorded as unavailable without a no-match verdict.

## New nodes

`def-pc-affine-base-change-into-pullback` records the relocated existing definition
in `Sheaf.Algebra.Homology.AffineBaseChangeIntoPullback`. Its data are unchanged;
there is no new existence choice or sorry.

`lem-pc-affine-base-change-tilde-source-model` records the affine module-resolution
calculation in `Sheaf.Algebra.Homology.AffineBaseChangeTildeSourceModel`. Checked
zero complexes, zero rings (prime assertions then vacuous), identity maps and
unbounded degrees: no additional flatness, boundedness or Tor-independence
assumption is needed.

`lem-pc-affine-base-change-source-representative-iso` records representative
transport in `Sheaf.Algebra.Homology.AffineBaseChangeSourceRepresentativeIso`.
For identical representatives the identity satisfies the equation; zero complexes
and all degrees are included. Neither representative must have quasi-coherent
terms. The action compatibility follows from cohomologyIso_smul, not an assumed
arbitrary linear equivalence.

Change record: `coord/changes/affineBaseChangeIntoPullback-location.md`.

Validation: the complete assembly compiled using lcompile.py. The delivery dry
run is the final check; no library build, push or delivery was performed.

## Second reading by V3

1. Compared the delivered module with the repository version. The existing declaration signature and all unchanged declarations are byte-for-byte preserved; the source-only definition relocation is recorded in the change record. Verdict: pass.
2. Compiled all four delivered modules with `lcompile.py --all`. The item has no sorry, and the only remaining sorries are the two named split-off public theorems, each with a matching DAG node; no forbidden commands or hollow definitions were found. Verdict: pass.
3. Checked the split-off statements against their docstrings, edge cases, and repository search results. Both are strictly narrower interfaces needed by the assembly and introduce no weakened target statement or duplicate library declaration. Verdict: pass.
4. Reviewed the proof route and imports. The assembly uses the affine core equivalence, explicit flat resolution, tilde K-flatness, the tilde source-model reduction, and representative transport. Removed imports are listed above; the unit route and realized records are unchanged. Verdict: pass.
5. Checked DAG `proof`, `proof_deps`, `proof_origin`, Lean records, and the relocation change record against the code. They agree with the delivered route and identify both added holes. Verdict: pass.

Changed during second reading: no Lean proof or statement changes; added this review section and completed the explicit old proof-dependency removal list. Validation completed with the sandbox full compile.

Independent search additionally inspected `StalkComparisonSourceTransport`,
`StalkComparisonPullbackNaturality`, and `StalkComparisonCoordinateInvariance`.
They provide the tensor-algebra source transport and naturality into derived
stalk cohomology. The new representative theorem requires the distinct
`affineRepresentativeStalkIso` identification with stalks of sheaf cohomology;
they do not directly give its displayed equation. These proved ingredients
should be used when closing that lower hole. LeanFinder returned only flatness
and tensor lemmas for the new representative-independence query; Loogle found no
identifier for the attempted uniqueness query. Independently read official
Stacks Tags 0DJ8 and 06Y6: the affine module localization calculation and
independence of derived tensor choices support the two split statements.
