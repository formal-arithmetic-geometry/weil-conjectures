## What changed

Proved `AlgebraicGeometry.dim_base_change` without changing its statement. The affine
clause follows from the existing topological dimension theorem, spectrum dimension,
and tensor symmetry. The curve clause now computes both dimensions using matching
affine covers, rewrites the chart dimensions by the affine clause, and applies the
curve's dimension field. Added `Sheaf.AlgebraicGeometry.FieldBaseChangeAffineCovers`
to isolate only the geometric chart construction and nonemptiness argument.

## Proved and sorry left

`AlgebraicGeometry.dim_base_change` and its private helper `ring_dim_base_change`
compile without sorry. The delivery adds one remaining sorry:
`AlgebraicGeometry.exists_field_baseChange_affine_covers`, node
`lem-pc-dim-base-change-affine-covers`. Its statement contains no dimension conclusion
and applies to any nonempty locally finite type scheme over a field. The imported
`topologicalKrullDim_spec_tensorProduct_of_field_extension` and
`Scheme.dim_eq_iSup_ringKrullDim_of_affineOpenCover` remain existing proof dependencies.

## No longer needed

Removed the direct proof import `Sheaf.AlgebraicGeometry.BaseChangeConventions`.
Its node `def-pc-base-change` remains needed by the new cover lemma; no original
geometric plan node is globally pruned. The original direct proof dependencies
`def-weil-finite-type-morphism`, `def-weil-pbc-finite-type-algebra`,
`def-pc-base-change`, `lem-weil-pbc-open-fibre-product`, and
`lem-weil-pbc-fibre-product-affine-spectra` move behind the new cover lemma.
`def-weil-pbc-krull-dimension-ring` remains needed, and the explicit spectrum/ring
dimension rewrite additionally uses `lem-weil-pbc-spec-topological-krull-dimension-ring`. The affine-cover dimension import is retained
and used. The original field-extension dimension import is retained and used.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement was changed. The affine spectrum's carrier is definitionally
PrimeSpectrum, but rewriting the spectrum dimension requires an explicit `change`
before applying `PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim`.
The planned chart construction was not supplied as a usable bundled declaration;
the new lemma provides this strict substep. Its edge cases include zero chart rings;
the nonempty assumption concerns X, not each chart. It needs local finite type only,
not integrality, separatedness, quasi-compactness, or a dimension assumption.

## New nodes

`lem-pc-dim-base-change-affine-covers` is the affine-cover construction from paragraph 2
of the existing blueprint argument, using Stacks Tags 01JR, 01JQ and 01T0. It provides
matching covers and pullback nonemptiness, and leaves the actual dimension calculation
to the fully written Lean proof in the original module. The original node's proof,
proof dependencies and origin now match that proof. The unit route is preserved.

## Second reading by A2

1. Compared the original module against the repository with diff: the existing
   theorem signature and all existing definitions are byte for byte unchanged.
   The added module states only a geometric chart substep. No change record is needed.
2. Both delivered modules compiled locally, without errors or warnings. There is
   exactly one direct sorry, the reported public cover theorem. No forbidden
   declarations or hollow definitions occur. Axiom checks are recorded below.
3. Checked the cover lemma for K = k, affine X, disconnected X, an infinite cover,
   and zero chart rings. The hypothesis Nonempty X excludes the empty scheme;
   tensoring with a field extension is faithful and hence does not empty X.
   Neither integrality nor quasi-compactness is needed. The lemma has no dimension
   assertion and is a strict part of the original argument, not a restatement.
   Read Stacks 01JR, 01JQ and 01T0: they give open pullbacks, tensor-product affine
   pullbacks, and finite type coordinate rings. Independent leanfinder, loogle,
   grep and repository searches found ingredients, but no bundled theorem.
   Formalizing the cover construction requires substantial scheme API work, so
   its named sorry is retained.
4. Read the proof from the target downward: tensor symmetry and the existing
   dimension theorem prove the affine clause; the cover and supremum lemmas
   prove the curve clause. All three proof imports are used; the public imports
   support the unchanged signature. The No longer needed section now explicitly
   accounts for every old dependency moved behind the cover lemma. The unit
   sk-thm-picard-rr has empty realized entries, and this reduction preserves the
   original affine-cover route without bypassing a realized step.
5. Compared both node records with the Lean declarations and the old proof plan.
   The original statement and statement dependencies are unchanged. Added the
   ring-dimension definition and the exact Mathlib spectrum-dimension node to the
   proof dependencies; corrected the new node's finite-type source tag and
   replaced dimension searches by searches for the actual chart construction.

Changes by this reader: only report and DAG metadata corrections; no Lean proof
or signature changes.

Scratch-copy #print axioms checks passed for ring_dim_base_change, dim_base_change,
and exists_field_baseChange_affine_covers: each uses only propext, Classical.choice,
Quot.sound, and sorryAx. The sorryAx in the written reduction comes from the
reported new cover lemma and the existing open dimension dependencies. This
is a partial reduction, not an axiom-free completion of the target.

The first dry run required a LeanSearch-kind record in addition to LeanFinder,
Loogle and grep. Ran the chart-construction query: LeanSearch returned Internal
Server Error; recorded that unavailability without inventing a search verdict.
The other three searches succeeded.
