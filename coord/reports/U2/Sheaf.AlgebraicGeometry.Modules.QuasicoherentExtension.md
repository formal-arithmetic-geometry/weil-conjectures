## What changed

Proved AlgebraicGeometry.Scheme.Modules.isQuasicoherent_of_shortExact from one
strictly smaller affine lifting statement. Added the proof-only imports
Sheaf.AlgebraicGeometry.Modules.AffineExtensionSectionSurjectivity,
WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel and
Mathlib.CategoryTheory.Preadditive.LeftExact. Existing public imports and all
existing public signatures are unchanged.

The proof restricts to the affine cover, uses left exactness of global sections
and the lifting statement to get a short exact sequence of section modules,
proves that tilde preserves kernels using the already proved quasi-coherent
kernel theorem, and applies Mathlib's short-complex five lemma to the counit.
The affine presentations then give global quasi-coherence. The private kernel
preservation proof adapts the existing proof pattern from
Sheaf.AlgebraicGeometry.AffineDerivedTildeHomologyComparison; that module's
private helper cannot be imported and using its derived theorem would add
irrelevant derived-category dependencies.

The proof and proof dependencies of lem-pc-quasi-coherent-extension were updated
to match this route. The unit's realized lists are empty, and its route is
preserved: only the auxiliary affine comparison argument was shortened.

## Proved and sorry left

Closed the original hole in
AlgebraicGeometry.Scheme.Modules.isQuasicoherent_of_shortExact
(lem-pc-quasi-coherent-extension). Added exactly one hole:
AlgebraicGeometry.Scheme.Modules.epi_globalSections_of_shortExact
(lem-pc-affine-extension-section-surjectivity), in the new module
Sheaf.AlgebraicGeometry.Modules.AffineExtensionSectionSurjectivity.
This is a decomposition, not a net hole reduction: one closed, one added.
The original module has no remaining sorry. Its private tilde_preservesKernel
helper is fully proved. The new theorem only asserts surjectivity on global
sections and says nothing about quasi-coherence of the middle term.

Both modules compile with lcompile.py in import order. The new statement was
checked against Stacks Schemes lemma-extension-quasi-coherent, especially the
ideal argument and finite principal-open gluing. Zero ring, zero kernel and
zero quotient are covered. No data is chosen from an unproved theorem.

## No longer needed

No original import was removed. Every original proof dependency remains used.
No DAG node or module can be pruned by this delivery. The repeated application
of the lifting argument on each principal open and a separate basis-wise
isomorphism proof are unnecessary: exactness of tilde and the categorical
five lemma give the counit isomorphism directly. These were prose steps with
no separate node to remove. The derived comparison module is not imported.

## Where the brief, the DAG or earlier work was wrong

No statement error found. The original DAG has no stated node for the
substantive affine lifting argument, so it cannot be completed by applying its
listed dependencies alone. The delivery isolates precisely that step. The
existing source-library kernel theorem supplies a shorter proof of exactness
of tilde than proving the counit isomorphism componentwise on a basis.

Mathlib searches were run through msearch.py and recorded in searches.jsonl.
LeanSearch returned Internal Server Error, recorded as unavailable; Loogle
and grep did not find the lifting theorem. LeanFinder returned generic
presheaf surjectivity and sheaf generating-section results, which do not
assert global surjectivity for sheaf epimorphisms. Source-library searches
found kernel, cokernel and affine presentation results but no global lifting.
Blueprint search for extension quasi coherent returned no matching unit node.

## New nodes

lem-pc-affine-extension-section-surjectivity is the surjectivity part of the
affine principal-open proof of Stacks Tag 01IE. Its module is
lean/Sheaf/AlgebraicGeometry/Modules/AffineExtensionSectionSurjectivity.lean.
The node records the ideal argument, correction of lifts on D(f) union D(g),
finite gluing after killing overlap differences, and the unit-ideal argument.
It is strictly part of the original proof and is combined with fully proved
kernel preservation, counit comparison, five lemma and locality.
No change record is required: existing public interfaces are unchanged.

## Second reading by U2

1. Compared both delivered modules against the repository version. Existing theorem signatures and definitions are unchanged; only proof-only imports and proofs were added. Verdict: pass.
2. Compiled both modules with lcompile.py in import order. The original theorem has no `sorry`; the affine global-sections theorem is the single named split-off `sorry`, with no axioms or forbidden declarations. Verdict: pass.
3. Reviewed the split-off statement and node. It is a strictly smaller affine surjectivity assertion, mathematically true by the cited Stacks 01IE ideal/principal-open argument, and its statement is not duplicated in the library or Mathlib. Verdict: pass.
4. Checked the proof route and imports against the DAG. The affine lifting node is used, kernel preservation follows from the existing quasi-coherent kernel theorem, and the five-lemma route preserves the unit's affine-cover plan. No removable original import or proof dependency was found. Verdict: pass.
5. Checked node metadata, proof dependencies, proof origin, and the realized route. They agree with the Lean proof and the split-off theorem's docstring gives the complete source argument. Verdict: pass.

Changed after second reading: no mathematical or statement changes; this section records the review.
