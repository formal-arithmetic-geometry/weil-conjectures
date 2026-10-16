## What changed

Proved `AlgebraicGeometry.ProEtale.condensed_qcqs_globalSections_continuity` with
its existing signature unchanged. The relative pushforward, naturality, shifts,
and representative proofs retain their existing signatures and proof bodies.

The proof uses the landed abelian hypercover total, its canonical augmentation,
the proved internal-module injective row, and the existing bounded-below row and
column comparisons. Forgetting the internal action preserves the required
quasi-isomorphisms and colimits. A private categorical lemma transports this
natural computation through the original truncated-colimit cocone, proving
invertibility of the original canonical comparison.

Added `Sheaf.CategoryTheory.DerivedCategory.BoundedBelowSectionModel`, a generic
natural comparison of an augmented bounded-below complex model with the actual
K-injective right derived functor. Its injective resolutions come from Mathlib's
proved existence theorem; no data comes from an unproved existence statement.
Naturality uses resolution lifts up to homotopy and the existing
`AlgebraicGeometry.Scheme.ProEt.map_eq_of_boundedBelow_homotopy`.

Repaired the landing-tool return at head `a31e90445`: removed the duplicate
private `CategoryTheory.Functor.map_eq_of_boundedBelow_homotopy`, replaced
both call sites with the existing theorem, and privately imported its module.
The new section-model node now records that dependency. The retained item
proof was compared with the current shared source; no newer item changes
needed merging. The required dry run rebases the delivery onto current main.

Repaired reviewer X-fbc38 point B5: the new bounded-below section-model node's
`source.document` and `proof_origin.document` both cite
`literature/stacks-project/proetale.tex`, where Tag 09A2
(`proetale-lemma-compute-cohomology`) is located.

All new proof dependencies are private imports. Existing public imports and all
existing declaration signatures are unchanged. No existing dependency interface
or target definition changes; no change record or forced adaptation is needed.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.ProEtale.condensed_qcqs_globalSections_continuity`.
Added zero holes. There are no remaining `sorry`s in either delivered module.
This closes 1 of 1 original holes, rather than decomposing it into new holes.

The one new node `lem-weil-pbc-bounded-below-section-model` is proved by
`CategoryTheory.Functor.boundedBelow_sectionModel`. Its construction uses proved
bounded-below injective resolutions and the derived unit.

## No longer needed

Removed item proof imports:

- `Sheaf.Algebra.Homology.BoundedBelowInjectiveResolution`;
- `Sheaf.AlgebraicGeometry.ProEtaleHypercoverComputesBoundedComplex` as a direct
  item import; it is retained through the section-model module because its
  existing homotopy theorem is used;
- `Sheaf.AlgebraicGeometry.ProEtaleWeaklyContractibleEvaluationColimits`;
- `Sheaf.CategoryTheory.RingedSiteGrothendieckAbelian`.

The exact old `proof_deps` removed from the parent node are:
`def-weil-pbc-proetale-operations`, `def-weil-pbc-scheme-conventions`,
`lem-pur-ringed-site-grothendieck-abelian`, `lem-sc-bounded-below-injective-resolution`,
`lem-weil-pbc-kinjective-hom-derived`,
`lem-weil-pbc-proetale-hypercover-computes-bounded-complex`,
`lem-weil-pbc-proetale-wcontractible-affine-evaluation-colimits`,
`lem-weil-pbc-qcqs-over-affine`, and
`lem-weil-pbc-ring-modules-grothendieck-abelian`.
The hypercover-computation node remains a proof dependency of the new
section-model node for its existing generic homotopy theorem; it is not
claimed pruned. Removed `Mathlib.Algebra.Homology.HomotopyCofiber` from the
new section-model module along with its duplicate cylinder proof.
The two definition nodes remain statement dependencies. These results may still
be used elsewhere; no existing module is claimed globally pruned.

Second reading omitted the proposed internal free resolution, tensor/free
construction, separate internal hypercover total and augmentation, separate
injective row, and duplicate row/column comparisons. The existing proved abelian
and internal-module declarations suffice. Their proposed new nodes and modules
are absent from this delivery. The finite-cone universe change and its change
record are also omitted because the final proof does not need them.

## Where the brief, the DAG or earlier work was wrong

The old plan's external ringed-module computation did not directly apply to
internal modules over the condensed ring object. The current library has since
proved the internal-module injective-row theorem and the required abelian
hypercover constructions. Reusing those declarations avoids rebuilding a free
resolution or changing the finite-cone module's universes.

The returned delivery copied an existing bounded-below homotopy theorem
word for word. Its existing public declaration is usable with exactly the
same binders, so the copy has been removed rather than generalized.

The parent node's proof, `proof_deps`, and `proof_origin` now describe this actual
route. The unit's statement and realized steps remain unchanged.

## New nodes

`lem-weil-pbc-bounded-below-section-model`, in
`Sheaf.CategoryTheory.DerivedCategory.BoundedBelowSectionModel`: an augmented
complex model inverting bounded-below quasi-isomorphisms and computing injective
complexes computes the actual derived functor naturally on every fixed strict
lower bound. The source is Stacks Project, `proetale.tex`, Tag 09A2. There are no
change records.

## Second reading by D3

1. **Signatures and accidental changes: pass.** I diffed the delivered item and
   node against the repository. Existing declaration signatures are unchanged;
   the only existing proof change is the body of
   `condensed_qcqs_globalSections_continuity`. The added imports are private, and
   the second delivered module and node are new. No dependency module was edited.

2. **Proof and axioms: pass.** Both modules compile with `lcompile.py` and contain
   no `sorry`, forbidden declarations, or hollow definitions. The bounded-below
   model uses Mathlib's proved injective-resolution existence theorem. The
   delivery probe and the scratch axiom file check the relevant declarations,
   whose only allowed axioms are `propext`, `Classical.choice`, and `Quot.sound`.

3. **Split statements: pass.** The sole new node is the generic intermediate
   theorem `CategoryTheory.Functor.boundedBelow_sectionModel`. Its statement is
   strictly stronger than the local application in generality while remaining
   exactly the needed comparison: it has no site-specific continuity conclusion
   and introduces no open split statements. Its docstring gives the resolution,
   augmentation, and bounded-below homotopy proof, and its source and search
   records are present.

4. **Route and pruning: pass.** The proof uses the existing affine
   weakly-contractible hypercover, abelian total and augmentation, internal
   injective-row theorem, row and column comparisons, and the new section model.
   The unit's realized route remains intact. Removed imports and old proof
   dependencies are listed above; the hypercover computation remains a
   dependency of the new node because its bounded-below homotopy theorem is used.

5. **DAG agreement: pass.** The parent node's proof steps and dependency union
   match the Lean proof, and the new node records its statement, source,
   proof-origin, searches, creation metadata, and Lean declaration. No statement
   or definition change record is needed.

I changed the global-sections proof to reuse the landed hypercover library,
removed redundant proposed constructions and imports, corrected the new node's
source citation, and updated the parent proof metadata. No holes were added.
