## What changed

Proved the body of `AlgebraicGeometry.Etale.isZero_higherDirectImage_constant_of_finite_submodules`
in `Sheaf.AlgebraicGeometry.SmoothBaseChange.ConstantFiniteSubmoduleVanishing`, with its signature
and existing docstring unchanged. The proof constructs the directed system of finitely generated
submodules using `Module.fgSystem`, its categorical colimit using `ModuleCat.directLimitIsColimit`,
and its equivalence with M using `Module.fgSystem.equiv`.

A proved private helper `finite_fg_submodule` restricts scalars to Z and applies
`Module.finite_of_fg_torsion`. The hypothesis's canonical lifted-integer action and the diagram's
inherited action are identified using `Int.cast_smul_eq_zsmul`. Constant sheafification and higher
image preserve the colimit; `IsColimit.isZero_pt` and the constructed equivalence finish the proof.
No data is chosen from a holed existence theorem. The zero module and n=1 need no special cases.

The higher-image preservation step at index universe u+1 is isolated in the new module
`Sheaf.AlgebraicGeometry.SmoothBaseChange.HigherDirectImageLargeFilteredColimit`. Its public theorem
`AlgebraicGeometry.Etale.preservesColimitsOfShape_higherDirectImage_large` concerns arbitrary
filtered sheaf diagrams and has no M, annihilator, finite-submodule or vanishing hypothesis.
It is strictly the colimit-continuity part of the argument, not a restatement of the item.
The item's proof-dependency imports and DAG proof are updated accordingly.

Both delivered modules compiled together in import order (10.7 and 21.8 seconds in the initial
successful run). All exploration files are under scratchpad and are not part of the delivery.
No existing interface changed and no forced adaptations are needed.

## Proved and sorry left

Closed the item's only direct hole:
`AlgebraicGeometry.Etale.isZero_higherDirectImage_constant_of_finite_submodules`
(node `lem-sbc-constant-finite-submodule-vanishing`). Its proof contains no sorry.
The private helper `finite_fg_submodule` is also proved.

Added one named public whole-proof sorry:
`AlgebraicGeometry.Etale.preservesColimitsOfShape_higherDirectImage_large`
(node `lem-sbc-higher-direct-image-large-filtered-colimit`). There are no other delivery holes,
no private sorry and no sorry in a definition. This is a decomposition: one upper hole closed,
one lower hole added, net zero before any import-closure pruning; it is not a fully discharged
vanishing theorem.

The new statement was checked on zero coefficients, empty schemes, singleton index categories,
degree zero and negative degrees. Its positive-degree argument is the finite-cover argument of
Stacks 0739 followed by the locally bijective comparison of 03Q8. Negative degrees give a zero
functor by nonnegativity of derived pushforward. There is no torsion restriction on the new
statement and no attempt to shrink the submodule index to Type 0.

## No longer needed

Removed these four original proof imports from the item:

- `WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafOver`: no localized-constant-sheaf
  comparison is used; constants preserve colimits through their existing left-adjoint instance.
- `WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.FilteredColimit`: its
  Type-0 preservation theorem does not accept the submodule index. The new coefficient-size
  preservation statement replaces it as the direct dependency. Its implementation was read
  as a model, but its theorem is not used in the delivered proof.
- `Sheaf.AlgebraicGeometry.EtaleCohomologyFilteredColimit`: the smaller-index theorem is not used.
  The new node's proof instead cites the existing larger-index theorem
  `lem-pbc-u2-sheafH-large-filtered-colimit-derived`.
- `Sheaf.AlgebraicGeometry.AbelianHigherDirectImagePresheaf`: its abstract abelian comparison is
  not used. The new node cites the existing canonical module-valued locally bijective comparison
  `sbc-lem-module-higher-image-raw-comparison-locally-bijective`.

Thus the item's original direct DAG dependencies `lem-weil-pbc-cohomology-filtered-colimit`,
`lemma-weil-pbc-direct-image-filtered-colimit`, and `sbc-lem-higher-direct-image-presheaf` are replaced
by the single new node. These are direct-route pruning claims; no claim is made that a removed
module is absent from every other target's import closure. The blueprint unit route through
cyclic coefficients and filtered finite submodules is retained.

## Where the brief, the DAG or earlier work was wrong

The DAG correctly warned that the source higher-image preservation interface only has a Type-0
index. Its suggested universe enlargement cannot be obtained by specializing that theorem.
An existing larger-universe abelian cohomology declaration was found and used during exploration:
`Scheme.etaleCohomology_isColimit_large_filtered`. The corresponding module-cohomology and
presheaf-evaluation helpers were made to compile in scratch experiments. The generic local-to-global
higher-image comparison remains isolated in the new node; I did not complete a usable Lean proof
of that bridge within the exploration budget.

The old source label for Tag 0739 says lemma-colimit; its actual label is
lemma-colim-works-over-collection. The new module records that label. The Stacks sources were read
at https://stacks.math.columbia.edu/tag/0739, https://stacks.math.columbia.edu/tag/03Q8 and
https://stacks.math.columbia.edu/tag/09Z1 because the literature source files are not installed
in this checkout. No existing docstring or mathematical statement was changed.

`tools/blueprint_refs.py ancestor lem-sbc-constant-finite-submodule-vanishing` reports a broken
created.item chain (None). The new node retains the item's explicit recorded ancestor
`sbc-lem-bc-universal-test`, with the item prepended to its existing via list, rather than
inventing a new ancestor. This is a metadata issue for the maintainer, not a change of unit route.

## New nodes

`lem-sbc-higher-direct-image-large-filtered-colimit`, in
`dag/nodes/sec-smooth-base-change/lem-sbc-higher-direct-image-large-filtered-colimit.json`, is the
single remaining continuity step. It is stated in
`lean/Sheaf/AlgebraicGeometry/SmoothBaseChange/HigherDirectImageLargeFilteredColimit.lean` as
`AlgebraicGeometry.Etale.preservesColimitsOfShape_higherDirectImage_large`. Its docstring and node
contain the complete affine-local cohomology and local-bijection proof, citing the existing
large-index cohomology, coefficient-forgetting, free-sheaf comparison and canonical module
presheaf-comparison nodes. The three search kinds were run and logged; LeanSearch was unavailable,
LeanFinder found general colimit infrastructure only, and Mathlib grep found no match. A search
of the entire imported blueprint found the existing smaller-interface filtered-colimit node
but no coefficient-size realization. No change record is needed: existing signatures and
visibility remain unchanged, and this delivery only adds an independent theorem module.

## Second reading by U2

1. Interface preservation: compared the delivered item with the repository using diff.
   The existing theorem signature and docstring are byte-for-byte unchanged. Only proof,
   proof-only imports, and the proved private helper were added. No definition or target
   statement changed; no change record or forced adaptation is required. Verdict: pass.
2. Kernel and holes: compiled both delivered modules in import order. A scratch copy
   with `#print axioms` reports only `propext`, `Classical.choice`, `Quot.sound`, and
   `sorryAx` for the item and the open continuity theorem. The private finiteness helper
   uses only the three allowed axioms. The only delivered sorry is the named whole-proof
   continuity theorem listed above. No forbidden declarations or hollow definitions occur.
   Verdict: pass as a decomposition, not an axiom-free vanishing proof.
3. Split statement: independently read Stacks Tags 0739, 03Q8 and 09Z1 and the recorded
   dependency declarations. The affine-local cohomology comparison proves continuity for
   arbitrary filtered module-sheaf diagrams at coefficient size. This is the continuity
   portion of the argument, strictly distinct from finite-submodule vanishing. Checked
   zero ring, empty schemes, identity morphism, singleton diagrams, degree zero and
   negative degrees; no missing torsion hypothesis or size restriction is needed.
   Repeated LeanFinder with "etale derived pushforward commutes with directed colimits
   of module sheaves on quasi compact quasi separated schemes" (eight unrelated module
   pushforward/colimit infrastructure hits), and Mathlib grep for derived directed/filtered
   continuity (no hits). Read the upstream and repository FilteredColimit declarations:
   their index is Type 0 and they do not specialize to this statement. The existing
   large-index cohomology result supplies only the affine-local portion. Verdict: pass;
   no short existing theorem closes this hole. The scratch full-proof experiment times out
   at 60 seconds and is not delivered or used as evidence of a completed proof.
4. Route and pruning: read Module.fgSystem, the finite torsion argument, the action
   identification, zero-colimit argument, and transport along the actual linear equivalence.
   The construction uses no arbitrary witness of a holed existence theorem. The four
   original direct imports and all three original direct proof dependencies removed from
   the item are listed under No longer needed. The blueprint universal-datum unit and its
   realized fields are unchanged; finite-submodule and cyclic-coefficient reduction remain
   the route. Restored the new hole's planned dependency imports as described below.
   Verdict: pass; pruning assertions refer to the item's direct route, not global closure.
5. DAG agreement: compared the existing node with its repository version: only proof,
   proof_deps and proof_origin changed. Its four steps match the actual Lean reduction.
   The new node has its source, full proof plan, exact Lean statement, searches, provenance,
   blueprint ancestry, chapter and unit; proof_deps is precisely the union of step uses.
   Read each dependency's actual statement. Verdict: pass after restoring its plan imports.

Second-reading changes: added five plain proof-dependency imports to
HigherDirectImageLargeFilteredColimit: Curve.EtaleSheafHLargeFilteredColimit,
EtaleModuleCohomologyForget, EtaleFreeSheafDerivedSections, EtaleInverseImageColimits,
and the source HigherDirectImage.CohomologyPresheaf module. These are the Lean modules
of the new node's non-Mathlib proof dependencies; they make the open theorem's imported
plan agree with its DAG and docstring. No proof or signature was rewritten. No extra hole
was added or closed by the second reading. Existing open holes in imported dependencies
remain existing holes and are not claimed as newly proved. The added imports are private
because none is required by the public statement. Mathlib leaves are already available
through these imports. All delivery files were compiled again after this repair.
