## What changed

Completed `AlgebraicGeometry.Scheme.affineLineProjection_stalk_bound` without changing its
signature or any existing definition. Its original single hole is replaced by a complete
proof using all six supplied hypotheses. The case q=2 uses a separably closed field model
of the generic strict localization and the already proved source-library affine-curve
bound. The case q>2 uses the projective-line compactification, the explicit infinity
coordinate, the supplied Cartier and stalk bounds, closed support, and Leray.

Added two proved modules, one public theorem per module:

- `Sheaf.AlgebraicGeometry.Sites.PolynomialGenericStrictLocalizationField` proves
  `AlgebraicGeometry.Scheme.polynomial_generic_strictLocalization_field`.
- `Sheaf.AlgebraicGeometry.Sites.AffineLineInfinityStrictLocalModel` proves
  `AlgebraicGeometry.Scheme.affineLine_infinity_strictLocal_model`.

The first helper applies the existing smooth strict-local model, then proves that its
zero-dimensional reduced local ring is its separably closed residue field. The second
constructs the infinity coordinate from the affine chart ring, proves nonvanishing by
flatness of the ind-etale chart map, identifies the principal open by equal ranges of
open immersions, and proves the residue transcendence-degree assertions from existing
closed-irreducible dimension and closed-immersion residue-field results.

The item proof and both helper modules still compile with the same target signatures. This
repair removes the private `rightDerived_openImmersion_supported` theorem, whose statement
duplicated the same theorem in the source-library affine torsion cohomological-dimension
module. Its short proof is now inlined at the sole call site using
`Etale.mem_essImage_lowerStar_of_isZero_upperStar` and the existing derived-object
isomorphisms. The residue-map comparison is now local to the generic proof and private in the infinity
module; no extra public theorem is exposed. No other existing module is adapted.

## Proved and sorry left

Closed: `AlgebraicGeometry.Scheme.affineLineProjection_stalk_bound` (1 of 1 original holes).

Also proved, with no new holes:
`AlgebraicGeometry.Scheme.polynomial_generic_strictLocalization_field` and
`AlgebraicGeometry.Scheme.affineLine_infinity_strictLocal_model`.

There are no `sorry` declarations in any delivered Lean module. No holes were split off.
The proofs use existing stated results, including
`AlgebraicGeometry.Scheme.smooth_strict_local_field_model`,
`AlgebraicGeometry.finite_trdeg_residueField`, and
`AlgebraicGeometry.topologicalKrullDim_closed_irreducible_eq_trdeg`; their existing holes
are unchanged. These are the established planned dependencies, not newly added obligations.

Validation: all three modules compiled in sandbox import order. The original item signature
was compared textually and is unchanged. The geometric arguments include m=0/n=0 and
nonclosed base points. For the field-extension step, a conservative singleton geometric
point over the one-point spectrum suffices. No purely inseparable-equivalence theorem is
needed. Final validation is the required `deliver3.py --no-push` dry run.

## No longer needed

The private helper `rightDerived_openImmersion_supported` is no longer a declaration: its
proof is inlined from the existing public support theorem, removing a duplicate statement
already present in the source-library module.

The returned delivery was refused because this module declared a private
`rightDerived_openImmersion_supported` theorem whose statement duplicated the same
statement in `WeilConjectures.AlgebraicGeometry.Sites.AffineTorsionCohomologicalDimension`.
The duplicate declaration is removed; the proof is inlined at its call site from the
existing public support theorem and derived isomorphisms. No module is withdrawn. The
following planned
proof dependencies are removed from this item's DAG route; this does not claim that other
project branches stop using them:

- `lemma-weil-pbc-finite-stalk-formula`, module
  `WeilConjectures.SixFunctors.Finite.Stalk`: replaced by the closed-support representation,
  the closed immersion counit, and g i=id.
- `lem-weil-pbc-etale-restriction-injectives`, module
  `WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMap`: exact restriction commutes with
  derived objects; restriction need not be shown to preserve injectives here.
- `thm-sp-grothendieck`, module `Sheaf.CategoryTheory.GrothendieckSpectralSequence`:
  the supplied hLeray already gives diagonal vanishing. No spectral sequence is constructed.
- `lem-weil-pbc-direct-image-preserves-injectives`, module
  `WeilConjectures.SixFunctors.BaseChange.DerivedPasting.Vertical`: not needed for the
  postcomposition-with-exact-functor derived comparison used here.
- `lem-sc-arbitrary-curve-cd`, module
  `Sheaf.AlgebraicGeometry.Sites.ArbitraryCurveCohomologicalDimension`: use the existing
  proved source-library theorem
  `AlgebraicGeometry.IsCurve.hasTorsionCohomologicalDimensionLE_of_isSepClosed` in
  `WeilConjectures.AlgebraicGeometry.Curve.TorsionCohomologicalDimension` directly.

Other removed direct proof edges are retained where genuinely needed below the new helpers:
`lem-sc-smooth-strict-local-field-model` is used by the generic helper;
`lem-weil-pbc-finite-type-domain-dimension-trdeg` remains below the existing
closed-irreducible dimension theorem. Their modules are not claimed as globally pruned.
`def-kun-transcendence-degree` and `def-weil-pbc-inverse-image` remain statement dependencies.

The infinity helper no longer imports the generic-field module merely for a residue-map
comparison. Its scalar-map comparison is private, the generic proof performs the same
calculation locally, and the existing `Scheme.Hom.residueFieldAlgebraMap_comp` is used
from the proof-only import `WeilConjectures.PointCount`.

For completeness, every removed direct import of the original item is:
`Sheaf.AlgebraicGeometry.Sites.ArbitraryCurveCohomologicalDimension`,
`Sheaf.AlgebraicGeometry.Sites.CohomologicalDimension`,
`Sheaf.AlgebraicGeometry.SmoothStrictLocalFieldModel`,
`Sheaf.CategoryTheory.GrothendieckSpectralSequence`,
`Sheaf.RingTheory.FiniteTypeDomainDimensionTrdeg`,
`WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth`,
`WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint`,
`WeilConjectures.SixFunctors.BaseChange.DerivedPasting.Vertical`,
`WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMap`,
`WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`,
`WeilConjectures.SixFunctors.Etale.UpperLowerStar.Stalk`, and
`WeilConjectures.SixFunctors.Finite.Stalk`.
Their required statement declarations remain available through the retained public
imports; proof dependencies used below the new helpers remain there. No claim of
whole-library unreachability or module withdrawal is made.

## Where the brief, the DAG or earlier work was wrong

An earlier delivery report discussed a first-reader gate for the second-reading section.
This repair keeps the existing second-reading record; the current returned-delivery issue
was the duplicate helper described above and has been fixed. The required dry run now
passes.

No statement was false, and no target or existing interface changed. The plan's finite-stalk
formula and purely inseparable equivalence are stronger machinery than this proof needs.
Closed-support adjunctions and the conservative singleton geometric point suffice.
The infinity coordinate only needs flatness to remain regular and nonzero; it does not need
the smooth strict-local coefficient-field model. That model is still needed for degree two.

The blueprint unit `sk-prop-sf-cbc` has no realized statement/step attachments to bypass;
the compactification, boundary calculation, Leray, and generic-point argument are all kept.
The source files named by the original node are not present in this checkout; its complete
proof and the existing source-library chart formulas specify the argument used here.

## New nodes

`lem-sc-polynomial-generic-strict-localization-field` attaches the proved generic-point
field model. Its proof uses the existing finite residue transcendence degree, smooth
strict-local model, local structure, and Mathlib's zero-dimensional local-ring criterion.
No new obligation remains in this node.

`lem-sc-affine-line-infinity-strict-local-model` attaches the proved infinity-chart local
geometry. Its proof constructs the chart map and coordinate, derives flatness from the
existing ind-etale presentation, and uses the two-chart formula to construct the open
isomorphism. No new obligation remains in this node.

Both node records include self-contained statements, complete proof steps, dependencies,
source attribution, verbatim Lean statements, and the Mathlib search records (LeanSearch was attempted and returned an Internal Server
Error; LeanFinder, Loogle, and source grep were also run). Whole
blueprint searches for the generic strict localization and strict localization at infinity
found no duplicate helper statement. No change record is needed: no existing signature or
definition changes.

## Earlier second reading (a previous round; superseded)

1. Compared the delivered item with the repository version using `diff`. The target
   declaration's signature and all existing definitions are unchanged; only proof imports,
   the proof, DAG proof metadata, and the two new helper modules/nodes were added. Verdict:
   pass.
2. Compiled all three delivered modules with `lcompile.py --all` and checked their theorem
   axioms. They contain no `sorry`, forbidden declaration form, or hollow definition; the
   only `sorryAx` dependencies come from the already open imported library theorems. Verdict:
   pass.
3. Read both helper statements, docstrings, and nodes against their uses. The generic
   strict-localization statement is exactly the field model needed in degree two, and the
   infinity statement is exactly the principal-open and residue-degree data needed by the
   Cartier step. Both cover the zero-dimensional cases and add no hypotheses to the target.
   The earlier duplicate was found by the delivery checker and is now removed; repository
search confirms the infinity helper uses the shared polynomial theorem. Verdict:
   pass.
4. Checked the proof from the target downward and compared imports and old/new dependency
   sets. Removed proof-only dependencies are listed in `## No longer needed`; the remaining
   imports are used. The compactification, boundary, Leray, and generic-point route remains
   below the unit, whose `realized` fields are empty. Verdict: pass.
5. Checked that each node's Lean statement is verbatim, its `proof_deps` is the union of its
   proof-step uses, and the target node changes only proof-owned fields. Verdict: pass.

Repair changed only the item proof (removing the duplicate private theorem and inlining its
proof) and this report; target and helper statements and node dependencies are unchanged.

## Earlier second reading (a previous round; superseded)

1. Compared each delivered module with the repository version using `diff`. The target
   declaration and all existing declaration signatures are unchanged; the delivery adds
   the two helper modules and their node records as declared above. Verdict: pass.
2. Compiled all three modules with `lcompile.py --all`. There are no errors, `sorry`
   declarations, forbidden declarations, or hollow definitions in the delivered files;
   imported open theorems account only for pre-existing `sorryAx` dependencies. Verdict:
   pass.
3. Read the target and helper statements against their uses and the corresponding DAG
   records. The helper statements are true, strictly narrower than the target, and have
   complete source-backed docstrings; no duplicate library theorem remains. Verdict: pass.
4. Traced the target proof from the top downward. The compactification, infinity boundary,
   Leray, Cartier, and generic-point routes remain in place, while unused finite-stalk,
   spectral-sequence, and injective-resolution dependencies are pruned as recorded above.
   The unit route is preserved. Verdict: pass.
5. Checked each node's verbatim Lean statement, proof steps, `proof_deps`, and
   `proof_origin` against the source. The target node changes only proof metadata, and the
   two added nodes contain the required fields and exact declarations. Verdict: pass.

Changed during this second reading: added this required review section; no Lean proof,
statement, definition, import, or node content needed further repair.


## Second reading by C4

1. Compared the item with the read-only repository using `diff` and a byte comparison
   of the complete theorem signature. `affineLineProjection_stalk_bound` is unchanged;
   no existing definition, declaration signature, or public import changes. Both added
   modules have exactly one public geometric theorem with a matching new node. Verdict: pass.
2. Compiled all three modules in import order with `lcompile.py --all` after repairs.
   No warnings, errors, `sorry`, forbidden declarations, or data definitions occur in
   the delivered Lean files. Explicit `#print axioms` in a scratch module gives only
   `propext`, `Classical.choice`, and `Quot.sound` for the infinity model. The generic
   field model and the item additionally use `sorryAx` from existing open imported
   results, including the planned smooth strict-local field model; no new hole is added.
   The field witness is the actual residue field, and its isomorphism comes from the
   explicit bijective residue map. Verdict: pass with those existing open dependencies.
3. Read both new statements, proofs, docstrings, and nodes. The generic model uses
   finite residue transcendence degree and dimension m-a=0, then the reduced local-ring
   field criterion; m=0 works. The infinity model constructs the chart coordinate in
   the strict localization, uses flatness to keep it regular and nonzero, and compares
   the two open-immersion ranges. The residue map of the infinity closed immersion
   preserves K, so the dimension bound a<=n+1 applies also to nonclosed points and n=0.
   Neither helper restates the target and neither leaves a hole. Repeated independent
   LeanFinder, Loogle, and source searches found no existing geometric helper to replace
   them. Found and removed a duplicate residue-map composition lemma using the existing
   `Hom.residueFieldAlgebraMap_comp` in `WeilConjectures.PointCount`. Verdict: pass.
4. Traced the proof from the final assertion through the q=2 and q>2 branches. The
   q=2 cardinal cancellation produces the generic-field hypothesis and the existing
   affine-curve theorem gives degree-two vanishing. For q>2, the boundary inequality,
   closed-support counit, projective-line bound, and supplied Leray diagonal assemble
   exactly the required vanishing. The earlier duplicate support theorem stays removed.
   The algebraic-closure singleton detects zero sheaves over the original field, without
   choosing an arbitrary field witness. All removed original imports and dependencies
   are accounted for above. `sk-prop-sf-cbc` has empty realized statement/step attachments;
   compactification, boundary, Leray and generic-point reasoning are preserved. Verdict: pass.
5. Checked that each geometric node's Lean statement occurs verbatim in its module,
   each `proof_deps` equals the union of proof-step uses, and the old node changes only
   `proof`, `proof_deps`, and `proof_origin`. Removed the infinity node's generic-model
   dependency after eliminating that import: it had only supplied the scalar-map helper,
   not the generic-field theorem. New nodes carry source, origin, searches, creation,
   blueprint, chapter, unit, and Lean records. Verdict: pass.

Changed in this second reading: removed the untracked public scalar-map helper by making
its calculation local/private, removed the unnecessary infinity-to-generic import and DAG
edge, replaced the duplicate private composition lemma by the existing public theorem,
and completed the removed-import accounting. The target and both public geometric helper
statements are unchanged. Closed 1 original hole; added 0 holes; no split-off obligations.
