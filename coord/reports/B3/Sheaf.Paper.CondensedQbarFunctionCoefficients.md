## What changed

Completed the original four-property theorem from two independent compatibility lemmas.
The proof now supplies affine weakly contractible scalar surjectivity, scalar evaluation
on algebraically closed fields, scalar evaluation at arbitrary scheme points, and
comparison of fibers over the same base point. The comparison uses an embedding of the
base residue-field closure into each chosen geometric-point field, so it needs no common
overfield construction.

Moved the existing explicit constructions, with their signatures and bodies unchanged,
to `Sheaf.Paper.CondensedQbarCoefficientConstruction`. The original module publicly
imports this lower module. This relocation lets the two independent compatibility
modules refer to the actual data without an import cycle; it is not a compile-limit
workaround. The complete unsplit file, including the new proofs, compiled in 34 seconds
before this relocation (saved locally in `scratchpad/full-green-before-extraction.txt`).

Added the actual definition `regularScalarValue F c f = c (F.map f (c.symm 1))` with
its proved computation rule. The two coefficient structures state their scalar-value
field through this folded expression. It is definitionally the old expression. This
prevents kernel checking from expanding geometric inverse-image modules just to compare
the same coordinate data. No geometric fiber, coordinate isomorphism, scalar action,
or target statement was changed. The change record is
`coord/changes/condensed-qbar-coefficient-value-api.md`.

The original proof-only imports of geometric field evaluation are retained where their
continuity instance is needed. The new proof imports weakly contractible sheafification,
regular-module evaluation, and the scalar compatibility and proved field-extension modules. All new imports used only
by proofs remain non-public.

Validation: all five delivery modules compile without warnings. The unchanged direct
consumers `CondensedQbarFunctionPresentations` and `CondensedQbarLfpMatrixRefinement`
also compile against the sandbox overlay. No consumer source adaptation is needed.
The value operation keeps ordinary definition transparency, so existing exact uses
of the scalar-value field continue to elaborate.

## Proved and sorry left

Original hole closed:

- `AlgebraicGeometry.ProEtale.condensedQbar_canonical_coefficient_properties`.

This is a decomposition, not a sorry-free proof: one upper hole is replaced by two
strictly smaller compatibility holes. The ledger net is 1 closed minus 2 added = -1; the total
hole count increases by one.

New holes, exactly two, each the sole admitted public theorem in its own module:

- `AlgebraicGeometry.ProEtale.condensedQbar_scalar_pullback`, node
  `lem-weil-pbc-condensed-qbar-scalar-pullback`. What remains is to construct the bounded
  presheaf base-change map, prove that its sheafified adjoint intertwines the normalized
  coefficient realizations using `globalCoefficientIso_test`, and transport bounded
  multiplication through that square and the regular-module comparison.
- `AlgebraicGeometry.ProEtale.condensedQbar_field_evaluation_linear`, node
  `lem-weil-pbc-condensed-qbar-field-evaluation-linearity`. What remains is to prove
  scalar linearity of the *specified* abelian evaluation comparison, through the
  tensor-action identity and the `fieldCoefficientIso` coefficient square using
  normalized constant test functions. This statement is a concrete equality, with
  no existence or invertibility conclusion. The field-extension natural isomorphism
  itself is now proved in `condensedQbar_fieldFiber_extension`: invertibility comes
  from the existing abelian extension theorem, `ModuleCat.isoMk` lifts components,
  faithful forgetfulness proves naturality, and `extendScalarsIsoComapInv` identifies
  the actual module inverse image. The arbitrary residue-field embedding and
  functor-composition argument are completed in the item module.

Completed private proofs in the item module include `bounded_unit_isIso`,
`sheafScalar_surjective`, `condensedQbarScalar_surjective`,
`fieldRegularCoordinates_apply`, `field_scalar`, `map_conjugate`,
`coordinates_conjugate`, `regularScalarValue_comp`,
`regularScalarValue_conjugate`, `fiber_scalar`, `fiber_pullback`, and `fibers_compare`.
The new `condensedQbar_fieldFiber_extension` is fully proved from the concrete linearity
lemma and the existing geometric field comparison. There is no `sorry` in the item,
construction, or field-extension modules, and no new admitted definition. The
scalar-value computation rule is proved.

The scalar-surjectivity proof handles the empty weakly contractible affine via
`boundedComponentsIso` and the terminal unit. Scalar pullback is true also for empty
source schemes; the endomorphism ring is then zero. The field-extension theorem allows
identities and transcendental extensions. No unjustified algebraicity hypothesis is
introduced.

## No longer needed

- Removed direct proof import `Sheaf.Paper.CondensedPointBasisEvaluation` and the original
  direct proof dependency `lem-weil-pbc-condensed-point-basis-evaluation`: the proof uses
  the weakly contractible Kan-sheafification unit and the explicit component quotient
  instead of this bundled point-basis theorem.
- Removed the redundant direct import `Sheaf.Paper.ProfinitePointPullback`; the geometric
  field evaluation module supplies its public interface where needed. This node remains
  needed transitively by the constructions and compatibility proofs, so it is not
  claimed as a globally pruned node.
- The common algebraically closed overfield route in the old final proof step is unused.
  No new common-overfield lemma or module is introduced.
- The public construction imports move to the common lower module and stay publicly
  available through the original module; they are relocation, not theory pruning.

## Where the brief, the DAG or earlier work was wrong

No false mathematical statement was found. The old plan's common-overfield comparison
is unnecessary: extending the residue-field map into the algebraic closure at the
source point gives the required embedding directly by `IsAlgClosed.lift`.

The direct scalar-coordinate expression was expensive for the kernel to compare after
substituting the canonical fiber data. Small abstract conjugation lemmas alone did not
fix this. Folding the value operation and supplying its exact computation rule fixes
the definition use while keeping the mathematical property unchanged. The full module
then compiled in 34 seconds before any construction relocation.

## New nodes

`def-weil-pbc-condensed-qbar-coefficient-construction` records the existing explicit data
in their common lower module and the new, fully constructed scalar-value operation.
It has zero holes. The old node's Lean attachment retains the interface structures and
the original two final theorems; moved data attach to the construction node.

`lem-weil-pbc-condensed-qbar-scalar-pullback` is the arbitrary-scheme scalar
compatibility needed both for restriction and for geometric scalar evaluation.

`lem-weil-pbc-condensed-qbar-field-fiber-extension` is the algebraically closed field
extension comparison needed for the completed residue-field argument. It concerns
all modules over a field spectrum and is fully proved from the concrete linearity
statement and the existing abelian extension evaluation theorem.

`lem-weil-pbc-condensed-qbar-field-evaluation-linearity` is the remaining explicit
scalar-action equality for the specified abelian comparison. Naturality, invertibility,
and the conversion to actual module inverse image have been proved outside this hole.

All four nodes record actual LeanSearch, Loogle and pinned-Mathlib grep searches.
The change record is `coord/changes/condensed-qbar-coefficient-value-api.md`.

## Second reading by B3

1. **Statements and interfaces.** I compared the delivered item with the repository
version and checked the declarations listed by the item node. The original theorem,
existence theorem, structures, and public helper signatures are unchanged except for
the declared `regularScalarValue` folding in
`coord/changes/condensed-qbar-coefficient-value-api.md`; its computation lemma makes
that field definitionally the previous expression. Verdict: pass.

2. **Proof and axioms.** I compiled all five delivered modules with
`lcompile.py --all`. The item, construction, and field-extension modules contain no
`sorry`; the only two remaining `sorry`s are the named public compatibility theorems
`condensedQbar_scalar_pullback` and `condensedQbar_field_evaluation_linear`, each with
its own node and proof docstring. The field-extension proof uses the specified
linearity theorem and the existing geometric comparison, and all declarations are
ordinary safe Lean declarations. Verdict: pass, with the two documented split holes.

3. **Split statements and searches.** I checked both split statements on their edge
cases (identity and arbitrary, including empty-source, scheme maps for scalar
pullback; arbitrary algebraically closed field extensions for evaluation linearity).
They are concrete equalities with no added algebraicity or invertibility hypotheses.
The construction node records the actual constructions and its search results; no
duplicate Mathlib or upstream declaration was found. Verdict: pass.

4. **Pruning and route.** The item proof uses the affine weak-contractibility unit,
the explicit coefficient construction, scalar pullback, and field-extension route.
The former point-basis and direct profinite-pullback imports are removed as reported;
the construction module retains the public imports required by its exposed
declarations, while the item keeps proof-only imports private. The unit route and
all realized construction steps remain represented in the DAG. Verdict: pass.

5. **DAG agreement.** I checked the item and the three compatibility nodes against
the Lean declarations, including `proof`, `proof_deps`, `proof_origin`, module paths,
and declaration names. The construction node records the relocated explicit data and
the folded value operation, and the field-extension node records its completed
natural-isomorphism assembly. Verdict: pass.

Changed during second reading: added this section and corrected the item theorem's
proof docstring to describe the actual residue-field embedding comparison.
