## What changed

Proved `Sheaf.AlgebraicGeometry.FlatBaseChangeChartUnitIso` without changing its
statement. Constructed its coefficient isomorphism by uniqueness of two composite
left adjoints, with their right adjoints identified by the chart's scheme
commutativity and Mathlib pushforward comparisons. Constructed the equivalence
for pushforward along the given scheme isomorphism and proved the coefficient
isomorphism's transpose invertible.

Added the proof-only import
`Sheaf.AlgebraicGeometry.FlatBaseChangeRestrictionUnitNormalization` for a proved
general unit-normalization equation. Its proof transposes through the composite
adjunctions and evaluates the given unit square on opens. After one additional
restriction, both sides agree by presheaf functoriality and thinness of the category
of opens. Existing definitions, signatures, public imports and attributes are
unchanged. The local unused-variable linter is disabled only for the existing
signature's unused let A; its text is preserved.

## Proved and sorry left

Closed the one original hole in
`AlgebraicGeometry.Scheme.Modules.isIso_flatBaseChange_chart_unit_adjoint`
(node `new-flat-base-change-chart-unit-iso`). Also proved the new auxiliary theorem
`AlgebraicGeometry.Scheme.Modules.restriction_chart_unit_normalization`
(node `lem-pc-restriction-chart-unit-normalization`). There are no sorries in either
delivered module and no new holes. Imported dependencies retain their own proof
status. This is a proof, not a decomposition.

Both statements cover empty schemes and opens, identity inclusions, and zero
coefficients through the same functorial identities. No affineness, compatibility
of scalar maps, cohomology or flatness is used in the coefficient argument.

## No longer needed

No existing imports, modules or dependency nodes were removed. All five original
proof dependencies still serve the argument or its types. The new module imports
only `Sheaf.AlgebraicGeometry.TensorPullbackAdjunction`; a redundant direct
Mathlib modules-sheaf import was removed during development. The unit's realized
nodes and route are preserved.

## Where the brief, the DAG or earlier work was wrong

The earlier attempt stopped without implementing a reduction. Uniqueness of the
composite adjoints constructs the coefficient comparison directly, so separate
coherence equations for each ordinary pullback comparison are unnecessary. The
remaining unit identity is proved by the specified unit square and restriction
maps between opens. No statement error was found.

## New nodes

`lem-pc-restriction-chart-unit-normalization`, in
`dag/nodes/sec-proper-base-change/`, records a proved equality of specified
coefficient morphisms. Its source is Stacks Sheaves 0096/0097, as applied in the
parent's original second proof step. It has no resolutions, affineness or
cohomology assumptions and no invertibility conclusion. LeanFinder and Loogle
found the individual uniqueness-of-adjoints unit identities; source searches
found private restriction-composition identities and affine-chart section
formulas but no public theorem giving this normalization. LeanSearch was
unavailable. No change record or forced adaptation is required.

## Second reading by T2

1. Interface preservation: PASS. Compared the delivered item with the repository
   using diff and checked its theorem signature byte for byte. Its statement,
   docstring, public imports and attributes are unchanged. The only added import
   is plain, proof-only. The added unused-variable option is scoped to this theorem.
   The normalization module is new; no existing definition or target is altered.
2. Proof and trust: PASS. Compiled both modules in import order with lcompile.py,
   without errors or warnings (26.2 s and 9.5 s). A separate scratch probe printed
   the axioms of both public theorems: exactly propext, Classical.choice and
   Quot.sound, with no sorryAx. Checked both delivered sources for sorry and the
   forbidden declaration mechanisms; none occur. The coefficient isomorphism is
   constructed from explicit functor isomorphisms and uniqueness of adjoints,
   not an arbitrary witness of an unproved existence assertion. The chosen tensor
   adjunction theorem is already proved and pins its unit on sections.
3. Auxiliary statement: PASS. No statement is left split off with sorry. The new,
   proved normalization theorem gives an equality of specified morphisms, without
   the original invertibility conclusion, resolution data or affine-chart data.
   Read its complete docstring calculation and proof. The inclusion used to
   restrict the unit square follows from j followed by u = l. Empty opens and
   empty schemes cause no nonemptiness obligation; identity inclusions and zero
   coefficients satisfy the same functorial calculation. Independent searches
   used LeanFinder for restriction-unit composition/naturality and Loogle for
   homEquiv with leftAdjointUniq, plus rg in Sheaf, upstream Modules and Mathlib.
   They found the already used basic identities, not this combined equality.
   Checked FlatBaseChangeOpenChoicesExist, ModulePullbackAffineChartUnit,
   EtaleTensorOpenSectionsNaturality and upstream PullbackUnit for overlap.
4. Route and pruning: PASS. Composite left-adjoint uniqueness gives the comparison
   directly; the right-adjoint equivalence makes its transpose invertible. This
   is the existing coefficient argument, with its unit calculation factored into
   a fully proved helper. Both original public imports supply statement data
   (FlatBaseChangeOpenChoices and the base-change scheme/module constructors).
   The helper's sole public import supplies its statement's tensor adjunction.
   No unused proof import was found. All five old dependency nodes still supply
   types or proof ingredients, so No longer needed is complete. Read sk-thm-p1's
   realized statement and four step lists: this reduction is below those nodes
   and leaves that route intact.
5. DAG agreement: PASS. The existing node changes only proof, proof_deps and
   proof_origin. Both nodes' recorded Lean signatures equal the actual signatures
   verbatim; each proof_deps is exactly the union of its proof steps' uses. The
   parent records coefficient comparison, pushforward equivalence and use of the
   new normalization theorem. The helper records the adjunction-transposition and
   open-restriction calculation, source, searches, creation, blueprint ancestry,
   chapter, unit and Lean declaration. No change record is needed.

Second-reading changes: appended this review and performed the independent
searches and scratch axiom probe. No Lean proof, statement, import or node repair
was needed. Removed the temporary probe source before delivery. Net holes closed:
one original; holes added: zero; outstanding split-off holes: zero.
