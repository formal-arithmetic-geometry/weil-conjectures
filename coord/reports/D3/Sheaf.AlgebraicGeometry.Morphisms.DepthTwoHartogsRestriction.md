## What changed

Replaced the sole sorry in
`Sheaf.AlgebraicGeometry.Morphisms.DepthTwoHartogsRestriction` with a complete Lean
proof, preserving its signature and visibility. Added proof-only imports of
`Sheaf.AlgebraicGeometry.Morphisms.DepthOneRestrictionInjective`,
`Sheaf.AlgebraicGeometry.Morphisms.DepthTwoRestrictionBoundarySurjective`, and
`WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf`.

The proof lowers the boundary depth bound to one, obtains injectivity on sections,
passes it to stalks, and combines it with boundary stalk surjectivity. Inside U,
the existing proved `Modules.bijective_stalk_of_isIso_restrict` applies because
the restriction adjunction has invertible counit and its triangle identity makes
the restricted unit invertible. Mathlib then gives bijective section components
from stalkwise bijectivity and reflects their invertibility to the module unit.

The two new statement modules each contain one public named theorem with its
entire proof left as `by sorry`. They separately state uniqueness at depth one
and existence of boundary germ extensions at depth two assuming injectivity.
Their docstrings and DAG nodes give the source arguments in full. The item's DAG
proof and dependency list now match the actual Lean proof. No definition, existing
statement, public import, target, unit statement, or unit proof step was changed.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Scheme.isIso_restrictAdjunction_unit_of_depth_two`
(node `lem-sbc-depth-two-hartogs-restriction`), by decomposition into two strictly
partial statements. There are no direct sorries left in the item's module.
This is a decomposition, not a claim that Hartogs is proved without sorry axioms:
one original hole closed, two lower holes added, net minus one.

The delivery adds exactly these holes:

- `AlgebraicGeometry.Scheme.injective_restrictAdjunction_unit_app_of_depth_one`
  (node `lem-sbc-depth-one-restriction-injective`). This establishes only uniqueness,
  under the weaker depth-one hypothesis; it gives no extension of any section.
- `AlgebraicGeometry.Scheme.surjective_restrictAdjunction_unit_stalk_of_depth_two`
  (node `lem-sbc-depth-two-restriction-boundary-surjective`). This establishes only
  boundary germ existence, and assumes injectivity of section restriction. It
  supplies neither injectivity nor the inside-U and sheaf-to-module glue.

All three modules compiled together with lcompile.py, without warnings. The new
statements include zero stalks, the zero module, empty L, U empty, and U top.
For U top the second statement has no boundary point to which it can apply;
the original proof takes the inside-U branch. For U empty its direct-image target
is zero, so boundary surjectivity is automatic; uniqueness at positive depth
forces the sheaf itself to vanish. For an empty scheme the stalk criterion is
vacuous and still yields the isomorphism. The finite-stalk witnesses are retained
in both new signatures and the depth-two witness is reused when lowering depth.

## No longer needed

None. No imports were removed, and the original node had no proof dependencies
to prune. The original public imports support the existing signature and are
retained. No unused proof import was added. The quoted coherence argument is
absorbed into the lower statements' affine arguments rather than added as a
separate coherence node. No bypass of the unit's depth-two extension route occurs.

## Where the brief, the DAG or earlier work was wrong

The node's two non-elementary steps had empty `uses` lists and no declared proof
dependencies. Thus there were no existing named statements from which the plan
could literally be assembled. The delivery makes the uniqueness and boundary
surjectivity parts explicit rather than moving the full isomorphism into one
replacement hole.

The module's source proof is mathematically sound. Stacks Tags 0E9I, 0AV8, 0AVN,
0B3M, 05AR, 00LL and 00LX were read from the Stacks website because this checkout
contains citation lists but no Stacks source files. No source or target error was
found. For the surjectivity proof the target need not be coherent: finite
submodules containing the finite source suffice, exactly as in 0AV8. Work on
Noetherian affine neighbourhoods avoids imposing global quasi-compactness.

Searches: LeanFinder returned general stalk criteria, not a depth-boundary
restriction theorem; LeanSearch returned Internal Server Error (recorded as
unavailable); Mathlib grep for `Hartogs|depth.*restriction|restriction.*depth`
returned no hits. Source-library Hartogs results concern special divisor or unit
situations. A blueprint search for restriction/depth and repository searches
found no existing node for either new statement. The source-library sheaf module
contains a proved inside-open stalk criterion and no direct sorry, which is used.

## New nodes

`lem-sbc-depth-one-restriction-injective`, in
`dag/nodes/sec-smooth-base-change/lem-sbc-depth-one-restriction-injective.json`,
is stated in `lean/Sheaf/AlgebraicGeometry/Morphisms/DepthOneRestrictionInjective.lean`.
It isolates the uniqueness argument of 0B3M using positive boundary depth,
05AR, and 00LL. It inherits the item's unit and blueprint ancestry.

`lem-sbc-depth-two-restriction-boundary-surjective`, in
`dag/nodes/sec-smooth-base-change/lem-sbc-depth-two-restriction-boundary-surjective.json`,
is stated in
`lean/Sheaf/AlgebraicGeometry/Morphisms/DepthTwoRestrictionBoundarySurjective.lean`.
It isolates the finite-submodule quotient and depth-lemma argument of 0AV8,
applied to the direct image using 0AVN. It assumes the already supplied
injectivity and only asserts boundary stalk surjectivity. It inherits the item's
unit and blueprint ancestry. No change record is needed: all existing signatures
and public imports are unchanged, and both new modules are proof-only imports.

## Second reading by D3

1. **Declarations and interfaces.** I compared the delivered target module with the repository
version. The target theorem signature and every pre-existing declaration are byte-for-byte
unchanged; the only changes are three proof-only imports and the target proof body. The two
new modules have declarations matching their node `lean.statement` fields exactly.

2. **Compilation and trust.** I compiled all three sandbox modules together with
`lcompile.py --all`; they compile without errors or warnings. The target contains no `sorry`,
axiom, unsafe, opaque, extern, implemented_by, or `debug.skipKernelTC`. The only remaining
sorries are the two named split-off theorems, each a public theorem with a source docstring.
A scratch copy with `#print axioms` for all three declarations reports exactly `propext`,
`Classical.choice`, `Quot.sound`, and `sorryAx`, as expected for this decomposition.
No definition or arbitrary witness construction was added.

3. **Truth and strength of split statements.** I checked the new depth-one theorem against
Stacks 0B3M, 05AR, and 00LL: it asserts only injectivity of each restriction component under
positive boundary depth. I checked the depth-two boundary theorem against 0AV8, 0AVN, 05AM,
and 00LX: it asserts only boundary stalk surjectivity and takes componentwise injectivity as
an explicit hypothesis. Neither statement restates the target isomorphism, and both include
the zero, empty-boundary, empty-open, and top-open cases described in their docstrings.
The depth-one statement is strictly weaker: for a DVR with its closed point removed,
restriction of the structure sheaf embeds the DVR into its fraction field but is not
surjective. In the surjectivity argument, if the finite source stalk vanishes then
the quotient equals the middle stalk; if the middle stalk vanishes both vanish. This
handles the nonzero-module hypotheses of 00LX without imposing them on the theorem.
I independently ran LeanFinder for determination by associated points and extension
across a depth-two complement, and Mathlib grep for
`WeakAss|associated.*restrict|depth.*stalk`: the hits give no exact match. Repository and
upstream `rg` searches found only special structure-sheaf Hartogs results and general
associated-point/depth tools. `associated_iff_weaklyAssociated_of_fg_stalk` supplies
one ingredient of uniqueness, not the restriction assertion; `depth_in_short_exact`
supplies an ingredient of existence, not boundary direct-image surjectivity. Neither
split can be closed by a short application of these declarations.

4. **Proof route and pruning.** The target proof follows the DAG route: lower depth to one,
obtain componentwise injectivity, use the inside-open stalk isomorphism, invoke the boundary
surjectivity split, then apply the sheaf stalk criterion and componentwise isomorphism
criterion. The unit route is preserved. The added imports are all used; no original import
or proof dependency is unused, so no pruning is reported.

5. **DAG agreement.** I compared the delivered item node and both new node records with the
Lean files. Their proof steps, `proof_deps`, `proof_origin`, source places, blueprint ancestry,
and declaration statements agree with the code. The unit record remains unchanged.

**Changes made during second reading:** added this review and its independent search,
edge-case, and axiom evidence to the report. No Lean proof, statement, import, or node
needed repair. The proof is a decomposition (one upper hole closed, two lower holes
added), not a sorry-free Hartogs theorem.
