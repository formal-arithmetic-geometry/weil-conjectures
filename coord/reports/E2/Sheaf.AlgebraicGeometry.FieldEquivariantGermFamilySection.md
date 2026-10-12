## What changed

Replaced the sorry in `AlgebraicGeometry.Scheme.field_equivariant_germ_family_section`
with a complete reduction to the nonempty one-point case. Its signature and public
imports are unchanged. The proof constructs the singleton open cover using
`LocallyQuasiFinite.of_etale` and `Scheme.Hom.isDiscrete_preimage_singleton`, restricts
the equivariant family to its members, checks compatibility, uses the sheaf axiom to
amalgamate the component sections, and verifies the germs of the amalgamation.

Repair of return X-27111: removed the duplicate private `field_section_germ_ext`.
Generalized it in place to the proved private `section_germ_ext_of_lifts`, over
an arbitrary base scheme S and geometric point s, with an explicit hypothesis
that lifts of the etale object cover all its underlying points. Equal germs make
the equalizer sieve covering, and separatedness gives equality. The parent now
supplies the lift-covering hypothesis using
`exists_fac_of_etale_of_isSepClosed` over Spec K. This is a genuine generalization:
it applies, for example, to an object supported over the geometric point of a
base with several points, and needs no field structure on the base. The existing
field helper is private in `GaloisStalkActionFull`, which imports this item;
importing it here would create a cycle. No existing module outside the item is edited.

Added `Sheaf.AlgebraicGeometry.FieldEquivariantGermsOnePoint`, with the restricted
invariant-section step as its sole theorem. Updated the parent node's proof,
proof dependencies and proof origin to describe the actual singleton-cover argument.
Added a proof-only import of
`WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite`, which supplies the
etale-to-locally-quasi-finite instance. No definitions, target signatures or public
interfaces of existing declarations change.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Scheme.field_equivariant_germ_family_section`
(node `lem-exc-field-equivariant-germ-family-section`). The item now has no sorry.
The private `section_germ_ext_of_lifts` is also fully proved, with no new hole.

Added one hole:
`AlgebraicGeometry.Scheme.field_equivariant_germ_family_section_onePoint`
in `Sheaf.AlgebraicGeometry.FieldEquivariantGermsOnePoint`
(node `lem-exc-field-equivariant-germs-one-point`). Its whole proof is `:= by sorry`;
its source and complete natural-language argument are in its docstring and node.
The new theorem applies only to nonempty one-point schemes. It neither constructs
a covering of an arbitrary X nor proves compatibility or gluing. Those steps are
proved in the parent, so this is a decomposition, not a net sorry-free proof.
Holes closed: 1. Holes added: 1. Net change: 0.

The remaining argument uses `fieldSections_stalkInvariants`, whose algebraicity
hypothesis requires transporting the stalk from the algebraic part of Omega;
finite separable residue fields, extension of automorphisms, and the orbit of a
chosen lift provide the component argument. The existing invariant-section theorem
is retained as a dependency of the new node, not duplicated.

Both delivered modules compile together cleanly through `lcompile.py --all`.
The repaired delivery also passes the dry run with `WEIL_SERVER_COMPILE=1`,
which compiles the standalone new helper on the server; the parent is checked
locally against the sibling overlay, as the delivery script specifies. The
landing guard `tools/import_prune_check.py` exits 0 on the repaired parent.
`deliver3.py --no-push` rebases the delivery on the fetched current `sheaf-dag`.
The old second-reading section was removed because the repaired proof needs a
fresh independent reading; no delivery was pushed.
Edge cases checked mathematically: empty X is handled by the empty singleton cover
and sheaf amalgamation without calling the nonempty helper; arbitrary, including
infinite, disjoint unions use a point-indexed cover with no compactness assumption;
constant singleton sheaves have a unique prescribed family; constant empty sheaves
on nonempty one-point schemes have no f, so the helper's implication is vacuous;
nonalgebraic Omega remains permitted and is handled in the helper's stated proof.

## No longer needed

Removed the direct proof imports
`Sheaf.AlgebraicGeometry.Sites.FieldSectionsStalkInvariants` and
`Sheaf.AlgebraicGeometry.EtaleFibreDiscreteSeparablePoints` from the item. The old parent proof dependencies
`lem-exc-field-sections-stalk-invariants` and
`lem-weil-pbc-etale-fibre-discrete-separable-points` are no longer direct
dependencies of the parent. Both are retained in the new helper's proof plan and
imports, so neither module or node is pruned from the transitive closure. No module or node is claimed as globally pruned.

The parent does not need to choose intermediate fields or transfer stalks: these
parts belong only to the one-point lemma. The covering argument needs just the
proved locally-quasi-finite instance and discreteness lemma, rather than the
stronger fibre decomposition theorem. The parent's proof dependencies now contain
the one-point node and the geometric-stalk and sheaf definitions.
The duplicate field-specific private helper is removed; its use is replaced by
the generalized helper and the field lift-covering argument. No further imports,
nodes or modules are pruned by this repair.

## Where the brief, the DAG or earlier work was wrong

The previous delivery duplicated the exact statement of a private helper in
`GaloisStalkActionFull` and was correctly refused by the landing's duplicate
statement check. Renaming the same statement would not fix it; the repair removes
the field-base restriction and makes lift coverage an explicit hypothesis.
No false statement or changed existing public signature was found. The existing invariant-section
interface is not directly applicable to arbitrary Omega because it assumes
`Algebra.IsAlgebraic K Omega`; the original plan already accounts for this by passing
to the algebraic part, and the remaining helper records that argument explicitly.

The Stacks source text is not present at the listed local literature path on this
machine. Read the original direct proof and the action discussion online at
https://stacks.math.columbia.edu/tag/04JM and
https://stacks.math.columbia.edu/tag/03QW; these are the same source places as the
parent node. The arbitrary geometric-point discussion in 03QW explicitly includes
nonalgebraic points and surjectivity of extension of automorphisms.

Read `dag/units/sk-prop-h2.json`: this node is not a realized unit statement or step,
and its reduction preserves the invariant-section argument and the unit route.

Searches made before creating the helper: LeanFinder for global and one-point
realization, Loogle for `toPresheafFiber`, msearch grep for germ injectivity and
discreteness, and repository rg for one-point/germ/section interfaces. LeanSearch
returned Internal Server Error and is recorded as unavailable, without a verdict.
No exact existing one-point realization statement was found; structure-sheaf germ
lemmas do not apply to an arbitrary sheaf. `blueprint_refs.py search 'equivariant
germs'` returned zero blueprint matches. All searches are recorded in the new node.

## New nodes

`lem-exc-field-equivariant-germs-one-point`, in
`dag/nodes/sec-curve-estimates/lem-exc-field-equivariant-germs-one-point.json`,
states realization only on nonempty etale K-schemes with one underlying point.
Its Lean declaration is
`AlgebraicGeometry.Scheme.field_equivariant_germ_family_section_onePoint` in
`Sheaf.AlgebraicGeometry.FieldEquivariantGermsOnePoint`. The proof plan identifies
such a scheme with a finite separable spectrum, transports from the algebraic part
of Omega, descends the value at a chosen lift by the fixing-subgroup bijection, and
uses Galois transitivity to verify the other lifts. No global gluing is asserted.
No change record or forced adaptation is needed.


## Second reading by E2

1. Compared the parent module with the repository using `diff -u`, then checked
   the existing theorem signature from `theorem` to `:=` byte for byte: identical.
   Only its proof, proof documentation, proof imports, and a new private proved
   helper change. The public imports are unchanged. The sibling module is new;
   there are no adapted modules, definitions, or changed target statements.
   Verdict: no accidental interface change.

2. Independently compiled both modules in import order through
   `lcompile.py --all`: no errors or warnings. Scanned both delivered sources for
   forbidden constructs, hollow definitions, and holes: the parent has none;
   the sibling has exactly its one public named theorem with whole proof
   `:= by sorry`. Compiled scratch copies with `#print axioms`: the private
   `section_germ_ext_of_lifts` uses only `propext`, `Classical.choice`, and
   `Quot.sound`; both public declarations use those and `sorryAx`, as expected
   from the documented remaining theorem. The gluing chooses local sections
   inside an existential proof, and introduces no definition choosing arbitrary
   data from an unproved existence theorem. Verdict: sound reduction, with the
   explicitly reported remaining proof obligation; no claim of a sorry-free target.

3. Read the one-point theorem, its full docstring and node, and both planned
   dependency declarations. Read Stacks Tags [04JM](https://stacks.math.columbia.edu/tag/04JM)
   and [03QW](https://stacks.math.columbia.edu/tag/03QW): invariant descent and
   extension of automorphisms support the argument, including nonalgebraic Omega.
   Checked the separably closed base case, one-point finite separable spectra,
   singleton sheaves, and the vacuous empty-sheaf case; the parent's empty X and
   infinite disjoint unions are handled by its actual covering argument.
   The new hypothesis restricts X to one nonempty component; compatibility and
   gluing across components are genuinely proved in the parent. This is a
   strictly smaller part of the argument, not a restatement of the whole item.
   Independent LeanFinder search for descent of invariant stalk elements and
   Loogle query `"BijOn", "toPresheafFiber"` found no applicable replacement.
   Searched repository sources for fixing-subgroup invariants, equivariant germs,
   subsingleton etale objects, and germ extensionality. Existing invariant descent
   requires algebraic Omega; the sheaf/Galois equivalence also requires an
   algebraic closure and is unproved. The upstream one-point Hilbert 90 results
   concern module sheaves and do not realize arbitrary prescribed germs.
   The private field helper in `GaloisStalkActionFull` is downstream and cannot
   be imported without a cycle; the delivered helper has a genuinely more
   general base and an explicit lift-coverage hypothesis. Verdict: true, needed,
   documented decomposition; closing the remaining hole is substantial work,
   not a few-minute application of an existing theorem.

4. Read the proof from its target downward: discreteness gives a singleton cover,
   covariance restricts to each member, equalizer-sieve separatedness proves
   compatibility, and amalgamation plus germ naturality proves the conclusion.
   Public imports supply the signature; the new imports are proof-only. The
   sibling retains the existing proof-plan imports rather than duplicating
   invariant descent. The two old proof-dependency nodes removed from the parent
   are now named explicitly under `No longer needed`; both remain transitive,
   so global pruning is none. Read `dag/units/sk-prop-h2.json`: the item is not
   a realized unit statement or step, and no unit record or route is changed.
   Verdict: route preserved and pruning accurately reported.

5. Compared old and delivered parent JSON: exactly `proof`, `proof_deps`, and
   `proof_origin` change. Read all new-node fields, its verbatim Lean statement,
   provenance, source, three kinds of successful search plus the unavailable
   LeanSearch record, and its dependency union. Both nodes match their Lean
   declarations and actual/remainder proof plans. Verdict: DAG agrees with Lean.

Changes in this second reading: completed the explicit list of removed direct
proof-dependency node ids and appended this independent audit. No Lean proof,
statement, import, or DAG repair was needed. Holes closed: the parent declaration;
holes added: the one-point declaration. This remains a decomposition with net
hole change zero and no globally pruned module.
