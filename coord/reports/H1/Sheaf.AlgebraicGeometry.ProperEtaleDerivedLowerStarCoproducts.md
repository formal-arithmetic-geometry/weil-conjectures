## What changed

This is a pruning delivery under brief step 8d. The assigned theorem
`AlgebraicGeometry.Etale.proper_rightDerivedLowerStar_preservesCoproducts_for_grothendieck`
has exactly one caller: the proper-pushforward instance in the unused
`AlgebraicGeometry.Etale.CompactificationUpperShriek` namespace. Retire that namespace in
`WeilConjectures.SixFunctors.Etale.Derived.CompactificationUpperShriek`, an unclaimed module,
and withdraw the assigned module through `deleted.txt`.

Keep the legacy parent module path and both original public imports. No importer needs
an adaptation. The active `AlgebraicGeometry.Etale.rightDerivedUpperShriek` remains in
`Derived.UpperShriek`, with an explicit adjoint-existence hypothesis for general
coefficients and its existing proved finite-module-coefficient instance. Its definitions,
statements and proofs are unchanged. No target statement or active definition is changed.

The assigned node keeps its historical statement, sets `lean` to null, and records
retirement in `proof`, `proof_deps`, and `proof_origin`. No other node is changed.
Change record: `coord/changes/etale-compactification-upper-shriek-retirement.md`.

Validation: the unchanged original `Derived.UpperShriek` compiles against the replacement
legacy module. A scratch Lean probe imports all 46 modules identified by the downstream
whole-word name search with `import all`, examines loaded declaration types and available
bodies, and reports `LEGACY-AUDIT inspected=677022 external-dependencies=0` for references
outside the retired namespace. Whole-word hits belong to the active Etale/ProEtale API.
The replacement module and unchanged consumers `SmoothTensorDuality`,
`Derived.Adjunctions`, `Etale.Derived.UpperShriek`, and
`ProEtale.FiniteCoefficient.Derived.UpperShriek` also compile together.
The change record lists all 403 transitive importers, all name hits, and the changed
modules with their claim holders. Temporary unchanged consumer copies used for validation
are removed before delivery.

The unit `sk-prop-sf-cbc` has empty `realized` arrays. Its finite-coefficient adjoint
route remains implemented in `LowerShriekLeftAdjoint` and imported by the active
`UpperShriek`: compactification, extension by zero, proper derived coproduct preservation,
and Brown representability. No unit statement or realized proof step is bypassed.

## Proved and sorry left

Original item: 1 sorry. Proved: 0. Split off: 0. Added: 0. Remaining in the delivered
Lean files: 0. This removes an unused obligation; it does not prove its historical
mathematical assertion and is not a decomposition.

Withdrawn hole:
`AlgebraicGeometry.Etale.proper_rightDerivedLowerStar_preservesCoproducts_for_grothendieck`
(node `lem-etale-proper-derived-lower-star-coproducts-for-grothendieck`).

There is no remaining sorry in the item (withdrawn) or the changed parent. Existing
holes in unchanged consumers are untouched and are not counted as closed.

## No longer needed

Withdrawn module:
`Sheaf.AlgebraicGeometry.ProperEtaleDerivedLowerStarCoproducts`.
Its node `lem-etale-proper-derived-lower-star-coproducts-for-grothendieck` has no remaining
Lean obligation; its historical mathematical statement is retained in the DAG.

Retired namespace: `AlgebraicGeometry.Etale.CompactificationUpperShriek`, including
`isLeftAdjoint_rightDerivedLowerStar_of_isProper`,
`rightDerivedUpperShriekOfCompactification`, `rightDerivedUpperShriek`,
`rightDerivedUpperShriek_eq`, `rightDerivedUpperShriekOfCompactificationAdjunction`,
`rightDerivedUpperShriekAdjunction`, `isLeftAdjoint_rightDerivedLowerShriek`, the anonymous
right-adjoint instance, and the two scoped exceptional-inverse-image notations.
The module path itself remains for compatibility with its two direct importers.

Removed proof imports from that legacy module:
`WeilConjectures.CategoryTheory.DerivedCategory.BrownRepresentability.Grothendieck`,
`Sheaf.CategoryTheory.GrothendieckDerivedCoproducts`, and the assigned module.
The withdrawn item's own public import
`WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar` disappears with the item.
These are removed edges; the other imported modules remain needed elsewhere.

The retired node no longer needs its proof-dependency edges to
`lem-weil-pbc-cohomology-filtered-colimit` and `lem-grothendieck-derived-has-coproducts`.
These nodes are not claimed to be globally unnecessary. The finite-coefficient
`thm-amb-etale-exceptional-adjoint` route and all of its active dependencies are retained.

## Where the brief, the DAG or earlier work was wrong

The assignment says the auxiliary module is target-reached, which holds through the
legacy import edge, but that edge does not correspond to a needed declaration. The
active upper-shriek API already uses the finite-module-coefficient adjunction proved
in `LowerShriekLeftAdjoint`; none of the retired namespace is used by that API or its
consumers. The F4 split introduced a new obligation for this unused route.

The auxiliary node's proof asserts finite cohomological amplitude for arbitrary
Grothendieck abelian coefficients. The cited geometric coproduct proof in the active
library treats torsion module coefficients; it does not justify that generalization.
This delivery does not decide whether the historical assertion is false. It prunes
an unused obligation rather than replacing it by a weaker statement.


## Second reading by H1

1. **Visible interfaces: pass, with the declared retirement.** Compared the complete delivered
   `CompactificationUpperShriek` module against the repository with `diff -u`. Its two public
   imports are byte-for-byte unchanged; the only code changes remove the three proof imports
   and the documented legacy namespace. No surviving declaration has a modified signature,
   proof, or definition. Checked that both complete original Lean files occur verbatim in the
   change record's Old section. The item's historical node statement is unchanged. The item
   withdrawal and all removed declarations are explicit in the record and report; this is an
   interface retirement, not a proof-only replacement or a weaker theorem. Rechecked the
   downstream tool: the only direct importers are the aggregate `WeilConjectures` module and
   `Derived.UpperShriek`; no external fully qualified legacy-name user was found.

2. **Compilation and trust: pass.** Independently compiled the replacement legacy module with
   `lcompile.py`, without errors or warnings. Copied four consumers byte-for-byte from the
   repository and compiled them with the replacement in the sandbox overlay:
   `SmoothTensorDuality`, `Derived.Adjunctions`, `Etale.Derived.UpperShriek`, and
   `ProEtale.FiniteCoefficient.Derived.UpperShriek`. All passed, and these temporary source
   copies were removed. The delivered module introduces no declaration, so its declaration
   axiom check is vacuous; it contains no sorry, axiom, unsafe, opaque, implemented_by, extern,
   or data chosen from an unproved existence theorem. Re-ran the independent consumer
   expression audit against the published library: `LEGACY-AUDIT inspected=677022
   external-dependencies=0`. This checks loaded declaration types and available bodies,
   including proof bodies; it supports the source search rather than claiming a global build.

3. **Split statements: pass, none.** This delivery adds no statement, definition, theorem,
   or node, and leaves no split-off sorry. The removed arbitrary-Grothendieck-coefficient
   assertion is not proved or replaced by the torsion-module assertion. The old proof's
   unsupported coefficient generalization remains identified in the report. Existing
   lower-level obligations outside this retirement are not claimed as closed.

4. **Route and pruning: pass.** Read the unit JSON and its source `_section.md`, the original
   auxiliary node, and the active `UpperShriek` and `LowerShriekLeftAdjoint` implementations.
   The unit's realized arrays and steps are empty, and its coefficient restrictions remain
   untouched. The active finite-module-coefficient instance still invokes
   `isLeftAdjoint_rightDerivedLowerShriekOfCompactification`, whose proof uses proper derived
   coproduct preservation, open-immersion extension by zero, and Brown representability.
   All three removed proof imports and both old node proof-dependency edges appear under
   No longer needed. The retained public imports preserve compatibility for existing importers.
   No source or compiled consumer depends on the retired namespace, so pruning it removes
   an unused obligation without replacing a unit step.

5. **Node agreement: pass.** The sole changed node retains its mathematical statement,
   source, chapter, and unit; `lean: null` detaches the withdrawn theorem, and `proof`,
   `proof_deps: []`, and `proof_origin` explicitly record retirement, not a mathematical
   proof. There are no new-node field requirements to satisfy. The proof-dependency list
   is exactly the union of the recorded uses, which is empty.

Second-reader changes: added this independent review record and synchronized untouched
maintainer-owned node metadata with the current repository. No Lean repair was needed;
the declared pruning implementation and its change record were retained.
