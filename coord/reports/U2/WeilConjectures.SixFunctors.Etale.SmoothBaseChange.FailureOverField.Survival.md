## What changed

Proved `Etale.survivesBaseChange_of_isLimit` by the limit argument of Stacks
[Tag 0F07](https://stacks.math.columbia.edu/tag/0F07), using two strictly smaller applications
of higher-image continuity. A hypothetical preimage at the limit descends to a stage.
Subtracting the transported original element produces a target-stalk element dying at the
limit. Finite-stage zero detection kills that difference after a transition. Compatibility
of transitions transports both the base-change image and the original element, contradicting
survival at this stage. The theorem signature and all existing definitions are unchanged.

Added the proof imports `Sheaf.AlgebraicGeometry.BaseChangeSourceImageLimitDescent` and
`Sheaf.AlgebraicGeometry.BaseChangeTargetLimitZeroDetection`. Their statements respectively
concern arbitrary source elements and arbitrary target elements dying at the limit. Neither
contains survival or the original element ξ. They are not restatements of the item.

Added `BaseChangeStalkTransition` with canonical wrappers for the existing stalks and
restriction maps, a proved range-preservation lemma using existing base-change compatibility
and coefficient naturality, and a proved transport-composition lemma using the existing
`baseChangeTargetTransition_comp`. The two compatibility statements are in their own
modules `BaseChangeTargetStalkRestrictionImage` and `BaseChangeStalkTransportComp`; the
wrapper module contains definitions only. No new axiom or hollow definition was added.

Updated the failure-field node's limit argument and dependencies. The unit's route remains
thickening invariance, limits, closed–open decomposition, and the empty scheme.

All six delivered modules compile locally. New statements were checked against
[Tag 09Z1](https://stacks.math.columbia.edu/tag/09Z1): stages mapping to affine S are qcqs;
the limit and its projections satisfy the needed qcqs/affine properties; base change to X
preserves these properties. The coefficient is pulled back from the fixed sheaf, not an
arbitrary system. Negative degrees vanish; the cofiltered category is nonempty, including
for the zero coefficient ring. Constant diagrams and zero elements give the expected
identity/zero special cases. The target zero-detection assertion requires vanishing only
of the specified representative and makes no assumption about any base-change image.

Searches: Lean Finder returned the abstract filtered module colimit element criteria;
Loogle confirmed `Concrete.colimit_rep_eq_zero`; LeanSearch was unavailable with an internal
server error. Local searches found `Etale.higherDirectImage_limit` and the target composition
and base-change naturality lemmas, but no canonical source-image descent or target relation
detection statement. The new nodes record the queries and results.

## Proved and sorry left

Of the item's two original sorries, one is now reduced with a complete Lean proof:
`AlgebraicGeometry.Etale.survivesBaseChange_of_isLimit`.

New compatibility proofs, with no local sorry:
`AlgebraicGeometry.Etale.baseChangeTargetStalkMap_mem_range` and
`AlgebraicGeometry.Etale.baseChangeStalkTransport_comp`.

Every sorry left in this delivery:

- `AlgebraicGeometry.Etale.survivesBaseChange_or_of_isClosedImmersion` (unchanged;
  existing node `sbc-lem-bc-failure-field`, condition (3)).
- `AlgebraicGeometry.Etale.baseChange_source_image_limit_descent`
  (`lem-sbc-source-image-limit-descent`).
- `AlgebraicGeometry.Etale.baseChange_target_limit_zero_detection`
  (`lem-sbc-target-limit-zero-detection`).

The new sorries are public named theorems in separate modules, with full proofs in words.
Existing proofs of identity survival, thickening invariance, empty-scheme failure, and the
assembling local-property theorem are retained.

## No longer needed

No existing import was removed: the existing proof imports support thickening invariance.
The limit argument now uses the fixed-pulled-back-module-sheaf continuity node
`sbc-lem-higher-image-pulledback-stalk-continuity`, via the two new intermediates.
The more general abelian-sheaf-system node `sbc-lem-higher-direct-image-limit` and its module
`Sheaf.AlgebraicGeometry.HigherDirectImageLimitSystem` are not needed by this limit proof;
its direct dependency was removed from the failure-field node. This is local pruning only:
other parts of the project may still require that generic theorem.

## Where the brief, the DAG or earlier work was wrong

The previous sandbox report recorded compilation with both original sorries untouched;
that did not constitute a stage-3 delivery. The present delivery supplies a compiling
reduction of the limit clause, with real combination and compatibility proofs.

The DAG's generic limit lemma is stated for abelian sheaf systems over a directed preorder.
The source library now supplies a module-coefficient, arbitrary-cofiltered-category,
fixed-pullback stalk continuity theorem. It fits this application more closely. The two
new statements isolate the inverse-image/homology and pullback/coefficient identifications
required to apply that theorem to the two sides. No false statement or target change was
found. The closed–open clause remains open rather than being moved under another name.

## New nodes

`def-sbc-canonical-base-change-stalk-transitions`: wrappers naming A(U), B(U), b_U, r_φ and
t_U using the existing geometric stalks, base-change maps and transitions. Module:
`Sheaf.AlgebraicGeometry.BaseChangeStalkTransition`.

`lem-sbc-target-stalk-restriction-image`: restriction preserves base-change images;
proved by transition compatibility and naturality, in `BaseChangeTargetStalkRestrictionImage`.

`lem-sbc-stalk-transport-composition`: restriction commutes with canonical transport
from any original Cartesian square; proved by target composition and pullback uniqueness,
in `BaseChangeStalkTransportComp`.

`lem-sbc-source-image-limit-descent`: the source-side continuity application, with one
sorry, in its own module `Sheaf.AlgebraicGeometry.BaseChangeSourceImageLimitDescent`.

`lem-sbc-target-limit-zero-detection`: the target-side zero-detection application, with
one sorry, in its own module `Sheaf.AlgebraicGeometry.BaseChangeTargetLimitZeroDetection`.

No change records are required: no existing signature or definition changed.


## Second reading by U2

1. PASS. Compared the complete item diff with the repository and checked its declaration
   table: every existing signature and definition is unchanged; only the limit proof and
   private proof imports change. No change record or target-statement adaptation is needed.
2. PASS. Compiled the delivered modules in import order through lcompile.py, with no errors
   or warnings. A scratch import file printed axioms for all public declarations: only
   propext, Classical.choice, Quot.sound, and sorryAx occur. The range-preservation theorem
   has no sorryAx; transport composition inherits sorryAx from the existing transition
   composition theorem. The limit clause is a checked reduction, not an axiom-free closure:
   its two continuity intermediates remain open. All three local sorries are listed above;
   none is in a definition. No forbidden declaration or compiler escape occurs.
3. PASS. Read both new open statements against Stacks Tags 09Z1 and 0F07. Their proofs in
   words use qcqs maps to affine S, preservation under base change, affine limit projections,
   exact inverse image, and stalk preservation of filtered colimits. Small cofiltered
   indexing is handled by directed cofinal refinement. Checked identity/constant systems,
   zero coefficients and representatives, negative degrees, and nonemptiness of indexing.
   The source assertion descends arbitrary images; the target assertion detects arbitrary
   zero representatives. Neither assumes survival or restates the item. Independent
   Lean Finder searches for geometric stalk inverse image filtered-colimit continuity
   returned scheme-stalk facts, not the needed identifications. Loogle's name-fragment
   query found Concrete.isColimit_exists_rep and Concrete.isColimit_exists_of_rep_eq.
   Local rg and msearch grep found higherDirectImage_limit and the source/target functor
   isomorphisms, but no complete geometric identification with these canonical transitions.
   Closing either intermediate requires that identification and is not a short lemma reuse.
4. PASS. Followed the subtraction/zero-detection proof from the target downward. It uses
   both intermediates and the two compatibility statements, with no unused added import.
   Original imports remain needed for statements or thickening invariance. The sole old
   proof dependency removed is sbc-lem-higher-direct-image-limit, as reported above.
   The unit sk-lem-failure-field keeps its thickening, limit, closed–open, and empty-scheme
   route. Its realized.statement and realized.steps entries were already empty in the
   repository; this delivery neither edits nor bypasses the unit route.
5. PASS after repair. Read all six node records against their declarations and checked
   proof_deps against the union of step uses. New nodes carry source, search, creation,
   blueprint ancestry, chapter/unit, and Lean records. Corrected the stale failure-field
   sentence that said both conditions (2) and (3) remain open; only (3) remains locally open.

Second-reading changes: moved each proved compatibility statement into its own new module,
with the range-congruence helper beside range preservation, as required by the brief.
Adjusted the item's private imports and the two node module/file records. Removed the now
unused transition-composition proof import from the definitions module. Corrected the stale
DAG sentence and updated this report. No mathematical statement, definition, or proof term
was altered. The delivery tool's all-declaration axiom probe provides the final check.
