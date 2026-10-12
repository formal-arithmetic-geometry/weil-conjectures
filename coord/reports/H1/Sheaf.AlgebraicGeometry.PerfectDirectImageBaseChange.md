## What changed

Proved `AlgebraicGeometry.perfect_derivedDirectImage_baseChange` in
`Sheaf.AlgebraicGeometry.PerfectDirectImageBaseChange`, preserving its complete signature
and all public imports. Updated the route of `lem-pc-rf-perfect-base-change` to match Lean.
No definition, public signature, target, or other module was changed.

Perfectness specializes `AlgebraicGeometry.properSupport_perfect_directImage` to the
structure tensor unit and the complex concentrated in degree zero at G. Fully proved
private helpers transport derived localizations along an exact equivalence, prove finite
presentation of zero sheaves, prove perfection of the derived tensor unit, and detect
derived isomorphisms on an open cover. The localization family supplied on S is preserved
by a dependent function update, so no extra localization hypothesis is added. No object is
chosen from an unproved existence theorem.

Base change uses the existing affine calculation and canonical-map affine-locality theorem,
then the existing open-cover detector for module sheaves and Mathlib's homology detector.
It proves invertibility of every map satisfying the given predicate, not just existence
of an unspecified isomorphism. The unit route remains the same: perfectness plus arbitrary
base change. The unit record has empty realization lists, and no unit is bypassed.

Added only proof imports of
`Sheaf.AlgebraicGeometry.CanonicalModuleBaseChangeAffineLocality`,
`Sheaf.AlgebraicGeometry.AffineRelativelyFlatCanonicalModuleBaseChange`,
`Sheaf.Topology.SheafIsomorphismLocalOpenCover`,
`Mathlib.CategoryTheory.Localization.Equivalence`, and
`WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree`.
The item's module compiles cleanly through the authorized launcher in about 13 seconds.
The search calls used LeanFinder, Loogle, and Mathlib grep; local searches additionally
found the newer canonical affine declarations. The proof follows the specialization in
[Stacks Tag 0B91](https://stacks.math.columbia.edu/tag/0B91) and
[Tag 0A1H](https://stacks.math.columbia.edu/tag/0A1H), read directly online.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.perfect_derivedDirectImage_baseChange`
(blueprint: `lem-pc-rf-perfect-base-change`).

No `sorry` remains in the item's module. No holes or new modules were added.
This is a proof from existing named dependencies, not a new decomposition: the general
proper-support theorem and dependencies of the affine calculation remain separate items.
The proof still depends on existing admitted declarations, so it is not a claim that
all five targets are already closed without `sorryAx`.

## No longer needed

Removed the proof imports:

- `Sheaf.AlgebraicGeometry.RelativelyFlatDerivedBaseChange`:
  `lem-pc-rf-base-change-flat-module` supplies only an unspecified isomorphism, whereas
  this proof uses the canonical affine calculation and its affine-locality theorem.
- `Sheaf.AlgebraicGeometry.ClosedSubsetProperOverBaseProperties`:
  `lem-weil-pbc-closed-subset-proper-over-base-properties` is unnecessary here. Compose
  the reduced induced closed immersion of each support with the proper morphism f;
  Mathlib's proper-composition instances prove the required support properness directly.
- `Sheaf.AlgebraicGeometry.ClosedSubsetProperOverBase`: its definitions remain needed
  and are available through the public imports of `ProperSupportPerfectDirectImage`;
  the separate direct import is redundant. Its definition node remains in `proof_deps`.

No claim is made that these modules are unreachable through every other target route.
The two omitted theorem nodes are removed from this node's proof dependencies. No other
original proof node is pruned; the perfect-complex, proper-support, finite-type-support,
and support-properness definitions remain used.

## Where the brief, the DAG or earlier work was wrong

The original base-change dependency only concludes `Nonempty (source ≅ target)`. That
cannot prove invertibility of the particular canonical comparison in this item's
statement. Existing stage-3 affine canonical-map results remedy the interface mismatch
without changing any declaration. The existential global canonical-map theorem also
asserts only one comparison's invertibility; instead we use the affine and locality
interfaces, which accept each supplied comparison.

The general proper-support theorem requires derived categories for the localized open
sites of every scheme, but this item supplies them explicitly only for S. These are
constructed from the given scheme localizations using `Scheme.Modules.overEquiv` and
Mathlib's exact-equivalence localization transport. This is proved in Lean, including
preservation of the supplied S family, rather than hidden in an added hypothesis.

The source texts named by the existing nodes are absent from this read-only clone.
WANTED: literature/stacks-project/perfect.tex, Tags 0B91 and 0A1H,
for lem-pc-rf-perfect-base-change. Their official online pages were read; the new Lean
assembly is recorded as agent-written. The sources agree with the unchanged statement.

## Second reading by H1

1. Signature and visible interface: PASS. Read the repository and delivered module
   in full and compared them with `diff -u` and the declaration-table checker.
   The existing theorem's signature is byte-for-byte unchanged: all scheme-derived
   categories, properness, local finite presentation, quasi-compactness,
   quasi-separatedness, the supplied open localizations on S, additive tensor
   pullbacks, finite presentation of G, and relative flatness remain. Both conclusions
   remain: perfectness of Rf_*(G[0]) and invertibility of every supplied map satisfying
   IsDerivedModuleBaseChangeMap, for every g. All public imports are unchanged;
   the four new helpers are private. No definition or other module is changed.
2. Proof and axioms: PASS. Compiled the sole delivered module through lcompile.py
   with no errors or warnings (14.6 seconds). Inspected every proof and scanned for
   forbidden constructs; no sorry or forbidden declaration occurs in the module.
   A scratch copy with explicit #print axioms checks compiled in 12.4 seconds.
   All four helpers use only propext, Classical.choice and Quot.sound. The main
   theorem uses those plus sorryAx from existing imported open statements, as
   disclosed above. The localization-existence helper is fully proved and explicitly
   constructs the localization; choosing its proved witnesses introduces no data
   from an unproved mere-existence theorem. Function.update_self restores exactly
   the given S family, so the resulting perfectness is about the original object.
3. Split statements and small cases: PASS; there are zero split-off statements,
   zero added holes and zero new nodes. Reviewed the private helpers as well.
   The empty coproduct gives the zero finitely presented sheaf; the rank-one term
   and zero off-degree terms give the strictly perfect unit. These arguments apply
   to empty schemes and opens. The affine cover construction requires a point only
   when proving the cover condition at that point, so an empty T causes no gap.
   The support construction uses the actual reduced closed immersion and proper
   composition. The comparison c is the one obtained from the supplied predicate,
   not an arbitrary replacement with easier invertibility.
4. Route, searches and pruning: PASS. Read the proper-support, affine calculation,
   affine-locality, open-cover detector, and global canonical-map modules. Local rg
   searches and an independent Mathlib grep for finite presentation of zero found
   no usable shorter public replacement. The matching localization/open-cover
   helpers elsewhere are private; the global canonical theorem has an existential
   conclusion and cannot directly prove this universal comparison assertion.
   The five added imports serve only proofs; retained public imports serve the
   statement. The report accounts for every omitted old proof dependency:
   lem-pc-rf-base-change-flat-module and
   lem-weil-pbc-closed-subset-proper-over-base-properties. The redundant direct
   support-definition import is also accounted for; its node remains used.
   Read dag/units/sk-thm-picard-semicon.json: its realized.statement and step lists
   are empty, and the perfect-direct-image plus arbitrary-base-change unit route
   remains. Checked the specialization against [Tag 0B91](https://stacks.math.columbia.edu/tag/0B91)
   and [Tag 0A1H](https://stacks.math.columbia.edu/tag/0A1H).
5. DAG agreement: PASS. Parsed and compared both node records. Only proof,
   proof_deps and proof_origin changed. The three steps match localization/unit
   preparation, proper-support specialization, and canonical affine-local assembly.
   Their uses have exactly the recorded proof_deps union. Statement, stmt_deps,
   source, unit, chapter and existing lean signature record are unchanged.

Second reading changed only this report, adding the independent checks and their
results. No Lean repair was needed; all four helper proofs and the main reduction
were retained. Closed holes: AlgebraicGeometry.perfect_derivedDirectImage_baseChange
(one of one). Added holes: none. Split-off statements: none. The scratch axiom-check
copy was removed before delivery.
