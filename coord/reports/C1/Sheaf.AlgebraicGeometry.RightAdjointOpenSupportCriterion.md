## What changed

Returned-delivery repair: removed the duplicate private
`AlgebraicGeometry.restriction_zero_iff_stalks` from
`RightAdjointOpenSupportOfBounded`. It now imports `RightAdjointOpenUnitConeTest`
and uses the same theorem there. The retained helper is now public, with the
identical explicit binders and proposition and its original complete proof.
Both modules are new in this delivery; no existing library interface changes.
The support-extension DAG node records this shared dependency.

Proved `AlgebraicGeometry.rightAdjoint_open_support_criterion` with its original
signature and visibility unchanged. Its bounded and unbounded equivalences use a
pointwise supported-cone test and a proved converse for supported objects. Its third
clause combines these equivalences with the proved extension of support preservation.

Added two modules with proved public theorems:
`Sheaf.AlgebraicGeometry.RightAdjointOpenUnitConeTest` transports the existing support
triangle to the supplied open-adjunction unit and applies the triangulated right
adjoint and restriction; `Sheaf.AlgebraicGeometry.RightAdjointOpenSupportOfBounded`
implements the perfect-generator and telescope argument. Both have matching DAG nodes.

The latter proof includes a finite-cover lower bound for perfect complexes, lifts
ambient colimiting cofans explicitly to the quasi-coherent full subcategory, and
transports countable coproduct preservation along the discrete ULift equivalence.
The source is Stacks Tag 0E4G, Lemma 48.4.3, and its cited Tags 0A9A and 09SN.
The source page was read at https://stacks.math.columbia.edu/tag/0E4G.

After the returned-delivery repair, all three modules compile together in import
order through `lcompile.py`, without warnings: cone test 16.2 seconds, support
extension 19.6 seconds, and criterion 39.2 seconds. There is no existing statement,
definition, public import, or interface change, and no forced adaptation.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.rightAdjoint_open_support_criterion`
(node `lem-sc-right-adjoint-open-support-criterion`). All three clauses are proved
from existing library declarations and the two proved helper theorems.

Also proved `AlgebraicGeometry.rightAdjoint_open_unit_cone_test`
(node `lem-sc-right-adjoint-open-unit-cone-test`) and
`AlgebraicGeometry.rightAdjoint_open_support_of_bounded`
(node `lem-sc-right-adjoint-open-support-of-bounded`), together with all private helpers and the shared public
`AlgebraicGeometry.restriction_zero_iff_stalks` helper.

Holes closed: one original. Holes added: zero. No `sorry` remains in any delivered
module. Imported library declarations retain their existing proof dependencies;
this report makes no claim that the entire target closure is axiom-free.

## No longer needed

Removed the duplicate restriction/stalk proof and the direct import
`Mathlib.Algebra.Category.Grp.Zero` from `RightAdjointOpenSupportOfBounded`;
that import remains used in the cone-test module. No additional module or node
is pruned by this repair.

Removed the direct proof import `Sheaf.Algebra.Homology.KInjectiveRestrictOpen`
and the direct proof dependency `lem-sc-derived-k-injective-restrict-open`.
The original Lean statement already tests the restricted image of the specified
open-adjunction unit, so it does not require construction of the two remaining
canonical isomorphisms in equation (the project server). No unit statement or realized proof
step is bypassed: `sk-thm-picard-duality` has no realized nodes for this argument.
This is a removed dependency of this item; other target paths may still need it.

Removed direct imports `Sheaf.AlgebraicGeometry.OpenRestrictionSupportTriangle` and
`Sheaf.AlgebraicGeometry.SupportedDerivedGeneratedPerfect` from the original module.
They remain used by the new cone-test and support-extension modules respectively,
so their nodes and modules are retained. No other original proof dependency is pruned.

## Where the brief, the DAG or earlier work was wrong

The returned delivery duplicated the identical private restriction/stalk theorem
in both new helper modules. The earlier second reading missed this duplication.
This repair retains one proof and imports it in the other module, as requested
by `tools/import_prune_check.py`. The second-reading section below records the
previous delivery and requires a fresh reading after this repair.

The earlier sandbox report said the support-extension theorem was left with `sorry`,
but its actual file contained an attempted complete proof with six compiler errors.
The proof is now repaired, and this report reflects the compiled files.

The support triangle supplies an existential open adjunction whereas the target
uses its supplied `adjOpen`. The cone-test proof explicitly transports the triangle
by uniqueness of adjoints, retaining the target's canonical unit. The third triangle
arrow includes the full-subcategory inclusion's shift comparison.

The generation theorem requires derived localizations on every open in the ambient
Hom universe; the existing proved `nonempty_derivedOpenLocalization` supplies them.
The existing `derivedLocallyBoundedBelowGlobal` assumes Noetherianity, unavailable
here, so the finite-cover argument is proved directly. Countable indices require
ULift transport because the sum hypothesis and closure theorem use Type u.

No statement is disputed; no target or existing interface was changed.

## New nodes

`lem-sc-right-adjoint-open-unit-cone-test` records the proved pointwise construction
in `lean/Sheaf/AlgebraicGeometry/RightAdjointOpenUnitConeTest.lean`. It gives a supported
cone, its conditional lower bound, and the pointwise zero/isomorphism test.

`lem-sc-right-adjoint-open-support-of-bounded` records the proved support extension
in `lean/Sheaf/AlgebraicGeometry/RightAdjointOpenSupportOfBounded.lean`. It retains the
perfect-generator and telescope route, including its coproduct and universe glue.
Neither new node is an outstanding proof item. No change record is required.

## Earlier second reading (a previous round; superseded)

1. **Interfaces: pass.** Compared every delivered module with the read-only
   repository. The only pre-existing module is the criterion module: its theorem
   signature is byte-for-byte identical, its docstring is unchanged, and its
   public imports are unchanged. The other two modules are new. No existing
   definition, hypothesis, conclusion, or visibility changed; no change record
   or forced adaptation is needed.
2. **Proofs: pass.** Independently compiled all three files in import order with
   `lcompile.py`: support extension 26.7 s, cone test 19.9 s, criterion 50.8 s,
   with no warnings. Scanned all delivered sources: no `sorry`, `axiom`,
   `unsafe`, `opaque`, `implemented_by`, or `extern`. A scratch copy with
   `#print axioms` for all three public theorems compiled and reported exactly
   `propext`, `Classical.choice`, `Quot.sound`, and imported `sorryAx`. Thus the
   original local hole is closed, with no new holes; this does not certify the
   imported library's remaining holes. The private triangle definition builds
   its data explicitly. Existential generators are eliminated inside a proof,
   and no arbitrary witness from an open existence theorem defines new data.
3. **New statements: pass.** No statement was split off with `sorry`. Read both
   new proved theorems and every private helper. The cone test retains the
   supplied adjunction unit via the adjoint-uniqueness automorphism, and the
   full-subcategory triangle uses the inclusion's shift comparison. The support
   extension uses a finite cover to bound the perfect generator, explicitly
   lifts the ambient coproduct universal property, and transports the countable
   coproduct hypotheses along `Discrete (ULift ℕ) ≌ Discrete ℕ`. Checked zero
   objects, empty/full opens, the empty finite subcover, and the initial zero
   telescope stage. The two helpers are strictly parts of the original argument
   and have complete source/proof docstrings and matching nodes.
4. **Route and pruning: pass.** Independently read Stacks
   [Tag 0E4G](https://stacks.math.columbia.edu/tag/0E4G), Lemma 48.4.3 and its
   preceding canonical-map test. Searched `lean/Sheaf` and `lean/WeilConjectures`
   by restriction/zero, perfect/lower-bound, and support-preservation concepts;
   the analogous restriction/stalk helper in the proper-flat module is private,
   and the perfect boundedness theorem for ring modules does not give the
   scheme finite-cover bound. Independent `msearch.py` leanfinder search for a
   coproduct-preserving triangulated kernel containing a generator found generic
   homological-kernel facts, not a shorter scheme reduction; loogle confirmed
   the triangle test already used; grep found no replacement. Imports serve
   signatures or the displayed proof APIs. The report lists all three old
   direct proof dependencies removed from the criterion: the support triangle
   and supported-generation dependency remain through the new helpers; only
   the K-injective restriction dependency is pruned from this route. The unit
   `sk-thm-picard-duality` has empty realized statement/step lists, and its route
   and record are unchanged.
5. **DAG: pass.** Read all three delivered nodes and the original node. Each
   `proof_deps` is exactly the union of its proof-step `uses`; the steps and
   origins describe the actual cone transport, zero-object converse, and
   perfect-generator/telescope proof. Both new `lean.statement` values occur
   verbatim in their files. New nodes contain source, searches, status, creation,
   blueprint, chapter/unit, and Lean records. Existing non-owned fields and the
   node's statement are unchanged.

Second-reading changes: appended this independent review and its verification
evidence. No mathematical, Lean, or DAG repair was necessary.


## Second reading by C1

1. **Interfaces: pass.** Freshly compared the delivered criterion module against
   the repository with `diff` and checked its entire existing theorem signature
   byte for byte. The signature, docstring, visibility, and public imports are
   unchanged. The other two modules are new; no change record is required.
2. **Proofs: pass.** Independently compiled all three delivered files in import
   order with `lcompile.py`: cone test 18.0 s, support extension 22.6 s, criterion
   37.5 s, without warnings. Scanned every delivered source for forbidden
   constructs and holes: none. A scratch module explicitly importing all three
   modules printed axioms for the four public theorems. The shared
   `restriction_zero_iff_stalks` uses only `propext`, `Classical.choice`, and
   `Quot.sound`; the other three additionally use imported `sorryAx`, and no
   other axiom. The scratch source was removed. The triangle definition is an
   explicit construction. Generator and telescope witnesses are eliminated only
   inside theorem proofs; the chosen open-localization family comes from the
   existing proved size theorem, not an arbitrary unproved existence assertion.
3. **New statements: pass.** No sorry statement is split off. Read every helper
   and both new proved theorems. Checked zero objects, empty/full opens, an empty
   finite subcover, and the zero initial telescope stage. The cone test preserves
   the supplied unit by adjoint uniqueness, including the shift comparison in
   the full-subcategory triangle. The sum proof lifts the coproduct universal
   property and transports countable indexing across ULift. Both new theorems
   are strictly parts of the criterion, with source/proof docstrings and nodes.
   The returned duplicate restriction/stalk proof is absent: support extension
   now imports and uses the one public proof in the cone-test module.
4. **Route and pruning: pass.** Read Stacks Tag 0E4G, Lemma 48.4.3 and its
   preceding unit-map criterion. Fresh leanfinder search for perfect complexes
   bounded below on a quasi-compact scheme found cover results, not a replacement;
   loogle confirmed the triangle test already used; grep and repository searches
   found no shorter applicable reduction. The existing pro-etale boundedness
   result has a different category, and the scheme local-to-global result assumes
   Noetherianity. Proof-only imports remain plain imports. The report accounts
   for every removed old proof dependency: support triangle and supported
   generation remain through the helpers, while K-injective restriction is not
   needed for the fixed unit-map statement. The unit's realized lists are empty;
   its statement and route are unchanged.
5. **DAG: pass.** Read all three nodes, compared the original node, and checked
   each proof-dependency list against the union of proof-step uses. Only `proof`,
   `proof_deps`, and `proof_origin` of the original node changed. The two new
   nodes contain the required source, search, creation, blueprint, chapter/unit,
   and Lean records; their Lean statements occur verbatim in their files. The
   shared restriction/stalk dependency is recorded in the support-extension node.

Second-reading changes: appended this fresh review and verification evidence.
No further Lean or DAG repair was necessary after the duplicate-helper repair.
Holes closed: `AlgebraicGeometry.rightAdjoint_open_support_criterion` (one).
Holes added: none. This is a proof of the local hole, not a decomposition or a
claim that the imported closure is already axiom-free.
