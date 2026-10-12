## What changed

Preserved every existing signature and definition in
Sheaf.AlgebraicGeometry.HigherDirectImageRawDiagram. Replaced the conjunction's hole
with direct proofs of zero and addition preservation and applications of separately
stated identity and composition laws. Added two proof-only imports. The two generic
five-factor helper lemmas are fully proved and private.

## Proved and sorry left

Closed the direct hole in
AlgebraicGeometry.Etale.higherDirectImageRawOverPullback_functorial
(lem-sbc-higher-image-raw-pullback-functorial). This is a decomposition, not a proof
free of sorryAx: one upper hole closed, two lower holes added, net minus one.
Zero and addition are proved from Mathlib additivity and bilinearity without new holes.
No sorry remains in the item's module.

The two added holes are:

- AlgebraicGeometry.Etale.higherDirectImageRawOverPullback_id
  (lem-sbc-higher-image-raw-pullback-identity).
- AlgebraicGeometry.Etale.higherDirectImageRawOverPullback_comp
  (lem-sbc-higher-image-raw-pullback-composition).

Each is a named public theorem in a separate module, with source and a complete proof
in words, and proof exactly `by sorry`. Neither repeats the four-clause statement:
identity and composition are independent, strictly smaller parts. No data are chosen
from them. Standard-axiom independence awaits these lower proofs and existing imported
dependencies; the raw presheaves and maps remain the explicit constructions.

## No longer needed

Removed the unused proof-only import
`WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`. Its declarations remain
available through the statement dependency; no library module is claimed pruned. The old direct proof dependency
`lem-weil-pbc-inverse-image-composition` is no longer used directly by the parent
proof; it remains in the two split nodes' proof plans. The original public import remains necessary for the
signatures and explicit raw pullback. The parent's direct inverse-image-composition
proof dependency is replaced by the two narrower raw-law nodes; it is still needed
transitively for their coherence proofs, so no library module is claimed pruned.
No unit statement or realized proof step is bypassed. The unit record
sk-lem-failure-field has empty realized statement and step arrays.

## Where the brief, the DAG or earlier work was wrong

The plan's inverse-image composition dependency supplies the underived comparison,
not by itself the single-complex and shift comparison cancellations of raw derived
Hom. These are now explicit identity and composition tasks. Existing Ext identity
comparison is for natural-number Ext; it does not immediately give arbitrary integer
shifts with the supplied D-plus instance. Existing single-complex composition and
higher-image transition comparisons do not directly state the raw laws. Searches
found no exact shortcut. The direct additive proofs compile by applying generic
five-factor lemmas, avoiding expensive simplification of the bundled Hom-group carrier.

Edge cases checked mathematically: zero coefficients, zero classes, zero and negative
degree, identity arrows in either position of a composite, and empty schemes. The
canonical unit and associativity comparisons apply in these cases. No scheme
finiteness or limit hypothesis is used or added.

## New nodes

lem-sbc-higher-image-raw-pullback-identity records only the identity law. Module:
Sheaf.AlgebraicGeometry.HigherDirectImageRawPullbackIdentity. Its source comparison
and coefficient comparison are identified by underived unit coherence; naturality
of the localized identity comparison and shift compatibility cancel the other factors.

lem-sbc-higher-image-raw-pullback-composition records only composition. Module:
Sheaf.AlgebraicGeometry.HigherDirectImageRawPullbackComposition. Naturality,
single-complex composition compatibility, inverse-image associativity and shift
compatibility combine the two raw formulas. The parent proof node now matches this
reduction. No change record or forced adaptation is required.

## Earlier second reading (a previous round; superseded)

1. Compared the delivered item with the repository using diff and the declaration
   reader. Every existing declaration signature and every definition body is unchanged;
   only private proof helpers, local elaboration options, two plain proof imports, and
   the conjunction proof were added. Restored the parent node's accidentally escaped
   statement and all other immutable fields from the repository. No statement change
   or change record is needed. Verdict: pass.
2. Compiled all three modules in dependency order with lcompile.py: no errors or
   warnings. A first compile timed out under heavy machine load; a retry compiled
   the split modules in 4.7 and 4.8 seconds and the item in 28.0 seconds. A scratch
   copy with #print axioms for every public declaration of the item and both split
   theorems compiled. Its only axioms were propext, Classical.choice, Quot.sound,
   and sorryAx. No forbidden declaration or attribute, hollow definition, or arbitrary
   existence witness was added. The only textual holes are the two reported named
   theorems. This remains a decomposition (one hole closed, two added), not a
   completed sorry-free functoriality proof. Verdict: pass as decomposition.
3. Read the explicit five-factor formula and both new docstring proofs. Identity
   uses inverse-image unit coherence and the localized single/shift comparisons;
   composition uses associativity on both the source and coefficients, then
   compatibility with single complexes and shifts. Neither asserts the entire parent
   conjunction. Both are true, needed, strictly smaller clauses, with unchanged
   hypotheses and all integer degrees. Zero objects, zero classes, negative degree,
   identity factors, and empty schemes cause no extra hypotheses. Independently
   searched leanfinder for derived pullback composition with shifts/single complexes,
   loogle for mapDerivedCategoryPlusNatIso, and Mathlib grep for derived identity,
   composition and map_naturality. Read EtalePullbackSingleComp,
   HigherDirectImageTransitionIdentity and ExtExactFunctorIdentityComparison.
   ShiftedHom.map_naturality and the existing comparison lemmas supply pieces, but
   none directly proves either complete raw law; the identity transport still needs
   the bounded-below single and shift comparison calculation. Both new nodes carry
   sources and full proof plans. Verdict: pass; no quick complete closure found.
4. The parent starts with direct Mathlib additivity and bilinearity, then applies
   the two smaller laws. Each of its three imports is used; the new imports are
   proof-only. Named the removed direct DAG dependency explicitly under No longer
   needed; it is retained transitively, so no module is pruned. Inspected unit
   sk-lem-failure-field: its realized statement and step arrays are empty and are
   unchanged. No realized unit route is bypassed. Verdict: pass.
5. Checked every proof_deps set against the union of proof-step uses, the parent's
   new three-step reduction, all required new-node fields, and the verbatim Lean
   statements of both new nodes (also against the declaration reader's whitespace
   normalization). Existing parent metadata and statement are preserved.
   Verdict: pass.

Second reading changed DAG LaTeX escaping (including restoring the parent statement)
plus report clarification of the old direct dependency and this review record.
No Lean proof, signature, definition, or import needed repair.

Delivery tool failure after the successful dry run (commit f614cb5cd2): the push
invocation of deliver3.py fails in check_import_sources with ImportError: cannot
import name 'refuse_missing' from the clone's tools/import_cycles.py. The launcher
copy provides this function, but the delivery process resolves the older clone
module. No tool was edited or bypassed; the reviewed sandbox remains ready.


## Second reading by E2

1. Compared the item against the current repository with `diff -u`. Every existing
   signature, docstring, and definition body is byte for byte unchanged. The edits
   are two private proved helpers, two local elaboration options, the conjunction
   proof, and proof-only imports. The current baseline also contains a redundant
   plain UpperLowerStar.Defs import which this delivery removes. No public import
   changes in the item and no change record is required. Verdict: pass.
2. Compiled the three delivered modules with lcompile.py --all: composition 6.9 s,
   identity 6.6 s, item 44.2 s; no errors or unexpected warnings. Compiled the
   scratch Review.lean with #print axioms for all six public declarations of the
   item and both split theorems: only propext, Classical.choice, Quot.sound and
   sorryAx. Searched all delivered Lean for forbidden declarations and holes:
   exactly the two reported named theorem holes, none in a definition. The
   explicit object and map constructions are unchanged and choose no arbitrary
   witness. Verdict: pass as decomposition; not a sorry-free proof.
3. Read both new modules, their full node statements, and their proof docstrings,
   against the five-factor definition in HigherDirectImageRawOverNaturality.
   Source checked: Stacks Tags 09Z1 (lemma-relative-colimit) and 015F
   (lemma-right-derived-exact-functor). 09Z1 supplies the surrounding cohomology
   comparison context, not an explicit raw integer-degree coherence formula;
   015F supplies exact-functor localization. The detailed canonical comparison
   argument is given in the docstrings rather than attributed verbatim to those
   tags. Identity uses the unit comparison on both the source and coefficients;
   composition uses associativity and single/shift compatibility on both sides.
   No qcqs or limit hypothesis is consumed by either argument. Checked zero
   sheaves, zero classes, q = 0, negative q, identity factors, and empty schemes:
   the same categorical comparison equalities apply. Each hole is a strictly
   smaller, needed clause of the original four-clause conjunction, with no added
   hypothesis. Independently searched leanfinder for bounded-below derived
   pullback identity on shifted Hom, loogle for ShiftedHom.map_naturality, and
   Mathlib grep for the raw laws and derived identity comparison. Read
   EtalePullbackSingleComp, HigherDirectImageTransitionIdentity, and
   CategoryTheory/ExtExactFunctorIdentityComparison. They provide pieces but no
   complete raw law for these supplied D-plus instances and all integer degrees.
   No complete closure was apparent in a few minutes. Verdict: pass.
4. The item proves zero and addition directly using Functor.map_zero/map_add
   and bilinearity; identity and composition then use the two narrower laws.
   Both new imports are plain proof imports. The public raw-naturality import
   remains necessary for signatures and constructions. Corrected No longer
   needed to name the actual removed import, in addition to the removed direct
   parent proof dependency. The latter remains transitively needed. Inspected
   dag/units/sk-lem-failure-field.json: realized.statement is [] and
   realized.steps is [[]]; no realized route is bypassed. Verdict: pass.
5. Parsed all three nodes: every proof_deps set equals the union of proof-step
   uses. The existing parent differs only in proof, proof_deps and proof_origin.
   Both new nodes have source, searches, creation, blueprint, chapter/unit and
   Lean records, with statements matching their modules. The parent records
   precisely the additive proof and two clause applications. Verdict: pass.

This second reading changed the report's inaccurate claim that no original import
was removed and appended this independent review. No Lean repair was needed.
The earlier tool failure above is historical; delivery is retried with the current tool.
