## What changed

Repair upstream review #1428: removed
`CochainComplex.termwise_product_isKInjective_and_isLimit` and its private
`productHomotopy` and `mapProduct` helpers from
`Sheaf.Algebra.Homology.KInjectiveProducts`. The module retains exactly its
original public imports as a compatibility module and drops its proof-only
DerivedCategory.KInjective import.

All three actual callers are adapted, with identical existing signatures and
visibility: `Sheaf.CategoryTheory.Triangulated.RightDerivedFunctorCountableProducts`,
`Sheaf.CategoryTheory.Triangulated.DerivedLimitTowerTriangle`, and
`Sheaf.Topology.RingedSpaceRGammaDerivedLimit`. They use the existing
`HomotopyCategory.isLimitFanQuotient`, right-orthogonal closure under limits, and
`CochainComplex.IsKInjective.Qh_map_bijective`, followed by the existing
`DerivedCategory.quotientCompQhIso` comparison. The Hom bijections transfer the
universal property directly inside their proofs; no global theorem or alias
replaces the duplicate. The tower-triangle caller replaces the retired private import
with a private import of the source HomotopyCategory.Products module. The
right-derived-functor caller already imports that source publicly and drops the
retired private import. The ringed
space caller already imports that module publicly and only drops the retired
private import. Stale references in the docstrings of the adapted callers now
name the available APIs.

The node lem-pc-ringed-space-product-kinjective records retirement with
`lean: null`: the full arbitrary-family statement has no verified Lean
realization in this snapshot. The canonical upstream pair remains an unverified
citation only. The returned delivery repair also replaces the proof-origin place
with the reviewer's exact text and corrects citation wording in this report and
the change record. Its mathematical statement is unchanged. Change record:
`coord/changes/remove-KInjectiveProducts-duplicate.md`.

## Proved and sorry left

This is a duplicate-removal repair of a module that already had zero sorries:
zero holes closed, zero holes added, zero split off. The removed declaration is
`CochainComplex.termwise_product_isKInjective_and_isLimit`; it was already proved.
There are no remaining sorries in the item or any adapted module. The existing
caller declarations `AlgebraicGeometry.Scheme.rightDerivedFunctor_preservesCountableProducts`,
`CategoryTheory.derivedCategory_towerLimit_triangle`, and
`AlgebraicGeometry.RingedSpace.rgamma_derivedLimit` retain complete proofs.
The private ringed-space preservation lemma also retains its complete proof.
This is repair work, not additional sorry-ledger progress.

## No longer needed

The three actual callers no longer import `Sheaf.Algebra.Homology.KInjectiveProducts`;
no library source has another import of that module. That compatibility module
and its duplicate conjunction theorem can leave the target import closure.
The item drops `Mathlib.Algebra.Homology.DerivedCategory.KInjective` as a private
proof import. The old private `productHomotopy` and `mapProduct` declarations
are removed. The available source product API replaces the homotopy assembly;
the localized universal-property argument remains local in each required caller.

No supporting mathematical node is claimed globally unnecessary: the product
fact of lem-pc-ringed-space-product-kinjective is still used, now through the
existing APIs. The retired module has no remaining direct importer after this set.
No new nodes or public declarations are introduced.

## Where the brief, the DAG or earlier work was wrong

The previous attempt treated zero sorries as a stale dispatch and missed the
explicit duplicate repair. The item is listed in coord/repairs.txt and requires
retirement even though its old proof was complete.

The upstream review cites `CochainComplex.isKInjective_of_isLimitFan` and
`DerivedCategory.isLimitFanMkQObjOfIsKInjective` in upstream DerivedCategory/Products.lean.
Neither declaration nor that source exists in the installed project, source
checkout or Mathlib snapshot. We cannot truthfully import them or certify their
signatures. Instead, all local uses are proved from the available source and
Mathlib APIs cited above, without adding a duplicate under those names.
The mathematical statement of the node remains unchanged; its upstream
citation is explicitly marked as unverified in this snapshot.

All three callers use countable families in categories with countable products,
so the available homotopy product theorem applies. K-injectivity follows from
closure of the right orthogonal of acyclic complexes under limits. To transfer
the universal property, essential surjectivity chooses a representative of each
cone point; that representative is uniquely specified up to isomorphism by the
functor's object-preimage API, and no data are chosen from a sorry theorem.
Hom-bijection inverses lift the legs, the homotopy product supplies the lift,
and injectivity proves its uniqueness. There is no new arbitrary witness chosen
from an unproved mere-existence result, no statement weakened, and no unit route
bypassed.

## Forced adaptations

The interface change removes the name used in all three original caller proofs.
The original compiler error against the changed item is
`error(lean.unknownIdentifier): Unknown constant
CochainComplex.termwise_product_isKInjective_and_isLimit`, followed by the
failed `rcases` of that application. The dry-run tool checks each original
against the baseline and again against the delivery overlay; its exact evidence
is appended to the delivered report.

- `Sheaf.CategoryTheory.Triangulated.RightDerivedFunctorCountableProducts`:
  remove the private item import and replace the removed application at original line 86
  with existing product/Hom APIs and the direct cone transfer. The local
  K-injective instance required by the unchanged later proof is retained.
- `Sheaf.CategoryTheory.Triangulated.DerivedLimitTowerTriangle`:
  replace the private item import and the removed application at original line 65
  with the same product/Hom APIs. The unchanged Roos triangle argument needs the
  resulting localized cone's limit property.
- `Sheaf.Topology.RingedSpaceRGammaDerivedLimit`:
  remove the private item import and replace the removed application at original
  line 80 using its already-public source Products import. The local K-injective
  instance and localized product cone serve the unchanged derived-section proof.

The original declarations' binders, universes, statements, visibility and later
proof steps are unchanged. Local docstring references in the first two adapted
files are updated because the cited old declaration is removed. The two other
library docstrings mentioning the old name are historical prose references only,
have no declaration use, and are not adapted under the forced-change rule.


## Earlier second reading (a previous round; superseded)

1. Compared all four delivered Lean files with the repository using `diff` and
   the declaration parser. All four surviving declarations (including the
   private ringed-space preservation lemma) retain exactly their statements and
   visibility. The only removed declarations are the recorded duplicate theorem
   and its two private helpers. No definition or target statement changes.
2. Compiled the complete delivered set locally in import order: all four files
   passed without warnings. Read the three replacement product arguments: the
   homotopy product gives K-injectivity by right-orthogonal closure; the Hom
   bijections lift arbitrary derived cones and prove uniqueness; the comparison
   isomorphism gives the original localized projections. No delivered source
   contains `sorry` or a forbidden declaration mechanism. Scratch copies print
   the axioms of the three public caller theorems; the delivery probe additionally
   checks every declaration, including the private lemma.
3. No statements or holes are split off, and no new nodes are introduced. Read
   the available upstream homotopy Products module, the right-orthogonal closure
   instance, and Mathlib's K-injective Hom comparison. A fresh search for product
   closure and the cited canonical names found no missing shorter theorem in the
   installed snapshot. The full arbitrary-family node is unchanged; the local
   caller proofs need only countable products, already present in their original
   hypotheses. The absent canonical pair is only a bibliographic citation from
   review #1428, not a locally certified realization of that general statement.
4. The retired module has exactly three direct importers, all adapted here;
   other mentions are prose. Its proof-only DerivedCategory.KInjective import
   and both private helpers are removed. No old mathematical proof dependency
   becomes globally unnecessary: the same product and Hom-comparison facts are
   still used locally. Read the unit `sk-thm-picard-duality`: this supporting node
   is not a replacement for a realized unit statement or step, and the unit's
   route is unchanged. Public imports of the compatibility and adapted modules
   are preserved under the forced-adaptation constraint.
5. Compared the node with its baseline: its mathematical statement and dependency
   union are unchanged. Its proof and origin now describe retirement and the
   actual local countable-product argument. The Lean citation explicitly says
   the review's inferred upstream path and signatures are unverified locally.
   No new node fields or new mathematical claims require review.

Second-reading changes: removed the redundant private Products import in
`RightDerivedFunctorCountableProducts` (the same module is already publicly
imported), restored the blank line before the compatibility module docstring,
clarified the node's proof and unverified upstream citation, and corrected the
report and change record accordingly. No proof repair was needed. Zero holes
closed, zero holes added; this delivery retires a duplicate and prunes its module.

## Forced adaptations

### Sheaf.CategoryTheory.Triangulated.DerivedLimitTowerTriangle
Original against changed dependencies failed:
```
/tmp/forced-adaptation-t7vg9pgs/lean/Sheaf/CategoryTheory/Triangulated/DerivedLimitTowerTriangle.lean:65:23: error(lean.unknownIdentifier): Unknown constant `CochainComplex.termwise_product_isKInjective_and_isLimit`
/tmp/forced-adaptation-t7vg9pgs/lean/Sheaf/CategoryTheory/Triangulated/DerivedLimitTowerTriangle.lean:65:9: error: Tactic `rcases` failed: `x✝ : ?m.263` is not an inductive datatype

(with the modules compiled into /tmp/forced-adaptation-t7vg9pgs/.lbuild) [2.0 s]
```
Adapted module compiled in the delivered set. Explain the forced changed lines in the change record; CODEX verifies them.

### Sheaf.CategoryTheory.Triangulated.RightDerivedFunctorCountableProducts
Original against changed dependencies failed:
```
/tmp/forced-adaptation-bv9g4jiw/lean/Sheaf/CategoryTheory/Triangulated/RightDerivedFunctorCountableProducts.lean:86:27: error(lean.unknownIdentifier): Unknown constant `CochainComplex.termwise_product_isKInjective_and_isLimit`
/tmp/forced-adaptation-bv9g4jiw/lean/Sheaf/CategoryTheory/Triangulated/RightDerivedFunctorCountableProducts.lean:86:11: error: Tactic `rcases` failed: `x✝ : ?m.467` is not an inductive datatype

(with the modules compiled into /tmp/forced-adaptation-bv9g4jiw/.lbuild) [2.8 s]
```
Adapted module compiled in the delivered set. Explain the forced changed lines in the change record; CODEX verifies them.

### Sheaf.Topology.RingedSpaceRGammaDerivedLimit
Original against changed dependencies failed:
```
/tmp/forced-adaptation-avc81mu8/lean/Sheaf/Topology/RingedSpaceRGammaDerivedLimit.lean:80:27: error(lean.unknownIdentifier): Unknown constant `CochainComplex.termwise_product_isKInjective_and_isLimit`
/tmp/forced-adaptation-avc81mu8/lean/Sheaf/Topology/RingedSpaceRGammaDerivedLimit.lean:80:11: error: Tactic `rcases` failed: `x✝ : ?m.472` is not an inductive datatype

(with the modules compiled into /tmp/forced-adaptation-avc81mu8/.lbuild) [20.9 s]
```
Adapted module compiled in the delivered set. Explain the forced changed lines in the change record; CODEX verifies them.

## Second reading by U2

1. Compared all four delivered modules against the repository with unified diffs
   and a declaration-head comparison through each assignment token. Every
   surviving declaration has a byte-identical signature, including the private
   ringed-space preservation lemma. Only the recorded duplicate theorem and its
   two private helpers are removed. The change record covers that removal and
   the three forced caller adaptations; no target or definition changes.
2. Independently compiled the four delivered files in import order with
   lcompile.py: all passed without warnings. Compared scratch copies to the
   delivered sources: their only additions are the three public theorems'
   `#print axioms` commands. All three print exactly propext, Classical.choice,
   and Quot.sound. No delivered Lean source contains sorry, axiom, unsafe,
   opaque, implemented_by, or extern. Read each replacement argument: the
   quotient product supplies the limiting homotopy cone, right-orthogonal
   closure proves K-injectivity, Hom bijections transfer arbitrary derived
   cones and prove uniqueness, and quotientCompQhIso identifies the specified
   localized projections. No data depend on an unproved existence theorem.
3. No new statements, nodes, or holes are split off. Read the source homotopy
   Products module, its right-orthogonal closure instance, and Mathlib's
   K-injective Hom comparison. Fresh searches for limit transfer through Qh
   and the canonical pair found no additional direct theorem in this snapshot.
   All callers need only countable products and already assume their existence;
   the arbitrary-family mathematical node is retained unchanged and has no
   verified Lean realization after retirement.
4. Verified the three direct importers are precisely the three adapted files;
   remaining references to the retired declaration are historical docstrings.
   The removed proof-only import and helpers are listed under No longer needed,
   and no old mathematical proof dependency is claimed unnecessary. Public
   imports stay unchanged. Read sk-thm-picard-duality and its realized field:
   this supporting node is not a realized unit statement or step, and this
   repair changes no unit route. The compatibility module leaves the target
   import closure when these three private imports are removed.
5. Compared the node JSON against the repository: only proof, proof_origin,
   and lean change. The statement, stmt_deps, proof_deps, and unit stay
   identical; the dependency union matches the recorded proof. The replacement
   proof_origin.place exactly matches the returned review, and lean is null.
   The upstream pair is explicitly an unverified citation, not a Lean mapping.

Second-reading changes: corrected one residual sentence in the change record
that still described the arbitrary-family statement as attached to the upstream
pair. No Lean repair was needed. Zero holes closed, zero holes added, zero split
off; this is duplicate-removal repair and module pruning, not new proof progress.

## Forced adaptations

### Sheaf.CategoryTheory.Triangulated.DerivedLimitTowerTriangle
Original against changed dependencies failed:
```
/tmp/forced-adaptation-nsewig31/lean/Sheaf/CategoryTheory/Triangulated/DerivedLimitTowerTriangle.lean:65:23: error(lean.unknownIdentifier): Unknown constant `CochainComplex.termwise_product_isKInjective_and_isLimit`
/tmp/forced-adaptation-nsewig31/lean/Sheaf/CategoryTheory/Triangulated/DerivedLimitTowerTriangle.lean:65:9: error: Tactic `rcases` failed: `x✝ : ?m.263` is not an inductive datatype

(with the modules compiled into /tmp/forced-adaptation-nsewig31/.lbuild) [1.7 s]
```
Adapted module compiled in the delivered set. Explain the forced changed lines in the change record; CODEX verifies them.

### Sheaf.CategoryTheory.Triangulated.RightDerivedFunctorCountableProducts
Original against changed dependencies failed:
```
/tmp/forced-adaptation-oun37l5i/lean/Sheaf/CategoryTheory/Triangulated/RightDerivedFunctorCountableProducts.lean:86:27: error(lean.unknownIdentifier): Unknown constant `CochainComplex.termwise_product_isKInjective_and_isLimit`
/tmp/forced-adaptation-oun37l5i/lean/Sheaf/CategoryTheory/Triangulated/RightDerivedFunctorCountableProducts.lean:86:11: error: Tactic `rcases` failed: `x✝ : ?m.467` is not an inductive datatype

(with the modules compiled into /tmp/forced-adaptation-oun37l5i/.lbuild) [2.4 s]
```
Adapted module compiled in the delivered set. Explain the forced changed lines in the change record; CODEX verifies them.

### Sheaf.Topology.RingedSpaceRGammaDerivedLimit
Original against changed dependencies failed:
```
/tmp/forced-adaptation-5n884g5b/lean/Sheaf/Topology/RingedSpaceRGammaDerivedLimit.lean:80:27: error(lean.unknownIdentifier): Unknown constant `CochainComplex.termwise_product_isKInjective_and_isLimit`
/tmp/forced-adaptation-5n884g5b/lean/Sheaf/Topology/RingedSpaceRGammaDerivedLimit.lean:80:11: error: Tactic `rcases` failed: `x✝ : ?m.472` is not an inductive datatype

(with the modules compiled into /tmp/forced-adaptation-5n884g5b/.lbuild) [17.3 s]
```
Adapted module compiled in the delivered set. Explain the forced changed lines in the change record; CODEX verifies them.
