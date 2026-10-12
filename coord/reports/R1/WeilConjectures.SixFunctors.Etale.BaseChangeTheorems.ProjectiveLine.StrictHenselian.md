## What changed

Reduced two of the five original sorries in
`WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.StrictHenselian`.
All existing declaration signatures and docstrings are unchanged.

`AlgebraicGeometry.Etale.exists_sum_eq_of_injective_projectiveLine` now obtains a
constructible representative, applies the existing finite-pushforward embedding theorem,
extends its map into the injective sheaf using `Injective.factorThru`, and proves the
finite-sum formula by mapping and evaluating the biproduct identity. This works for
henselian local bases without using separable closedness, but the original hypothesis is
retained. A declaration-local unused-section-variable linter setting preserves that
original signature without compiler warnings.

`AlgebraicGeometry.Etale.subsingleton_H_projectiveLine_closedFibre_of_injective` now splits
q = 1 from q > 1. The latter case applies the original general restriction bound with
n = 1 and the two standard affine charts, using the actual projective-space pullback
square. The former case uses the proved representation and kills every summand using the
new finite-pushforward H1 image lemma. The finite sum and the subsingleton conclusion are
proved in Lean.

Added proof-only imports of `WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Charts`,
`Sheaf.AlgebraicGeometry.ConstructibleModuleFinitePushforwardEmbedding`, and the two new
modules. No public import in the original module changed. The two new modules each contain
one public theorem, its complete proof in words, and a corresponding new node. Updated the
two existing nodes' proof plans and dependencies to reflect this reduction. No definitions,
targets or intermediate signatures were changed; no change record is needed.

## Proved and sorry left

Closed the direct sorries in:

- `AlgebraicGeometry.Etale.exists_sum_eq_of_injective_projectiveLine`
  (`lemma-weil-pbc-h1-constructible-representation`).
- `AlgebraicGeometry.Etale.subsingleton_H_projectiveLine_closedFibre_of_injective`
  (`prop-weil-pbc-p1-acyclicity`). Its residue-field alias also uses this reduction.

These are reductions from named dependencies, not unconditional sorry-free results.
The original module still has exactly these three direct sorries:

- `AlgebraicGeometry.Etale.subsingleton_H_upperStar_of_injective_of_iSup_eq_top`
  (`lemma-weil-pbc-injective-restriction-acyclicity`).
- `AlgebraicGeometry.Etale.bijective_cohomologyMap_projectiveLine_residueField`
  (`prop-weil-pbc-p1-strict-henselian-comparison`).
- `AlgebraicGeometry.Etale.exists_addEquiv_sheafFiber_baseChangeHomologyMap_strictLocal`
  (`prop-weil-pbc-strict-local-exchange`).

The delivery adds exactly these two named whole-proof sorries:

- `AlgebraicGeometry.Etale.exists_constructible_restriction_class`
  (`lem-weil-pbc-constructible-restriction-class`), in
  `Sheaf.AlgebraicGeometry.ConstructibleRestrictionClass`.
- `AlgebraicGeometry.Etale.finite_pushforward_H_one_image_eq_zero_of_henselianLocalRing`
  (`lem-weil-pbc-henselian-finite-pushforward-h1-image`), in
  `Sheaf.AlgebraicGeometry.HenselianFinitePushforwardH1Image`.

The first new theorem is only the constructible-class factorization step: it does not
produce an embedding, a finite pushforward, an injective extension, or a sum. The second
only kills the image of a single finite-constant-pushforward class: it does not assert
vanishing of all H1 classes or of any higher degree. The original statements are recovered
by genuine Lean proofs combining these distinct steps and existing dependencies.

## No longer needed

No original imports removed, and no entire previously needed branch pruned. The unit route
`sk-thm-p1` is preserved. The standard-chart theorem of
`Sheaf.AlgebraicGeometry.ProjectiveSpaceStandardCharts` need not be imported for the
acyclicity proof: the already proved `isAffineOpen_standardOpen` and `iSup_standardOpen`
in the source library provide exactly its needed cover clauses. Its twisting-module and
coordinate-section dependencies are not used by this proof. This is pruning below the
unit level, not a change of its prescribed route.

`Sheaf.AlgebraicGeometry.EtaleCohomologyPullbackFunctorial` is not needed for the finite-sum
algebra in the representation proof: Mathlib's `Sheaf.functorH`, `H.map_comp_apply`, and
additivity provide it. Its naturality content remains needed by the new image lemma's
future proof, so this is not a claim that its module is globally unreachable.

The following representation dependencies are delegated to the new constructible-class
node, not pruned: `lem-weil-pbc-module-sheaf-colimit-constructible`,
`lem-weil-pbc-module-sheaves-colimits-forgetful`,
`lem-weil-pbc-inverse-image-preserves-colimits`,
`prop-weil-pbc-inverse-image-modules-exact`, `lem-weil-pbc-cohomology-filtered-colimit`, and
`def-weil-directed-colimit-abelian-groups`.

Likewise the finite exchange, edge-map compatibility, torsor lifting, and injective-module
abelian acyclicity dependencies remain behind the new finite-pushforward image node.
A trial proof-only Gabber import was removed: its elementary forgetful-additivity instance
is proved locally by reflexivity, avoiding importing its unrelated comparison proof.

The complete accounting of old dependencies no longer used directly is as follows.
For `lemma-weil-pbc-h1-constructible-representation`, the six colimit/factorization
nodes listed above remain through `lem-weil-pbc-constructible-restriction-class`.
`lem-weil-pbc-projective-space-standard-charts` is unnecessary for this representation;
quasi-compactness and quasi-separatedness follow from properness.
`def-weil-pbc-scheme-conventions` supplies ambient definitions, not a separate proof step.
`lem-weil-pbc-cohomology-pullback-functorial` is replaced for its finite-sum algebra by
Mathlib functoriality and additivity; it remains behind the image lemma.

For `prop-weil-pbc-p1-acyclicity`, these old dependencies remain through the image lemma:
`lem-weil-pbc-finite-morphism-permanence`, `lemma-weil-pbc-finite-exchange`,
`lemma-constructible-pullback-constant`, `lem-weil-pbc-finite-pushforward-cohomology`,
`lem-weil-pbc-edge-map-base-change`, `thm-weil-pbc-finite-etale-lifting`,
`lemma-weil-pbc-h1-torsor-comparison`, `lem-weil-pbc-constant-module-sheaf-underlying`,
`lem-weil-pbc-injective-module-abelian-acyclic`,
`lem-weil-pbc-cohomology-pullback-functorial`, and
`prop-weil-pbc-inverse-image-modules-exact`.
`def-weil-pbc-henselian-terminology`, `def-weil-pbc-strict-henselian-setup`,
`def-weil-pbc-cartesian-square`, and `def-weil-pbc-underived-exchange` describe the
setting or exchange map; they are not separate invoked proof steps.
No global unreachability is claimed for any of these nodes.

The second reader removed the unused public import of `TorsionSheaf` from the new
`HenselianFinitePushforwardH1Image` module: its statement has no torsion predicate,
and compiles using its other imports alone. This changes no existing public import.

## Where the brief, the DAG or earlier work was wrong

Repair B5: corrected the finite-pushforward lifting source to Stacks 0A5H in both
Lean source locators, every locator in the new image node, both existing nodes’
`proof_origin.place`, and the New nodes paragraph. Theorem 095T paragraph 2 was
the wrong locator. No Lean statement or proof changed in this repair.

The earlier attempt incorrectly treated sorry-backed stated dependencies as an obstacle.
They are intended inputs at this stage. The two original proof plans can be implemented
using existing dependencies plus the two explicitly isolated steps above.

The recorded injective-module abelian acyclicity dependency is expressed using
`SheafOfModules` and right-derived evaluation, whereas this module uses module-valued
`Sheaf` and `Sheaf.H` (Ext). The image lemma's future proof must bridge these encodings;
the bridge has not been silently assumed to be definitional equality. Similarly, the
constructible-class step packages the colimit/forgetful/inverse-image identifications.

LeanSearch was unavailable (Internal Server Error) for both new statements. Searches with
LeanFinder and the Mathlib source did not find a matching theorem. Whole-blueprint searches
found no identical statement. Search unavailability is recorded without an absence verdict.
The literature files themselves are not populated in this remote clone; source locators
and complete arguments are taken from the existing source-cited DAG proof steps.

Edge cases checked mathematically: q = 1 and q > 1 are exhaustive for q > 0; q = 0 is
excluded only in the acyclicity theorem. The class-factorization lemma includes q = 0,
empty schemes, zero classes, and the zero coefficient ring. The image lemma includes empty
V and the zero finite module. In the representation proof, the empty biproduct case n = 0
is handled by the same total identity and finite-sum proof.

## New nodes

`lem-weil-pbc-constructible-restriction-class` records original representation Steps 2-3,
with Stacks 03SA(3) and 03Q5 as sources. Its module is
`lean/Sheaf/AlgebraicGeometry/ConstructibleRestrictionClass.lean`. It separates filtered
constructible factorization from the embedding and injective/biproduct algebra now proved.

`lem-weil-pbc-henselian-finite-pushforward-h1-image` records original acyclicity Steps 4-7,
with Stacks 0A5H, 0A48 and 03FD as sources. Its module is
`lean/Sheaf/AlgebraicGeometry/HenselianFinitePushforwardH1Image.lean`. Its scope is the image
of one finite pushforward class over an arbitrary proper henselian local base.

## Earlier second reading (a previous round; superseded)

1. I compared the delivered item module against the repository version. Existing declaration signatures and docstrings are byte-for-byte unchanged; only proof imports, proof bodies, and the declaration-local linter option changed. Verdict: pass.

2. I compiled all three delivered modules with lcompile. There are no errors, forbidden declarations, or hollow definitions. The three original direct sorries remain named, and the two new theorem sorries are named with source/docstrings and matching DAG nodes. Verdict: pass subject to those explicitly split nodes.

3. The two split statements are genuine intermediate reductions: constructible factorization and vanishing of one finite-pushforward image. They are not restatements of the item, and their edge cases are documented. Verdict: pass.

4. The proofs use existing Mathlib/library declarations and preserve the unit route. Imports are proof-only where appropriate; chart dependencies unnecessary to this proof were pruned as described above. Verdict: pass.

5. The existing nodes' proof plans and dependencies were updated to match the Lean proof, and each new node has a matching declaration and source. Verdict: pass.

I changed only this report by adding the required second-reading record; no Lean code or DAG content required repair.

## Second reading by R1

1. Compared the item module with the repository using `diff` and the delivery parser.
   Every existing declaration signature and docstring is unchanged; the parser reports
   no statement changes. No definitions, targets, or change-record adaptations were added.
   Verdict: pass.
2. Compiled all three modules with `lcompile.py --all`. Scratch copies with `#print axioms`
   check every declaration: only `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`
   from the listed open dependencies occur. No forbidden declaration or hollow definition
   occurs. The three original direct sorries and two split sorries match the report.
   Verdict: pass as reductions, not unconditional axiom-free target proofs.
3. Read both split statements and their complete docstring proofs. Checked the actual
   Stacks pages 03SA(3), 03Q5, 0A5H, 0A48, and 03FD. The finite ring is Noetherian;
   arbitrary qcqs restriction supports the colimit argument. Properness of V follows
   from finite h and proper Y; finite constant-module torsors lift over the henselian
   pair, and module injectivity suffices for underlying abelian acyclicity. Neither
   lemma restates the representation or all-degree projective-line vanishing.
   Empty schemes/modules, zero coefficients/classes, q=0 in the first lemma, and n=0
   in the biproduct argument cause no exception. Independent LeanFinder searches used
   different wording; source searches found no replacement. Existing colimit and
   acyclicity results use derived cohomology or `SheafOfModules`, so closing these
   split lemmas also needs the stated encoding bridges, not a quick application.
   Verdict: pass; neither split could be closed in a few minutes.
4. Read the injective extension and biproduct calculation, and the q=1/q>1 split.
   These use the existing embedding and general restriction bound. Read `sk-thm-p1`
   and its `realized` record: its strictly henselian comparison/acyclicity/exchange
   route remains. Completed the old-dependency accounting in `No longer needed`.
   Removed one unused public import from a new module and verified compilation.
   Verdict: pass; no entire branch is pruned.
5. Compared each existing node with its repository record: only proof, proof_deps,
   and proof_origin changed. Proof dependencies equal the union of step uses; the
   two new nodes have matching Lean signatures, source locators, complete proofs,
   searches, creation/blueprint records, chapter, unit, and status. Verdict: pass.

Changes in this reading: removed the new image module's unused TorsionSheaf import;
normalized a stray space before a proof delimiter; removed copied Lean comment closers
from the two new nodes' proof text; completed dependency accounting and this review record.
Source verification: [03SA](https://stacks.math.columbia.edu/tag/03SA),
[03Q5](https://stacks.math.columbia.edu/tag/03Q5),
[0A5H](https://stacks.math.columbia.edu/tag/0A5H),
[0A48](https://stacks.math.columbia.edu/tag/0A48),
[03FD](https://stacks.math.columbia.edu/tag/03FD).
