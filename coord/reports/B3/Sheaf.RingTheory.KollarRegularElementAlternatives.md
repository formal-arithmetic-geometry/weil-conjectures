## What changed
Proved `IsLocalRing.kollar_regular_element_alternatives` with its existing signature
byte-for-byte unchanged. Extract the associated-prime quotient representative directly
using Mathlib, then split on preservation of the maximal ideal by division of ay by x.
The unstable branch constructs t with yt = x, proves the maximal ideal is (t), and
uses the height bound and Mathlib regular quotient dimension drop to prove regularity
and dimension one.

Added the fully proved `IsLocalRing.kollar_finite_extension_of_stable_ideal` in
`Sheaf.RingTheory.KollarFiniteExtensionFromStableIdeal`. It constructs the subalgebra
of R localized at x preserving the image of the maximal ideal. Multiplication by x
injects that algebra into the finite image of the maximal ideal, proving finiteness
without an integrality argument. Its image of the maximal ideal is already an ideal,
so the cokernel condition holds with n = 1. The ring is explicitly constructed; no
object is selected using an unproved existence theorem.

The target imports the new helper and Mathlib KrullDimension.Regular only for its
proof, using plain imports. Replaced the public RegularSequence import by the smaller
IsSMulRegular import for the statement's regular-element and quotient-module notions.
Change record: `coord/changes/kollar-regular-element-alternatives-imports.md`.

## Proved and sorry left
Closed original hole: `IsLocalRing.kollar_regular_element_alternatives`.
Added fully proved declaration: `IsLocalRing.kollar_finite_extension_of_stable_ideal`
(node `new-kollar-finite-extension-stable-ideal`).
Holes added: none. Holes left in delivered modules: none. Thus 1 of 1 original holes
is closed, with a net reduction of one hole; this delivery is a proof, not a decomposition.
The first worker's two proposed holes and modules were removed rather than delivered.

Both declarations were checked with explicit `#print axioms` scratch copies; each
uses exactly `propext`, `Classical.choice`, and `Quot.sound`, without `sorryAx`.
Both delivered modules compile without warnings. The sole direct importer,
`Sheaf.RingTheory.KollarLocalDichotomy`, compiles unchanged against the delivery overlay.

## No longer needed
Removed import `Mathlib.RingTheory.Regular.RegularSequence`, replaced by the narrower
`Mathlib.RingTheory.Regular.IsSMulRegular`. Removed the proposed witness and core
modules and nodes from the sandbox delivery. They never existed in the repository.

Old target proof dependencies no longer used:
- `lem-weil-pbc-endomorphism-finite-module-monic`: finiteness follows by injection
  into the image of the maximal ideal; no determinantal trick.
- `def-weil-polynomial-ring`: no polynomial or integrality argument.
- `lem-weil-pbc-finite-of-integral-generators`: use Module.Finite.of_injective.
- `lem-weil-pbc-noetherian-minimal-prime-associated`: use the dimension drop for
  quotienting by the regular element x, rather than a minimal-prime argument.

`def-weil-ring-localization-away` remains needed by the new helper, rather than as a
direct dependency of the target. The Noetherian, regular-ring and dimension definitions
and the dimension bound remain used. No repository Sheaf module is pruned. The unit
`sk-thm-p1` realized statement and steps are untouched; this is a below-unit proof.

## Where the brief, the DAG or earlier work was wrong
The earlier delivery blocker is resolved: the resumed dry run compiled both modules
and passed preflight with review class CODEX. Nothing was pushed. This retry also
updated the target proof docstring to match the implemented stabilizer construction
and dimension-drop argument, and supplied the new module's required file header.

The first worker's proposed witness and core nodes had placeholder mathematical and
Lean statements, no recorded searches, and incomplete natural-language proofs. The
core retained essentially the original disjunction. That proposal closed one hole by
adding two and did not provide the substantive case reduction. The second reading
removed it, proved the representative extraction in the original target, and proved
both genuine subcases. The DAG's original determinantal-trick and minimal-prime routes
were unnecessary: finiteness by injection and regular quotient dimension drop give
shorter proofs.

The source was checked at https://stacks.math.columbia.edu/tag/0BHZ, fourth and fifth
proof paragraphs (label lemma-hart-serre-loc-thm). The stabilizer algebra is a different
explicit finite extension satisfying precisely the original existential conclusion.

## New nodes
`new-kollar-finite-extension-stable-ideal` states only the stable finite-extension
subcase, with its full hypotheses and conclusion, complete elementary construction
proof, and an exact Lean signature. It is fully proved. Searches by leanfinder, loogle,
grep and leansearch are recorded; leansearch was unavailable with an internal server
error, and the successful searches found no one-line specialization proving this
finite-extension statement. Repository searches found no duplicate. Standard finite
submodule and localization lemmas are used in its actual proof.

## Earlier second reading (a previous round; superseded)
1. Compared the target against the repository with diff and extracted its signature:
   the existing theorem statement is byte-for-byte identical. No definition or target
   statement changes. The narrower public import is documented in the change record;
   its sole direct importer publicly imports Depth, which publicly imports
   RegularSequence, and compiled
   unchanged against the new module. Verdict: pass after import review.
2. Compiled both delivered modules without warnings, scanned every delivered file for
   sorry and forbidden declarations, and printed axioms of both theorems in scratch
   copies. Only the three allowed axioms occur, with no sorryAx. The local subalgebra,
   its image module, linear embedding, lifted ring and ideal are real constructions.
   Verdict: pass; all holes closed.
3. Removed both original split-off statements. The one new statement covers only the
   stable subcase and is proved in full. Checked nontriviality through the injective
   localization map, non-surjectivity through y outside xR, and the associated-element
   exclusion at x and at 1. The cases x = 0, a field, or an Artinian ring cannot satisfy
   a regular x in the maximal ideal; the principal-maximal case is handled by the
   regular branch. No domain assumption is introduced in the stable construction,
   so rings with other zero divisors are covered. Searches found no duplicate result.
   Verdict: pass.
4. Read the proof from the target down. Extraction uses Mathlib directly, the regular
   subcase is fully proved in the target, and the extension subcase uses the fully
   proved helper. All four unused old dependencies are listed above; localization
   remains through the helper. Inspected dag/units/sk-thm-p1.json: the changed node is
   not a realized unit statement or step, and no unit route is bypassed. Verdict: pass.
5. Rewrote the existing node's proof, proof_deps and proof_origin to follow the Lean.
   The new node has self-contained mathematics, exact signature, source, proof steps,
   dependencies, searches, chapter, unit and creation record. Verdict: pass.

Second reading changed the proposed decomposition into a complete proof, removed its
placeholder nodes and modules, added a proved stable-extension helper, narrowed the
regular-element import, and repaired the DAG and report.

## Second reading by B3

1. Interface: independently compared the original module with the sandbox by diff,
   and asserted byte-for-byte equality of the existing theorem signature. No existing
   definition changed. The only public-import change has its change record. The sole
   direct importer, KollarLocalDichotomy, still publicly imports Depth and therefore
   RegularSequence; it compiled unchanged against the delivery overlay. Verdict: pass.
2. Proof: independently compiled both complete modules without errors or warnings.
   Explicit scratch-copy #print axioms checks for both declarations returned exactly
   propext, Classical.choice and Quot.sound, with no sorryAx. Scanned both files:
   no sorry or forbidden construct, and no line exceeds 100 characters. Read the
   construction of the localization subalgebra, linear injection, ULift transport,
   image ideal and annihilator exclusion: all data are explicit, with no arbitrary
   witness extracted from an unproved theorem. Verdict: pass.
3. New statements: there are no split-off holes. The fully proved helper covers only
   the stable-ideal subcase, and the original theorem proves representative extraction
   and the complementary regular-local subcase directly. Checked x = 0, x a unit,
   fields and Artinian local rings: their impossible hypotheses cannot generate an
   extension. Checked that no domain hypothesis is used, so other zero divisors are
   permitted. Independently searched Mathlib and both library roots with preservation
   and stabilizer terminology, and searched Loogle for Subalgebra, Module.Finite,
   Function.Injective (zero hits). No duplicate shorter alternatives result found.
   Read the cited stable and unstable branches of Stacks Tag 0BHZ online, since the
   local algebra.tex is absent; the explicitly identified stabilizer variant is valid.
   Verdict: pass.
4. Route and pruning: read downward from the original target. The proof uses direct
   Mathlib quotient/associated-prime lemmas, the proved helper for the stable branch,
   and dimension drop for the regular branch. The four unused old dependencies are
   all listed above. Localization is removed as a direct dependency but remains
   genuinely used through the helper. Imports match statement/proof visibility.
   Neither changed node realizes a statement or step in sk-thm-p1; the fixed unit
   route is preserved. No repository module is pruned. Verdict: pass.
5. DAG: the existing node changes only proof, proof_deps and proof_origin. Their steps
   match the Lean case split and declarations used. The new node has the prescribed
   source, complete mathematical argument, dependency union, searches, creation and
   blueprint records, and exact Lean statement. Verdict: pass.

This second reader changed only this report, adding the independent checks above.
No repair of the submitted Lean proofs or DAG was needed. Temporary axiom and
unchanged-importer scratch copies were removed before delivery. Confirmed count:
one of one original holes closed, zero holes added or left, zero split off.
