## What changed

Proved `AlgebraicGeometry.Scheme.local_perfect_of_openRestriction_iso` in
`Sheaf.AlgebraicGeometry.OpenPerfectModelTransport`, preserving its signature,
visibility, docstring and original import of `Sheaf.AlgebraicGeometry.PerfectComplex`.
No other module changed.

The proof implements the existing four-step plan of
`lem-sc-open-perfect-model-transport`. Apply perfectness at the point of the open
subscheme, take the image open, and use `U.ι.isoImage V`. Build the restriction
equivalence along this isomorphism explicitly from `restrictFunctorComp`,
`restrictFunctorCongr`, and `restrictFunctorId`; compose it with the two
`Modules.overEquiv` equivalences. Its unit comparison and preservation of
coproducts identify finite free modules. Termwise transport preserves zero terms
and the given retraction equations, hence strict perfectness. Finally build the
underived restriction comparison and derive it, composing the supplied
isomorphism and the local representing isomorphism with
`mapDerivedCategoryFactors`.

All constructions use proved Mathlib APIs. The separate `Scheme.Modules`
category instance requires explicitly annotating the global restriction functor
with the shared `SheafOfModules` categories, as required by the existing derived
category binders. No additional derived-category instance is chosen.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.Scheme.local_perfect_of_openRestriction_iso`
(node `lem-sc-open-perfect-model-transport`).

One hole closed; zero holes added or split off. No `sorry` remains in the item,
and no new module or declaration is introduced. Single-file compilation succeeds
without warnings. The delivery dry run checks the declaration's axioms.

## No longer needed

None. The original public import is needed for the statement and definitions.
No proof dependency, node or module is pruned: the proof realizes the existing
DAG plan directly, using Mathlib for its comparison and equivalence steps.

## Where the brief, the DAG or earlier work was wrong

No mathematical discrepancy found. The unit's `realized` lists are empty for
this item; no unit statement or step is bypassed. The proof uses the given point
only to choose the local model, so empty opens are vacuous; zero complexes and
the total open satisfy the same transport calculation. Boundedness uses the
original degree bounds and each retraction retains the original finite rank.
The proof makes no assertion outside the given open.

Searches actually run through `msearch.py`: LeanFinder for transport of strictly
perfect models along an open immersion (eight open-immersion results, no exact
match); Loogle for `Modules.overMapCompOverEquiv` (one comparison theorem);
grep for unit comparisons and `overFunctorEquiv` (eight relevant ingredients).
Direct searches of both library roots found related transport modules, but none
was needed: the original plan can be proved directly from Mathlib.

## Second reading by Y3

1. Compared the complete delivered module with the repository using `diff -u`.
   The only difference replaces the original theorem's `by sorry` with its proof.
   Every existing signature, definition, visibility, docstring and import is byte
   for byte unchanged. No change record or forced adaptation is needed. PASS.
2. Independently compiled the module with `lcompile.py`: no errors or warnings.
   Scanned the delivered Lean for holes and forbidden constructs: none occur.
   Compiled a scratch copy with `#print axioms
   AlgebraicGeometry.Scheme.local_perfect_of_openRestriction_iso`; its only axioms
   are `propext`, `Classical.choice`, and `Quot.sound`. Checked the equivalence
   orientation, the finite-free comparison and retraction equation, and the final
   derived restriction comparison. The model is constructed from the given local
   model, with no data selected from an unproved existence theorem. PASS.
3. No new declarations, nodes or split-off statements exist. The one original
   hole is closed and zero holes are added. Independently searched Mathlib with
   Loogle for `Modules.restrictFunctor` and inspected restriction/unit comparisons;
   searched both Lean roots for perfect/open/isomorphism transport. The related
   `scheme_iso_local_perfect_transport` requires extra global equivalence data,
   and `perfect_of_open_pullbacks` is still open with different hypotheses; neither
   gives a shorter direct proof here. PASS.
4. Read from the conclusion back through the derived comparison and transported
   strict model to the local witness supplied by `hF`. The proof uses the shortest
   direct Mathlib constructions identified in the search. The sole public import
   is required by the statement. Both old proof dependencies remain used, so
   `## No longer needed` is complete. Checked the item's actual unit,
   `sk-thm-picard-duality`: its realized statement and step lists are empty, and
   no recorded unit realization is bypassed. Empty U is vacuous; zero terms,
   rank zero, and the total open require no exceptional argument. PASS.
5. Read `lem-sc-open-perfect-model-transport` in full. Its four proof steps,
   `proof_deps` (`def-pc-perfect-complex`, `def-pc-derived-category`) and
   `proof_origin` already describe the delivered Lean argument accurately.
   No node update is necessary, and no new-node fields need checking. PASS.

Changes made in second reading: appended this review and recorded the independent
search and axiom verification. No Lean or DAG repair was necessary.
