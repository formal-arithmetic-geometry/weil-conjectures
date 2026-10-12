## What changed

Replaced the sole remaining sorry in
`AlgebraicGeometry.Scheme.IsFiniteLocallyConstantSheaf.ihom_unit` by a compiling proof.
The theorem's signature, universes, coefficient-ring hypotheses and original docstring are
unchanged. Added two proof-only imports, `Sheaf.ConstructibleSheaf.DualLocallyConstant` and
`Sheaf.ConstructibleSheaf.DualStalk`. Each new module has one public intermediate theorem.

The proof supplies local constancy from the first intermediate theorem. At each geometric
point it converts finite generation of the original stalk to `Module.Finite`, uses Mathlib's
`isNoetherian_linearMap` and `IsNoetherian.finite` for the module dual, and transports finite
generation along the stalk comparison from the second intermediate theorem. It then fills
both fields of the finite-locally-constant class. This is a reduction to two strictly partial
results, with the module finiteness argument completed in Lean; neither intermediate states
finite local constancy of the dual.

Added a DAG attachment for the previously unattached original theorem and two nodes for the
new intermediate statements. The proof follows the original module docstring's finite
presentation argument. No definition, existing statement or target changed. No change record
is needed. The `sk-thm-p1` unit's existing realizations are untouched.

## Proved and sorry left

Decomposed (not proved without sorry):
`AlgebraicGeometry.Scheme.IsFiniteLocallyConstantSheaf.ihom_unit`
(node `lem-weil-pbc-flc-dual`). There are no direct sorries left in the item's module.
One original declaration hole was closed and two strictly partial declaration holes were added;
this is a decomposition, with zero of the one original holes proved without sorry.
This theorem still depends on the following two new sorries:

- `AlgebraicGeometry.Scheme.IsFiniteLocallyConstantSheaf.ihom_unit_locallyConstant`
  in `Sheaf.ConstructibleSheaf.DualLocallyConstant`,
  node `lem-weil-pbc-flc-dual-locally-constant`.
- `AlgebraicGeometry.Scheme.IsFiniteLocallyConstantSheaf.nonempty_ihom_unit_stalk_iso`
  in `Sheaf.ConstructibleSheaf.DualStalk`, node `lem-weil-pbc-flc-dual-stalk`.

Each is exactly `:= by sorry`, with its source and complete natural-language proof in its
own docstring and matching node. All three delivered modules compile together without
warnings through `lcompile.py`. Existing indirect sorries in `MonoidalParts` are unchanged:
`IsLocallyConstantSheaf.tensorObj_part` and `IsFiniteSheaf.tensorObj_part` are still used by
the already-proved tensor theorem.

Edge cases checked mathematically: the empty scheme makes the stalk assertion vacuous;
empty members can be discarded from a trivializing cover; F = 0 and the zero ring cause no
exception; a finite nonprojective module is allowed. In particular, for a constant torsion
module over the integers its ordinary coefficient dual can be zero. The comparison concerns
ordinary internal Hom, not derived Hom, and requires finite presentation rather than
projectivity. No noetherianity, quasi-compactness or connectedness hypothesis on X is added.

## No longer needed

Removed the trial proof import `Mathlib.RingTheory.Noetherian.Basic`: the needed instances
are already available through the original imports, and the module compiles without it.
No original import is removed. Both new sheaf imports are used. The existing
`Sheaf.ConstructibleSheaf.MonoidalParts` import remains necessary for the tensor theorem.
No existing DAG node or module is pruned by this route.

No new work is required for finite generation of a module dual: Mathlib already supplies it.
The ringed-space module theorems in `Sheaf.AlgebraicGeometry.StalkInternalHomFinitePresentation`
and `Sheaf.Algebra.Category.ModuleCat.Sheaf.HomFinitePresentationKernel` are not imported:
their signatures concern sheaves on topological opens rather than ModuleCat-valued sheaves
on the small étale site. `Sheaf.AlgebraicGeometry.ConstructibleModuleFinitePresentation` is
also unnecessary: it assumes finite coefficients and qcqs X, and imports the item itself.
These are search alternatives, not formerly attached dependencies being removed.

## Where the brief, the DAG or earlier work was wrong

No DAG node has a `lean.module` record for the item's module in the starting checkout, and
there is no blueprint tag on `ihom_unit`. Thus there is no numbered node proof to translate.
The complete route was taken from its existing docstring and recorded in the new attachment.
The new nodes identify this missing upstream attachment honestly: their blueprint ancestor
is null rather than an invented blueprint provenance. Their chapter/unit follow the existing
MonoidalParts nodes. The unit's own statement and proof steps are not bypassed.

LeanSearch returned HTTP 500 on both attempted queries. The searches are recorded as
unavailable, not as evidence of absence. LeanFinder, Loogle, repository search and Mathlib
source search were performed. Loogle found `isNoetherian_linearMap`, whose signature was read
in Mathlib.RingTheory.Noetherian.Basic. No exact library result for the two small-étale-site
sheaf steps was found. The existing field-coefficient derived-dual theorem does not handle
arbitrary commutative noetherian rings.

## New nodes

`lem-weil-pbc-flc-dual`: attaches the original theorem to
`lean/WeilConjectures/ConstructibleSheaf/Monoidal.lean`; its proof dependencies are exactly
the two new sheaf steps. The finite-generation glue is complete Lean using existing Mathlib
instances.

`lem-weil-pbc-flc-dual-locally-constant`: local constancy alone, in
`lean/Sheaf/ConstructibleSheaf/DualLocallyConstant.lean`. Its natural-language proof uses
finite presentations on a trivializing cover to express the dual as a constant kernel.

`lem-weil-pbc-flc-dual-stalk`: the geometric stalk comparison alone, in
`lean/Sheaf/ConstructibleSheaf/DualStalk.lean`. Its natural-language proof uses the same
local finite presentation and exactness of geometric stalks to identify two kernels.
It makes no assertion about finite generation of the resulting dual.


## Second reading by H1

1. **Existing interface unchanged — PASS.** Read the complete three delivered modules and
   compared Monoidal with the repository version before the dry run. The only diff is two
   plain proof imports and the body of `IsFiniteLocallyConstantSheaf.ihom_unit`; its signature,
   original docstring, universes and hypotheses are byte-for-byte unchanged. No existing
   definition, target, attribute or other declaration changes. No change record is required.
2. **Kernel-checked reduction — PASS, with two declared holes.** Independently compiled all
   three modules in import order with lcompile.py: no errors or warnings. Searched the delivered
   Lean for forbidden declarations and hollow definitions: none. Scratch copies with explicit
   `#print axioms` for ihom_unit, the two helpers, and the existing tensorObj show only propext,
   Classical.choice, Quot.sound and sorryAx. The two helper bodies are exactly `by sorry`;
   the main module has no direct sorry. The delivery wrapper also probes every declaration.
3. **Split statements — PASS.** Matched both node statements to the full elaboration context:
   arbitrary scheme X, commutative noetherian coefficient ring, finite locally constant F;
   the stalk lemma quantifies over every separably closed geometric point. The helpers assert
   respectively local constancy and a stalk identification, not finite local constancy under
   a renamed theorem. The completed module-dual finiteness argument genuinely combines them.
   Checked empty X, zero coefficients, zero F and a nonprojective constant torsion module over
   the integers (whose coefficient dual is zero). Finite presentation suffices: locally a finite
   presentation presents the dual as a kernel between finite free constant sheaves; exact
   constant sheafification preserves that kernel and exact geometric stalks identify its
   stalk with the module dual. These are complete sourced docstring proofs of true partial
   results, with matching nodes. New LeanFinder query used “internal Hom from a locally
   constant finitely presented module commutes with geometric stalk functor”; its eight hits
   concern condensed modules, not this site. Loogle query `"ihom", "Sheaf"` found no result;
   grep queried sheafFiber/hom in both orders and IsConstant/ihom in both orders. Repository
   searches and reading StalkInternalHomFinitePresentation and HomFinitePresentationKernel
   confirm their different ringed-space/SheafOfModules signatures. No immediately applicable
   theorem or short proof closing either helper was found.
4. **Route and pruning — PASS.** The main proof uses both new lemmas and Mathlib's existing
   finite-generation instances, without copying an algebra lemma. Each new public import is
   needed for its statement: constructibility predicates, ModuleCat closed structure, and
   sheaf closed structure. Both new imports of Monoidal are plain imports. No original
   dependency is removed: the previously landed tensor proof still uses both MonoidalParts
   declarations. There was no original DAG attachment or old proof_deps for ihom_unit to prune.
   Read sk-thm-p1's statement, steps and realized record; none is replaced or bypassed.
5. **DAG agreement — PASS.** Read all three new nodes. The attachment's three proof steps
   match the Lean's local-constancy field, stalk-dual finite-generation transport and class
   assembly; proof_deps equals the union of uses and names exactly the two helpers. Each
   helper has its own module/declaration, source, complete argument, searches, created record,
   chapter/unit and honest null blueprint ancestor for this unattached upstream theorem.
   No existing node or unit record is changed.

Second reading changed the accounting above to explicitly call the result a decomposition
(one hole closed, two added, zero original holes proved without sorry), and added this review.
No Lean repair was needed; the valid reduction and both intermediate statements are retained.
