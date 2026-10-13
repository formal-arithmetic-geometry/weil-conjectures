## What changed

Proved `Algebra.principalLocalization_algEquiv` in
`lean/Sheaf/RingTheory/PrincipalLocalizationAlgEquiv.lean` by explicitly constructing the
quotient evaluation map and its inverse via Mathlib's localization universal property.
Checked both composites and the specified images of old and new variables. The theorem's
signature, visibility and existing docstring are unchanged.

Replaced the unused public import `Sheaf.Paper.RelativeGlobalCompleteIntersectionPresentation`
with `Mathlib.RingTheory.Ideal.Quotient.Operations` and `Mathlib.Data.Fin.Tuple.Basic`.
The public import change is recorded in
`coord/changes/principalLocalization_algEquiv-imports.md`. No adapted modules are delivered:
both direct importers already import the removed module independently; no adaptation is
needed. The originally checked importer compiled unchanged against the delivered module. Updated the existing node's proof and proof_origin
to describe the actual argument; proof_deps remains empty.

Validation: the item compiled without errors or warnings. Both unchanged direct importers,
`Sheaf.RingTheory.PrincipalLocalizationCI` and
`Sheaf.RingTheory.RelativeGlobalCompleteIntersectionPrincipalLocalization`, compiled against
the sandbox's compiled item without errors or warnings. The construction uses no nontriviality, nonzero-element, or
positive-variable-count assumptions: the quotient and localization universal properties also
cover zero rings, h = 0, n = 0 and c = 0. No additional edge-case hypotheses were introduced.

## Proved and sorry left

Closed the one hole in `Algebra.principalLocalization_algEquiv`
(node `new-principal-localization-alg-equiv`). All parts, including the equivalence and both
variable formulas, are proved from Mathlib. No holes remain in the item and no holes were added.
This is a proof, not a decomposition: zero statements split off.

## No longer needed

Removed import: `Sheaf.Paper.RelativeGlobalCompleteIntersectionPresentation`.
Its complete-intersection condition (node `def-weil-pbc-relative-global-complete-intersection`)
is not needed for this algebra equivalence. The underlying
`Sheaf.Paper.RelativeGlobalCompleteIntersection` is also unnecessary for this proof; it is
still needed elsewhere in the library. No proof-dependency nodes were present to prune, no
unit statement or step was bypassed, and no other imported module is unused.

The searched `IsLocalization.Away.mvPolynomialQuotientEquiv` concerns one polynomial variable
over the already-quotiented coefficient ring. Directly using the two universal properties
avoids importing `Mathlib.RingTheory.MvPolynomial.Localization` or introducing auxiliary
presentation-transport statements.

## Where the brief, the DAG or earlier work was wrong

The original node contained only a placeholder saying the construction was split off for a
later worker, rather than numbered usable proof dependencies. Its docstring supplied the
correct universal-property argument, now implemented completely. The original public
complete-intersection import was unnecessary for this general algebraic statement. No
statement or definition was false, and no interface adaptation was forced.


## Second reading by M2

1. **Visible declarations — pass.** Compared the delivered Lean module and existing node
   with the repository versions using `diff`. The existing theorem signature, visibility,
   universes, hypotheses, conclusion and docstring are byte-for-byte identical. There are no
   definitions or new declarations. The public import replacement has its change record;
   both direct importers keep the complete-intersection public import independently and
   compile unchanged against the delivered module.
2. **Proof and axioms — pass.** Compiled the item locally with `lcompile.py`, without errors
   or warnings. Read every local construction, both kernel arguments, the inverse relation,
   unit cancellation, both composite identities and both variable formulas. A scratch copy
   with `#print axioms Algebra.principalLocalization_algEquiv` reports exactly `propext`,
   `Classical.choice`, `Quot.sound`. No sorry, axiom, unsafe, opaque, implemented_by, extern,
   kernel-check bypass or hollow definition occurs. The maps are constructed explicitly;
   no arbitrary witness is extracted from an unproved existence theorem.
3. **Split-off statements — pass, none.** No lower holes or new statements were introduced.
   Checked the degenerate cases: Fin.lastCases still handles the sole variable/relation
   when n or c is zero; localizing at zero and imposing the inverse relation both give the
   zero ring; all arguments remain valid for an initially zero ring. No nontriviality,
   regularity or nonzero hypothesis is hidden. Independently searched Lean Finder, Loogle
   and Mathlib/source grep with different queries: no directly matching equivalence with
   this finite-variable quotient and both generator formulas was found.
4. **Route, imports and pruning — pass.** Mathlib's mvPolynomialQuotientEquiv uses a Unit
   variable over the already quotiented coefficient ring; using it here would still require
   extra quotient and variable transport. The existing direct universal-property proof is
   sound and needs no rewrite. Each remaining public import supplies statement data:
   quotient algebra structures, Fin.snoc, localization/invSelf and polynomial rename.
   There are no proof-only public imports. The old proof_deps was empty, and No longer needed
   names the removed Sheaf import and its underlying definition module. Read
   dag/units/sk-thm-p1.json and its realized statement/steps: this algebraic helper is below
   the unit route, and no unit statement, step or realized node is bypassed.
5. **Nodes — pass.** Only proof and proof_origin change in the existing node; proof_deps
   stays empty because the argument uses Mathlib and no project proof dependency.
   The three recorded proof steps describe exactly the evaluation/quotient construction,
   inverse localization construction and composite/generator checks in Lean. No new nodes
   or changed statements require further records.

**Changes made in this reading:** corrected the report and public-import change record to
account for the second direct importer, Sheaf.RingTheory.PrincipalLocalizationCI, and added
its user-table row. Compiled both unchanged importers against the sandbox item. No Lean
proof, signature, import or node change was necessary. Closed one existing hole, added zero
holes, and split off zero statements.
