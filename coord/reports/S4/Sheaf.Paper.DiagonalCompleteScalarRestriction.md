## What changed

Implemented `AlgebraicGeometry.ProEtale.DiagonalTrace.diagonalCompleteScalarRestriction`
with its original signature and public imports unchanged. The proof transports the
orthogonality predicate through an additive equivalence, uses local completeness
reflection under restriction and the existing constant-completion equivalence, and
lifts the given full subcategory into the complete completed-coefficient category.
Full faithfulness follows from the full inclusions, the equivalence, and the natural
isomorphism with the actual scalar functor. All the categorical assembly is proved.

Added `Sheaf.Paper.DiagonalCompletionCoefficientTransport`. Its theorem
`AlgebraicGeometry.ProEtale.DiagonalTrace.diagonalCompletionCoefficientTransport`
compares the actual scalar functor with the small-site constant-completion functor.
The proof constructs the quotient ring isomorphisms using `PadicInt.ker_toZModPow`,
checks their transition equations, compares the limits and every projection, and
identifies the coefficient map. The small-site comparison is constructed directly
from sheafification compatibility and preservation of limits, avoiding the wider
stratified-perfect completion theory. It constructs the two ringed-site module
equivalences and the scalar-restriction square, then derives this square through
the arbitrary localization instances in `DiagonalTraceLocalizations`. This theorem
contains no completeness assertion and no new hole.

Added `Sheaf.Paper.ConstantPrincipalCompleteOrthogonality` for the missing comparison
from orthogonality to local ringed completeness. Only this direction is needed. The main proof uses this
comparison and the proved coefficient transport through private proof imports.
No existing module besides the assigned item, existing definition, target signature,
public import, or unit realization was changed. No change record is needed.

Validation: `lcompile.py --all` compiled all three modules after profiling was
removed. The only warnings were overlong lines in the main helper; those lines
were then wrapped. Static checks confirm the original theorem signature and
public imports are unchanged, the node signatures and proof dependencies agree
with the code, and all Lean lines are at most 100 characters. The delivery tool
checks the final formatted packet again.

## Proved and sorry left

Closed the original single hole:
`AlgebraicGeometry.ProEtale.DiagonalTrace.diagonalCompleteScalarRestriction`
(node `lem-sfb-diagonal-complete-scalar-restriction`). Its proof is complete Lean
from the declared dependencies and the one new intermediate criterion.

Also proved, without introducing a hole:
`AlgebraicGeometry.ProEtale.DiagonalTrace.diagonalCompletionCoefficientTransport`
(node `lem-sfb-diagonal-completion-coefficient-transport`). Its private helper
constructions and equations are proved.

One added hole remains:
`CategoryTheory.ConstantCompletion.constantPrincipalComplete_of_orthogonal`
(node `lem-sfb-constant-principal-complete-orthogonality`), whose proof is exactly
`by sorry`. Its docstring and node give the slice-localization and extension-by-zero
argument, including the passage from the principal generator to all ideal sections.
This is a generic sufficient completeness criterion over a constant ring; it asserts neither
full faithfulness nor anything about a completed coefficient category. It is a
strict part of the original argument, not a renamed scalar-restriction theorem.

Counts: original item 1 hole closed, 0 remaining there; 1 lower hole added.
This is a decomposition, with net hole reduction 0, not an axiom-free proof of the
whole result. No data definition contains `sorry` or chooses an arbitrary witness
from an unproved existence assertion. The new criterion was checked on the empty
site, zero objects, unit generators and the zero ring. The coefficient comparison
uses no geometric finiteness or invertibility assumption on the scheme.

## No longer needed

No original public import was removed, and no module is withdrawn or globally
pruned. The main proof does not directly use
`lem-sfb-source-principal-completion-orthogonal`, attached to
`WeilConjectures.CategoryTheory.DerivedCategory.Complete.Principal` and
`DerivedCategory.derivedComplete_iff_rightOrthogonal`. That statement concerns the
Milnor-completion predicate for module-valued sheaves; the missing comparison with
slice-local ringed completeness is now isolated precisely in the new criterion.
It may still help prove that criterion and remains in the library unchanged.
The proof also avoids `Sheaf.Paper.SfbCompletionRingComparison` and its
stratified-perfect dependencies: the new private comparison is built directly from
the site equivalence and limit preservation. Those existing declarations remain
unchanged. The other original dependencies, constant completion and flat-ringed
completeness reflection, are used. The blueprint unit route remains unchanged.

## Where the brief, the DAG or earlier work was wrong

The planned application of the source principal-completion theorem is not a direct
application: its predicate, coefficient category and derived-category instances
differ from `ConstantCompletion.IsComplete`. The DAG did not state this bridge.
The coefficient transport also needed actual projection and scalar-map equations;
an abstract equivalence of categories would not identify the functor in the goal.
Those equations and the derived scalar square are now proved, rather than left as
another equivalent full-faithfulness obligation. No statement is disputed.

The server's compiled library still placed the diagonal interface declarations in
`DiagonalTowerLimit`, while the current source had extracted them into
`DiagonalTowerLimitInterface`. An unnecessary private import of the extracted
module caused a duplicate-declaration error. The final packet avoids that import
and proves the ordinary restriction exactness helper from the existing public
forgetful-colimit theorem. The main file also proves its kernel-extension helper
from public ideal-section formulas; it needs no `import all` access to private
completion declarations. No launcher tool or shared file was changed.

## New nodes

`lem-sfb-diagonal-completion-coefficient-transport` records the proved site,
quotient-tower, completed-ring and derived-functor comparison. Its proof dependencies
include the constant-module equivalence, exact forgetful functor, and exact-derived composition and natural-isomorphism lemmas.

`lem-sfb-constant-principal-complete-orthogonality` records the sole remaining lower
obligation, with its source and complete natural-language proof. It separates the
local/global completeness comparison from the completed coefficient encoding and
from the full-faithfulness assembly. No change records were added.

## Second reading by S4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
