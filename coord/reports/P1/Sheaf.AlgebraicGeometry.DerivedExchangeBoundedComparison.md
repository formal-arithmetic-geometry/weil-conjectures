## What changed

Proved `AlgebraicGeometry.derivedExchangeBoundedComparison` in
`Sheaf.AlgebraicGeometry.DerivedExchangeBoundedComparison`, with its signature unchanged.
The proof uses `Etale.derivedBaseChangeMapPlus_fac_app`, already proved in the source library,
and naturality of the two right-derived units. It lifts `s` to D⁺ and treats `q(j) ≫ h₂` as
a map between bounded below homotopy objects; no lower bound on J is introduced.
The existing node's proof, proof_deps and proof_origin now describe this route.
The unit sk-def-exchange has no proof steps; its realized exchange definition and replacement
node are kept, including the proved component formula from the replacement node.

The only retained import is the existing public import
`WeilConjectures.SixFunctors.BaseChange.Derived`. No public interface, definition or statement
was changed. Local compilation passed without warnings (54.9 seconds). Search used Lean Finder,
Loogle, the search wrapper's grep and repository rg; the source's component formula was the
usable shorter route. Loogle did not recognize the queried identifier `NatTrans.naturality`;
the existing naturality API is nevertheless available directly in Lean.

## Proved and sorry left

Closed the sole hole: `AlgebraicGeometry.derivedExchangeBoundedComparison`
(node `lem-weil-pbc-derived-exchange-bounded-comparison`). Holes added: none.
Sorries left in the delivered module: none. No new modules or intermediate holes were added.
This is a proof, not a decomposition. It uses the already proved component formula; it does
not rely on any newly imported statement with sorry.

## No longer needed

Removed all six proof-only imports:

- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusAdjunction`
- `WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction`
- `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`
- `WeilConjectures.SixFunctors.BaseChange.Square`
- `WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.MorphismDefs`
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`

Removed proof dependencies:

- `prop-weil-pbc-derived-inverse-image-adjunction`
- `lem-weil-pbc-termwise-adjunction-homotopy`
- `lem-weil-pbc-kinjective-hom-derived`
- `def-weil-pbc-derived-square-iso`
- `def-weil-pbc-inverse-image`
- `def-weil-pbc-cartesian-square`

The direct-image, derived inverse-image and derived-category definitions are still used.
The underived and derived exchange definitions are still used. Their defining modules are
available through the retained public import, so the removed explicit imports do not imply
that every such module leaves the global targets' closure. K-injective Hom lifting, derived
counit calculations, the derived adjunction unit calculation, and the derived square
comparison are unnecessary for this proof. Statement dependencies remain unchanged.

## Where the brief, the DAG or earlier work was wrong

The planned adjunction/resolution comparison is longer than necessary for the actual Lean
exchange definition: `derivedBaseChangeMapPlus_fac_app` directly supplies its value on H.
The compatibility assumptions already provide the maps needed for unit naturality, so no
K-injective comparison lift or extra resolution is needed. All hypotheses remain unchanged.
The textual proof of `lemma-weil-pbc-derived-exchange-replacement` mentions the termwise node,
but its recorded source declaration `derivedBaseChangeMapPlus_fac_app` is independently
proved via the universal property of the right derived functor. This proof uses that closed
Lean declaration, not the textual back-reference, so there is no circular Lean import.

## Second reading by P1

1. Interface: PASS. Compared the only delivered Lean module with the repository version.
   The existing declaration signature is byte-for-byte unchanged after removing one extra
   space before `:=`; its docstring and all hypotheses and conclusions are unchanged.
   The only other Lean changes are the proof, a declaration-local elaboration option, and
   removal of six private proof imports. No definitions, public imports or target statements
   change; no change record is needed.
2. Proof: PASS. Local compilation succeeded without warnings (59.5 seconds). A scratch copy
   compiled in 55.9 seconds with `#print axioms` for both
   `AlgebraicGeometry.derivedExchangeBoundedComparison` and
   `AlgebraicGeometry.Etale.derivedBaseChangeMapPlus_fac_app`: each lists exactly `propext`,
   `Classical.choice`, `Quot.sound`, with no `sorryAx`. The delivered module has no `sorry`,
   axiom, unsafe/opaque declaration, external implementation, or data chosen from an
   unproved existence statement. Read the cancellations, both unit naturality equations,
   the component formula, and the final passage through the faithful inclusion.
3. Split statements: PASS, none added or left. In particular J is never asserted bounded
   below: the morphism q(j) followed by h.2 is between bounded homotopy objects even when
   its intermediate representative J is unbounded. The construction also works for zero
   complexes and identity squares, and needs no additional resolution or witness.
4. Route and pruning: PASS. Read the upstream proof of the component formula, searched
   the repository's exchange declarations and Mathlib's right-derived factorization and
   naturality API (including an independent msearch grep query). The existing component
   formula is the direct available route; no duplicated helper or restatement is added.
   The retained public import is required by the signature. All six old proof dependencies
   absent from the new proof, and all six removed private imports, are listed under
   No longer needed. This is explicit import pruning, not a claim that those modules leave
   the global target closure. Read dag/units/sk-def-exchange.json: it has no proof steps,
   and both realized statement nodes remain used. The replacement node's closed Lean
   component theorem is used independently of its old textual termwise back-reference.
5. Nodes: PASS. The sole delivered existing node changes only proof, proof_deps and
   proof_origin. Its proof steps describe the Lean argument; proof_deps is exactly the
   union of their uses, and its stored Lean statement matches the unchanged signature.
   No new node or statement change is present.

Second-reading changes: removed the extra space before the proof delimiter to restore
literal signature equality, and appended this review. The proof itself needed no repair.
Holes closed: AlgebraicGeometry.derivedExchangeBoundedComparison (one of one).
Holes added or split off: none.
