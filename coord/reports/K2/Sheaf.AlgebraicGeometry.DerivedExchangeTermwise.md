## What changed

`AlgebraicGeometry.derivedExchangeTermwise` retains its original signature. Its termwise
component clause is proved by reflexivity. A proved private helper lifts a derived map
uniquely into a K-injective homotopy object; this proves the existence and uniqueness
of the two comparison classes. A second proved private helper lifts the inverse of a
localized isomorphism and checks both inverse identities using injectivity. It proves
both comparison classes invertible. The unit on the chosen bounded below complexes
of injective objects, the equivalence counits, termwise pushforward, localization and
exact inverse image then prove all three remaining isomorphism claims.

The remaining exchange equation is reduced to the original plan's two separate cases:
`derivedExchangeBoundedComparison` is the equation with an additional strict lower
bound on I, and `derivedExchangeUnboundedTransport` extends a universally supplied
bounded formula to the arbitrary I. The original theorem supplies the first theorem
as the hypothesis of the second, then combines the resulting equation with the
independently proved component, uniqueness and isomorphism clauses. The new statements
are in two separate modules, with nodes and complete proof docstrings. No statement,
definition, universe or binder of an existing declaration changed.

Compilation used only lcompile.py, repeatedly. The three final modules compile together
in import order. Searches found the K-injective Hom bijection and the existing bounded
base-change factorization, but no theorem doing the entire comparison. LeanSearch
returned HTTP Internal Server Error; this is recorded as unavailable, not as no match.
The bounded statement was checked for the zero derived object, identity squares,
and a K-injective target J that is unbounded as a complex. It only requires boundedness
of I. The transport hypothesis fixes K and J, but ranges over all bounded below source
representatives, isomorphisms and resolution maps to this J, exactly what the canonical
bounded below representative and a transported resolution provide.

A further scratch attempt at proving transport constructed the homotopy inverse,
the bounded representative, and the transported quasi-isomorphism, but did not finish
all the naturality glue within the compiler's file-check limit. Its draft is retained
only in the sandbox as transport-draft.txt, not delivered as incomplete Lean code.

## Proved and sorry left

Proved, from the two intermediate statements:
`AlgebraicGeometry.derivedExchangeTermwise`
(node `lem-weil-pbc-derived-exchange-termwise`). There is no sorry in the item's module.
The private helpers `comparison_existsUnique` and `comparison_isIso` are proved directly.

Remaining sorries added by this delivery:

- `AlgebraicGeometry.derivedExchangeBoundedComparison`
  (`lem-weil-pbc-derived-exchange-bounded-comparison`): the equation for a strictly
  bounded below K-injective source, original proof step 6 with supporting steps 2–5.
- `AlgebraicGeometry.derivedExchangeUnboundedTransport`
  (`lem-weil-pbc-derived-exchange-unbounded-transport`): transport from the supplied
  bounded formula to arbitrary K-injective source representatives, original step 7.

Both remaining proofs are exactly `:= by sorry`, in their own public theorem modules.
The original theorem is not proved by a renamed copy: its component, unique-lifting,
and five invertibility assertions have independent complete proofs, and its equation
combines a bounded computation with a separate transport implication.

## No longer needed

Removed all seven original proof-only imports from the item's module:

- WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusAdjunction
- WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
- WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
- WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
- WeilConjectures.SixFunctors.BaseChange.Square
- WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.MorphismDefs
- WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs

The public import WeilConjectures.SixFunctors.BaseChange.Derived supplies the statement
and the existing tools used directly. The new modules likewise require only that public
import. The item adds two proof-only imports for the new intermediate theorems.

The item's direct proof no longer uses the derived counit/unit formulas, derived-square
comparison or direct-image triangulated structure. Consequently its direct proof_deps
omit prop-weil-pbc-derived-inverse-image-adjunction, def-weil-pbc-derived-square-iso,
lem-weil-pbc-derived-direct-image-triangulated, lem-weil-pbc-termwise-adjunction-homotopy,
def-weil-abstract-derived-category, def-weil-pbc-inverse-image,
def-weil-pbc-cartesian-square, def-weil-pbc-derived-exchange, and
lemma-weil-pbc-underived-exchange-naturality. These are not claimed to be globally
unnecessary: the bounded computation and transport nodes retain the appropriate
supporting dependencies, and statement dependencies remain untouched. No unit-level
statement or step is bypassed; sk-def-exchange has no proof steps, and its realized
exchange definition and replacement formula remain on the route.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement was found false. The K-injective Hom node is a Mathlib match,
not a separate Sheaf module. Qh inverting the localization of j needs an explicit
Localization.inverts application; it is not synthesized automatically in this context.
Two generic lifting helpers suffice for all the structural clauses; the much longer
seven-step comparison argument is only needed for the final exchange equation.

## New nodes

`lem-weil-pbc-derived-exchange-bounded-comparison` is the bounded-source equation,
with module Sheaf.AlgebraicGeometry.DerivedExchangeBoundedComparison and the explicit
additional hypothesis `[I.IsStrictlyGE n]`. It isolates step 6, uses the stated derived
adjunction and square-comparison tools, and carries a complete proof in words.

`lem-weil-pbc-derived-exchange-unbounded-transport` is step 7 as a conditional transport
statement: a formula for all bounded representatives of the fixed K, with resolution
maps to the fixed J, implies the formula for the arbitrary I. Its module is
Sheaf.AlgebraicGeometry.DerivedExchangeUnboundedTransport. The proof in words gives the
canonical bounded representative, homotopy inverse, transported quasi-isomorphism,
and the source, target and termwise naturality equalities. Both nodes stay in
sec-proper-base-change/sk-def-exchange. No change record is needed.

## Second reading by K2

1. Compared the delivered `DerivedExchangeTermwise` module with the repository version. The
   theorem signature is unchanged byte for byte; only proof imports and proof text changed.
   Verdict: pass.
2. Compiled all three delivered modules with `lcompile.py --all`. There are no errors, no
   forbidden declarations, and no `sorry` in the item's theorem; the two explicitly split
   lemmas contain only their named `sorry`s. The proof helpers are private and proved.
   Verdict: pass.
3. Checked the two split statements against their docstrings, edge cases (zero complexes,
   identity squares, and unbounded targets), and searched the library for duplicates. They
   are true conditional reductions and exactly match their nodes; no existing declaration
   duplicates them. Verdict: pass.
4. Checked the route and pruning. The termwise component, comparison uniqueness, and
   invertibility clauses are proved independently; the final equation uses the bounded and
   transport nodes. Removed proof-only imports are listed above, and no unit step is
   bypassed. Verdict: pass.
5. Checked all node `lean` statements against the declarations and their proof/proof_deps
   against the written route. The new nodes have source, blueprint, proof origin and
   complete docstring proofs. Verdict: pass.

No code or node repair was needed in this second reading; this report section is the only
change.
