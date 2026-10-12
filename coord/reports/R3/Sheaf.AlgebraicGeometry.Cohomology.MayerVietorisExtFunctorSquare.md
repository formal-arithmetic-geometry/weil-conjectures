## What changed

Proved `CategoryTheory.Abelian.Ext.mapExactFunctor_square` with its public signature and
visibility unchanged, including all four independent Ext universes. The proved private
`compositionComparison` generalizes the existing composition argument to independently
chosen Ext universes; two applications prove the square.

Repair of the maintainer's duplicate-statement return: removed the entire private
`singleComparison_hom` declaration. No renamed or restated replacement is introduced.
Instead the endpoint calculation directly normalizes the three comparison components
using Mathlib's existing `Functor.mapDerivedCategorySingleFunctor` and
`DerivedCategory.singleFunctorIsoCompQ` definitions. Localized `conv` simplification
preserves the rest of the derived-morphism calculation.

The sole proof import remains
`WeilConjectures.CategoryTheory.DerivedCategory.Shift.ExactFunctor`; the original public
import is unchanged. Updated the node's proof and proof origin to describe this repair.
No other library modules, definitions, public statements, or interfaces change.

## Proved and sorry left

Closed the one original hole: `CategoryTheory.Abelian.Ext.mapExactFunctor_square`
(node `lem-pc-ext-exact-functor-square`). Added zero holes; split off zero statements.
No `sorry` remains in the delivered module. The sole private helper
`compositionComparison` is fully proved.

Single-file compilation through `lcompile.py` passed without errors or warnings.
The argument covers degree zero, zero classes, zero objects, and identity comparisons
without additional hypotheses. The delivery dry run checks axioms for all declarations.

## No longer needed

Removed the duplicate private declaration `singleComparison_hom` identified in the return.
The same-named declaration in `Sheaf.CategoryTheory.ExtExactFunctorCompositionComparison`
is private, so importing that module does not expose it. Direct normalization of the
existing Mathlib definitions avoids introducing or re-proving a duplicate theorem.

The earlier attempt's import `Sheaf.CategoryTheory.ExtExactFunctorCompositionComparison`
remains unnecessary: its public composition theorem imposes one common Ext universe.
The local composition helper has explicitly independent universe binders. The earlier
redundant zero-map lemma also remains removed; Mathlib already supplies that fact.

No baseline import is removed. The original proof-dependency nodes `def-pc-ext` and
`lem-weil-pbc-exact-functor-derived-factorization` remain needed. No blueprint unit or
realized step is bypassed; the unit's realized statement and step lists are empty.
No additional node or module is pruned.

## Where the brief, the DAG or earlier work was wrong

The returned delivery unnecessarily introduced `singleComparison_hom` with the exact
statement of a private helper in another module. The repair removes that declaration
outright and uses the existing Mathlib constructions directly at the calculation site.
It does not access private implementation names or change the other module's visibility.

The previous second reading predates this repair and has been removed for a fresh
independent reading. The public composition theorem's common Ext universe still prevents
its direct application to the unchanged square signature; the fully proved local
composition generalization retains independent universes explicitly.

## Second reading by R3

1. **Visibility and statements.** Compared the delivered module and node with the repository versions. The public theorem signature and all existing declarations are byte-for-byte unchanged; the only module interface addition is the plain proof import of `WeilConjectures.CategoryTheory.DerivedCategory.Shift.ExactFunctor`. The node statement, hypotheses, and conclusion are unchanged.

2. **Proof and axioms.** Compiled the module with `lcompile.py`; compilation succeeds without warnings. The file contains no `sorry`, `axiom`, `unsafe`, `opaque`, `implemented_by`, or `extern`, and no definition contains postponed data. The private composition helper is fully proved; the delivery dry run checks declaration axioms.

3. **Statements and duplication.** No statement was split off and no new public theorem was added. The removed private `singleComparison_hom` duplicate is not needed: endpoint calculations use the existing Mathlib definitions directly. The target theorem is exactly the node statement and applies to the independent Ext universes, including identity and zero cases by the same extensional proof.

4. **Pruning and route.** The proof uses the exact-functor derived factorization dependency and the new plain proof import; removing that import makes the Mathlib derived-category comparison constants unavailable. No proof-dependency node is unused, and the unit route remains represented by the existing node and realized metadata.

5. **DAG agreement.** The node proof steps and `proof_origin` describe the private universe-independent composition comparison and its two applications, matching the Lean proof. `proof_deps` remains exactly the declarations used by the proof; no new node or change record is required.

Changed only the report: independently verified the delivered proof and imports, and recorded the direct-normalization repair and pruning checks above.
