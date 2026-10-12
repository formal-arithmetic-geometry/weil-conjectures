## What changed

Filled the proof of
`Algebra.exists_finite_subalgebra_away_of_isQuasiFiniteAtPrime` in
`Sheaf.RingTheory.QuasiFiniteAtFiniteSubalgebraAway`. No signature, visibility,
definition or import changed.

The existing `Algebra.zariskisMainProperty_of_isQuasiFiniteAtPrime` supplies
`ZariskisMainProperty R q.asIdeal` directly: its existential conclusion is the
definition of that property. Mathlib's
`Algebra.ZariskisMainProperty.exists_fg_and_exists_notMem_and_awayMap_bijective`
then carries out the finite-subalgebra construction, including integrality,
injectivity and surjectivity. Finally `Module.Finite.of_fg` converts the
subalgebra's finitely generated underlying submodule to the required finite
module. The original five-step mathematical route and the unit route are kept;
steps 2–5 are already formalized by the Mathlib theorem rather than rewritten.
No DAG route change or new node is needed.

Checked the full signatures and implementation in
`Mathlib/RingTheory/ZariskisMainTheorem.lean` (lines 666–701), and
`Module.Finite.iff_fg`/`of_fg` in `Mathlib/RingTheory/Finiteness/Basic.lean`.
LeanFinder, Loogle and grep searches were run through `msearch.py`; Loogle and
grep confirmed the exact construction theorem. The project theorem and the
Mathlib construction both compile in the sandbox with the original universes
and all original hypotheses.

## Proved and sorry left

Closed the only hole:
`Algebra.exists_finite_subalgebra_away_of_isQuasiFiniteAtPrime`
(node `lem-weil-pbc-quasi-finite-at-finite-subalgebra-away`).
One hole closed; zero holes added. No sorry remains in the delivered module.
This is a proof, not a decomposition: no intermediate statements were added.
The imported project Zariski-main theorem is itself proved.

## No longer needed

None. All existing imports are used: `QuasiFiniteAtPrime` supplies the
hypothesis, `Localization.Away.Basic` supplies the canonical map in the
statement, and `ZariskisMainAway` supplies the first step and Mathlib's
construction theorem. The mathematical ingredients of the original DAG plan
are used inside that Mathlib construction; no separate new work is needed to
reimplement its fraction calculations. No unit statement or step is bypassed.

## Where the brief, the DAG or earlier work was wrong

No statement error found. The original candidate warning about translating
quasi-finiteness is now resolved by the already-proved
`zariskisMainProperty_of_isQuasiFiniteAtPrime`; its conclusion is definitionally
`ZariskisMainProperty`, so the exact Mathlib construction applies without a new
translation lemma. The local Stacks TeX file is absent on this machine;
this delivery follows the existing sourced plan and its Mathlib formalization,
and adds no unproved theory or new source-dependent claims.

## Second reading by J3

1. **Unchanged interface: PASS.** Compared the delivered module with the
   repository using `diff -u`. The only difference is the replacement of the
   theorem's `sorry` by its proof. The existing signature, universes, hypotheses,
   visibility, definitions, docstrings and imports are byte-for-byte unchanged.
   No change record or forced adaptation is needed.
2. **Kernel proof: PASS.** Compiled the delivered file through `lcompile.py`
   without errors or warnings. Compiled a scratch copy with `#print axioms` for
   `Algebra.exists_finite_subalgebra_away_of_isQuasiFiniteAtPrime` and the imported
   `Algebra.zariskisMainProperty_of_isQuasiFiniteAtPrime`: both use exactly
   `propext`, `Classical.choice` and `Quot.sound`, with no `sorryAx`. The delivered
   file has no remaining `sorry`, forbidden declaration or data definition.
3. **Split-off statements: PASS (none).** No statement or helper was introduced,
   so no new node or docstring proof is missing. Checked the exact Mathlib
   construction and finiteness lemmas, and independently searched the project
   for finite-subalgebra and localized-bijectivity results. No repair or further
   split is required. The proof adds neither nontriviality nor domain assumptions;
   it retains the original general commutative-ring statement. A zero target
   ring has no prime and therefore no instance of the premise.
4. **Shortest route and pruning: PASS.** The existing proved Zariski-main
   declaration supplies the precise `ZariskisMainProperty`; the Mathlib theorem
   constructs the finite integral adjoin and proves the localized map bijective.
   Read its implementation at lines 666–701, including `fg_adjoin_of_finite`,
   injectivity of localization of the inclusion and the surjectivity argument.
   Read `finite_adjoin_of_finite_of_isIntegral`: it is precisely
   `Module.Finite.of_fg` applied to `fg_adjoin_of_finite`, the two ingredients used
   here. The original proof dependencies are therefore still mathematical
   ingredients of this route, including the finite-integral-generators leaf;
   none is retired. The two public imports supply the signature's quasi-finite
   predicate and canonical away map; the Zariski-main import is proof-only.
   Read `dag/units/sk-thm-p1.json`: this item is below its realized statements
   and steps, and the existing route through Zariski's main theorem is kept.
   No unit route or realized entry changes, and nothing is pruned.
5. **DAG agreement: PASS.** Read the item's node and the finite-integral-generators
   Mathlib leaf. The five planned mathematical steps are implemented by the
   existing Zariski-main theorem followed by Mathlib's finite-adjoin construction,
   with exactly the same objects and conclusion. The existing `proof`,
   `proof_deps` and document `proof_origin` remain accurate; using their Mathlib
   formalization requires no node change. There are no new nodes to audit.

Second reading changed only this report, adding the independent review and
explicit axiom-check evidence. The Lean proof was correct as delivered.
