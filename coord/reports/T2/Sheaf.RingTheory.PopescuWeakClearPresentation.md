## What changed

The existing theorem `Algebra.exists_cleared_submersive_presentation` keeps its exact
signature and is reduced to clearing the defining equations/Jacobian certificate and
then clearing the auxiliary relations. It combines the scalars with `Fin.cases`.
Its two new imports are proof-only. The new core theorem records the essential extra
invariant: the extended ideal of the cleared equations equals the evaluation kernel.
The auxiliary-relation theorem is proved using Mathlib's polynomial-localization
instance and ideal-membership criterion. No existing definition or public import changed.

## Proved and sorry left

Hole closed in the original module:
- `Algebra.exists_cleared_submersive_presentation`
  (`lem-weil-pbc-popescu-weak-clear-presentation`), proved conditionally on the core theorem.

Hole added:
- `Algebra.exists_cleared_submersive_presentation_core`
  (`lem-weil-pbc-popescu-weak-clear-core`), in `Sheaf.RingTheory.PopescuWeakClearCore`.
  This is the sole remaining `sorry` in the delivery; it has a complete source-backed
  proof in its docstring and DAG node.

New theorem proved without `sorry` or dependence on `sorry`:
- `Algebra.exists_cleared_submersive_relations`
  (`lem-weil-pbc-popescu-weak-clear-relations`). The second reader closed the hole
  initially left in this declaration after repairing its false statement.

This is a decomposition: one original hole closed and one lower hole added, net zero
holes removed from the targets' import closure. It is not a completed unconditional
proof of the original theorem. No data definition or arbitrary witness definition was added.

## No longer needed

No original imports or modules were pruned. Removed the redundant proof import of
`Mathlib.RingTheory.Localization.Ideal` from the new relation module; it is already
publicly imported by `Mathlib.RingTheory.Localization.AtPrime.Basic`.
The item's old direct proof dependencies are no longer direct dependencies:
`lem-weil-pbc-polynomial-scalar-extension`, `lem-weil-pbc-localization-base-change`,
`def-weil-pbc-localization-at-prime`, `def-weil-pbc-module-localization`,
`def-weil-pbc-standard-smooth-algebra`, and `def-weil-pbc-polynomial-partial-derivative`.
They remain used in the core plan or proved relation lemma and are not globally pruned.
The item's new direct dependencies are precisely the core and relation nodes.

## Where the brief, the DAG or earlier work was wrong

The first worker's auxiliary-relation lemma was false: it assumed only that f vanishes
at P.val, rather than that f generates the localized kernel. Take R = Q, p = (0),
D = Q with the submersive presentation Q[X]/(X), n = c = t = 1, m = 0, f = 0 and
 g = X. All of its hypotheses hold, but no s outside p has s*X in (0).
This invalid lemma was replaced before delivery: the new core supplies the kernel
identity and the relation theorem assumes and uses it. These declarations are new,
so no existing interface was changed and no change record is needed.

The core initially had no natural-language proof, and the new nodes had placeholder
statements ("core", "relations") and unspecific proof steps. Repaired all of these.
The existing item's DAG initially still described the unsplit proof; updated its proof
and proof_deps to the actual reduction. The first report's two open statements are
superseded by one open core and a proved relation lemma.

## New nodes

`lem-weil-pbc-popescu-weak-clear-core`, module `Sheaf.RingTheory.PopescuWeakClearCore`,
states the equation/Jacobian clearing part together with localized kernel generation.
Its full proof follows the denominator-clearing paragraphs of Stacks Tag 07F9
(`smoothing.tex`, `lemma-delocalize-weak`, lines 2179–2188). It has no auxiliary g or
relation certificates and is a proper part of the original argument, not its restatement.

`lem-weil-pbc-popescu-weak-clear-relations`, module
`Sheaf.RingTheory.PopescuWeakClearRelations`, states the auxiliary-relation consequence
of a given localized kernel identity and is proved using
`MvPolynomial.isLocalization`, `IsLocalization.algebraMap_mem_map_algebraMap_iff`,
`MvPolynomial.aeval_map_algebraMap`, and `MvPolynomial.aeval_rename`.
No change records and no forced adaptations.

## Second reading by T2

1. Compared the delivered main module with the repository using `diff`: its only
   original declaration has byte-for-byte identical text before `:= by`, including
   all universes, instances, hypotheses, and conclusion. Only proof-only imports and
   the proof changed. No existing data or definitions changed. The two repaired
   helper signatures are new declarations, absent from the repository.
2. Compiled all three modules in import order through `lcompile.py`, with no errors
   or warnings. Inspected all sources for forbidden constructs and holes: only the
   named core theorem has `sorry`; no definitions were introduced. A scratch copy
   with `#print axioms` showed the relation theorem uses only `propext`,
   `Classical.choice`, and `Quot.sound`. The main and core also show `sorryAx`,
   accounted for by that one explicitly reported core hole. The scratch source was
   removed before delivery.
3. Rejected the false original relation lemma using the Q[X]/(X), f=0, g=X
   counterexample above. The repaired hypothesis is necessary, and its kernel
   rewriting and localization-membership argument now compile as a complete proof.
   The core's coefficient clearing, unit rescaling of the Jacobian and finite
   certificate clearing agree with the cited Stacks paragraphs, read from the local
   Stacks source. Checked c=0 (empty determinant 1; no equations), t=0 (no auxiliary
   choices), n=m=0, and a possible zero target D (allowed). Noninjective localization
   is handled by the extra scalar annihilating the kernel error; no domain or
   Noetherian hypothesis was silently used. Core and relation node statements are
   now self-contained, with complete docstring proofs. Repeated searches with Loogle
   (`IsLocalization.algebraMap_mem_map_algebraMap_iff`), LeanFinder (descent of finite
   polynomial equations and a unit Jacobian minor), and grep of Mathlib and both
   library roots. Read the returned `SubmersivePresentation.ofHasCoeffs` machinery:
   it requires all coefficients already lie in the smaller coefficient ring and
   does not supply the required clearing to the fixed R. The localization criterion
   found by search closes the auxiliary relation hole. No existing equivalent core
   or specialized relation theorem was found.
4. The proof starts at the original theorem and separates its equation/Jacobian
   construction from the now-proved ideal-membership consequence. The new core
   contains no g and no auxiliary-relation conclusion, so the reduction is not a
   renamed restatement. Both new main imports are plain `import`. The sole additional
   relation import supplies the polynomial-localization instance and is proof-only.
   Removed the redundant localization-ideal import. Inspected `dag/units/sk-thm-p1.json`
   and its `realized` routes: this is a split below the unit level, retains the same
   Popescu argument, and bypasses no realized unit statement or step. No original
   module is pruned; all old direct proof dependencies are accounted for above.
5. Opened and repaired both new nodes and the existing item's node. Their signatures
   match the Lean verbatim; the existing item's proof uses the core and relation
   declarations then Fin.cases, and proof_deps is the union of step uses. The core
   plan records coefficient localization, clearing equations while preserving the
   kernel, and clearing the inverse-determinant identity. The relation node records
   the actual evaluation rewriting and Mathlib ideal-membership proof. Both nodes
   carry source, proof_origin, searches, chapter/unit, creation and Lean metadata.

Second reading changed: repaired the false relation statement; strengthened the new
core with localized kernel generation; proved the relation lemma; expanded the core's
proof docstring; repaired placeholder node statements and proof plans; updated the
parent dependency record and report; removed a redundant proof import and resolved
one letI linter warning. The existing theorem's statement is unchanged.
