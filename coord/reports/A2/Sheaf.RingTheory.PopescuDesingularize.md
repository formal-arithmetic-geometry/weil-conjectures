## What changed

`Sheaf.RingTheory.PopescuDesingularize`: replaced the hole in
`Algebra.exists_desingularization` without changing its signature. The proof takes the
quotient construction data, uses the generic local elimination theorem at primes over π,
and proves the final ideal containment using the nonsmooth zero locus and radicality.

Added `Sheaf.RingTheory.PopescuDesingularizationQuotientData`, containing the remaining
construction theorem, and `Sheaf.RingTheory.QuadraticRelationsSmoothQuotient`, containing
a fully proved local quotient theorem. The latter proves flat annihilator stabilization,
quadratic-ideal vanishing by Nakayama, finite denominator clearing, and the smooth principal
localization isomorphism. Its private helpers are all proved. These helpers do not choose
data for any public definition; the quotient construction is an existential theorem used
only inside a proof.

The existing node's proof and dependencies now follow the Lean reduction. All new proof
imports are nonpublic. The main module preserves its public imports and all existing
signatures. No other existing module is adapted.

## Proved and sorry left

Closed the original hole: `Algebra.exists_desingularization`
(node `lem-weil-pbc-popescu-desingularize`). This is a decomposition, not an unconditional
proof of the desingularization theorem: one upper hole closed, one construction hole added,
net zero holes for this delivery before import-closure effects.

Proved with no sorry: `Algebra.smoothAtPrime_quotient_of_quadratic_relations`
(node `lem-weil-pbc-quadratic-relations-smooth-quotient`). `#print axioms` reports exactly
`propext`, `Classical.choice`, and `Quot.sound`. Its three private helpers are also proved.
The original module contains no remaining sorry.

The only sorry added and left in the delivery is
`Algebra.exists_desingularization_quotient_data`
(node `lem-weil-pbc-popescu-desingularization-quotient-data`). It is exactly a public named
theorem with the whole proof `:= by sorry`, a source and the full construction proof in its
docstring. It covers source steps 1–9 and the relation-ideal observations. It does not assume
any singular-ideal containment or any smoothness of the quotient at primes containing π.
Source steps 10–12 are implemented by the proved local lemma and the main proof.

Compilation: all three modules compile in dependency order using `lcompile.py --all`.
The required `deliver3.py --no-push` dry run printed OK: compilation and preflight pass,
except for the expected second reading, which is reserved for the next worker. Nothing
was pushed.

Edge checks: π=0 forces K=0 by the divisibility hypothesis of the local lemma; π invertible
makes its prime-over-π hypothesis impossible. K=0 and the zero ring need no exceptions. The
finite-generator argument takes denominator 1 for an empty generator set. No cancellability
of π is assumed: annihilator stability is derived from flatness and the invertible r. In the
construction proof the g-polynomials must be obtained by expansion, not by cancellation of
π³. Finite polynomial quotients can be lifted to universe max u w without changing their
algebraic properties.

## No longer needed

Removed direct proof imports from `PopescuDesingularize`:

- `Sheaf.AlgebraicGeometry.FlatSmoothFibreSmoothAtPrime`
- `Sheaf.LinearAlgebra.Matrix.LeftInverseMinors`
- `Sheaf.RingTheory.AnnihilatorElementFlatBaseChange`
- `Sheaf.RingTheory.EquationCountFibreDimensionFlat`
- `Sheaf.RingTheory.StandardSmoothDimensionAtPoints`
- `Sheaf.RingTheory.StrictlyStandardLocalizationSmooth`
- `WeilConjectures.Mathlib.Topology.KrullDimension`

The matrix, fibre, dimension and strictly-standard-localization nodes remain mathematical
proof dependencies of the construction node. They have been relocated, not claimed as
pruned from the complete mathematical argument. Annihilator base change remains a needed
import of the proved local quotient module.

Two original planned nodes are no longer used anywhere in this delivery's argument:
`lem-weil-pbc-krull-intersection-jacobson` (replaced by Mathlib Nakayama, recorded through
`lem-weil-pbc-nakayama-jacobson`) and
`lem-weil-pbc-localization-at-prime-of-quotient` (replaced by injectivity and surjectivity
of the canonical map between principal localizations after clearing denominators).
Also removed the redundant proof import `Mathlib.RingTheory.Localization.Ideal` from the
new local-quotient module; it is already public through its statement import of prime
localization. All other original mathematical dependencies occur either in the construction node, the
local quotient node, or the main node. No module is claimed to leave every target's closure;
that requires the global ledger calculation.

Complete inventory of original `proof_deps` removed from the main node (construction
means the new quotient-data node; local quotient means the new proved quotient node):

| Original dependency | Where it remains, or why removed |
|---|---|
| `def-kun-dimension` | construction |
| `def-kun-topological-dimension-at-point` | construction |
| `def-weil-pbc-finitely-presented-algebra` | construction |
| `def-weil-pbc-flat-ring-map` | construction, local quotient |
| `def-weil-pbc-localization-at-prime` | construction, local quotient |
| `def-weil-pbc-mv-polynomial-ring` | construction |
| `def-weil-pbc-noetherian-ring` | local quotient |
| `def-weil-pbc-polynomial-partial-derivative` | construction |
| `def-weil-pbc-smooth-ring-map` | construction |
| `def-weil-pbc-standard-smooth-algebra` | construction |
| `def-weil-pbc-strictly-standard-element` | construction |
| `lem-weil-pbc-annihilator-element-flat-base-change` | local quotient |
| `lem-weil-pbc-equation-count-fibre-dimension-flat` | construction |
| `lem-weil-pbc-flat-smooth-fibre-smooth-at-prime` | construction |
| `lem-weil-pbc-krull-intersection-jacobson` | Unused; replaced as explained above |
| `lem-weil-pbc-localization-at-prime-of-quotient` | Unused; replaced as explained above |
| `lem-weil-pbc-localization-noetherian` | local quotient |
| `lem-weil-pbc-localization-of-localization` | local quotient |
| `lem-weil-pbc-localization-quotient-commute` | construction |
| `lem-weil-pbc-matrix-left-inverse-minors` | construction |
| `lem-weil-pbc-polynomial-ring-smooth` | construction |
| `lem-weil-pbc-presentation-base-change` | construction |
| `lem-weil-pbc-smooth-ring-map-base-change-composition` | construction |
| `lem-weil-pbc-smooth-ring-map-principal-localization` | local quotient |
| `lem-weil-pbc-standard-smooth-is-smooth` | construction |
| `lem-weil-pbc-standard-smooth-over-field-dimension-at-points` | construction |
| `lem-weil-pbc-strictly-standard-localization-smooth` | construction |

## Where the brief, the DAG or earlier work was wrong

No statement discrepancy was found. The original step 10 used Krull intersection to kill
(π)K, but the inclusion (π)K ≤ (π²)K directly supplies the hypotheses of Nakayama. The
original step 11's principal-neighbourhood argument is now formalized explicitly using the
localized quotient map's bijectivity.

LeanSearch returned HTTP Internal Server Error for both intermediate-statement queries.
These searches are recorded as unavailable, with no false no-match verdict. LeanFinder,
Loogle and local Mathlib/source searches were available.

The source files under `literature/stacks-project/` and the blueprint section file are not
present in this clone. The existing node and unit records were read, and the Stacks proof
was checked at https://stacks.math.columbia.edu/tag/07CR. No literature file was downloaded
or written. WANTED: local copy of `literature/stacks-project/smoothing.tex`, Tag 07CR, for
`lem-weil-pbc-popescu-desingularization-quotient-data`; its source record uses the project's
existing canonical citation.

## New nodes

`lem-weil-pbc-popescu-desingularization-quotient-data`:
`Algebra.exists_desingularization_quotient_data` in
`Sheaf.RingTheory.PopescuDesingularizationQuotientData`. The construction up to B=S/K,
with divisibility, quadratic relations, factorization, smoothness away from π and
smoothness/flatness of S above π. One remaining hole; strictly the construction part of
07CR, with no annihilator-good-prime smoothness conclusion.

`lem-weil-pbc-quadratic-relations-smooth-quotient`:
`Algebra.smoothAtPrime_quotient_of_quadratic_relations` in
`Sheaf.RingTheory.QuadraticRelationsSmoothQuotient`. A generic theorem about a given
quotient and prime, independent of the input algebra, strictly standard presentations and
sections modulo π⁴. Fully proved. Both nodes keep the original chapter, unit and blueprint
ancestry. No change record is needed because no existing interface changed.

## Second reading by A2

1. **Existing interfaces: PASS.** Compared the main module with the repository using
   `diff -u` and compared the complete declaration text before `:= by` programmatically:
   the signature of `Algebra.exists_desingularization` is byte-for-byte identical.
   The four existing public imports and the original definitions/docstrings are unchanged.
   The other two modules are new; there are no forced adaptations or interface changes.

2. **Proof and trust: PASS as a decomposition.** Independently compiled all three modules
   with `lcompile.py --all`, without errors or warnings. Scratch copies under
   `scratchpad/axioms` printed axioms for all three public theorems and all three private
   helpers. The local quotient theorem and its helpers use only `propext`,
   `Classical.choice`, and `Quot.sound`. The construction theorem and the main theorem
   additionally use `sorryAx`, exactly as expected from the one remaining named theorem.
   No forbidden declaration or hollow definition occurs. Existential construction data
   are unpacked only within a proposition proof; no public definition chooses an arbitrary
   witness of the unproved existence theorem.

3. **Split statements: PASS.** Read both statements and the complete construction
   docstring against [Stacks Tag 07CR](https://stacks.math.columbia.edu/tag/07CR).
   The remaining hole covers the polynomial construction and its relations, not the
   original singular-ideal conclusion. The main theorem implements the remaining local
   elimination and radical argument; this is a genuine reduction, not a renamed target.
   In the local proof Nakayama kills `(π)K`, flat annihilator base change makes
   `Ann(π²)=Ann(π)` after inverting the obstruction, and hence kills `K` itself.
   Checked π=0 (divisibility forces K=0), π a unit (no prime above π), K=0, c=0,
   no remaining relations, empty generator sets, and zero rings. The construction uses
   expansion to obtain g rather than invalid cancellation of π³, including for
   zero divisors. Its identity Jacobian in the v variables works also for c=0.
   Independent searches used different wording: LeanFinder for smooth neighbourhoods
   descending through finite quotients and for auxiliary-variable factorizations,
   Loogle `Ideal, _ ≤ _, _ = ⊥`, and Mathlib grep for annihilator powers and quotient
   smoothness. Also searched `lean/Sheaf`, `lean/WeilConjectures`, and the upstream
   source file inventory. Hits supply Nakayama, localization maps and smooth-neighbourhood
   machinery already used; none closes the construction theorem or replaces the entire
   proved local quotient lemma. The large polynomial construction cannot be closed by a
   short application of an existing result.

4. **Route and pruning: PASS.** Read `dag/units/sk-thm-p1.json`, including `realized`.
   No unit statement, step or realizing node is bypassed; the changes are below unit level
   and implement the original desingularization steps. Every newly added proof import is
   plain `import`. The new modules' public imports provide their statement vocabulary.
   The report now explicitly inventories every old main-node dependency removed from its
   direct `proof_deps`, distinguishing relocation into the construction/local quotient
   nodes from the two genuinely unused planned nodes. No globally pruned module is claimed.

5. **DAG agreement: PASS.** Existing node changes are exactly `proof`, `proof_deps`, and
   `proof_origin`; its statement and Lean signature record stay unchanged. Checked the
   step-use union equals `proof_deps` for each of the three delivered nodes, all cited
   node IDs exist, new nodes carry source, complete proof plan, statement dependencies,
   creation group/item/date, chapter/unit, blueprint ancestry and verbatim normalized
   Lean statements. Both new nodes record the three required real search kinds, with
   the unavailable LeanSearch queries honestly marked unavailable. The local node's
   Nakayama and principal-localization references match the Mathlib declarations used.

**Second reader changes:** added the complete removed-dependency inventory and this
independent review. No Lean proof, statement, import or node required repair. Holes closed:
`Algebra.exists_desingularization`; holes added:
`Algebra.exists_desingularization_quotient_data`. This remains one-for-one decomposition,
with `Algebra.smoothAtPrime_quotient_of_quadratic_relations` fully proved and no additional
holes. Axiom scratch copies are outside the delivered `lean/` tree.
