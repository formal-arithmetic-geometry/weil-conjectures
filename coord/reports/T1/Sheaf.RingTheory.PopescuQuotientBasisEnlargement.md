## What changed

Replaced the sorry in `Algebra.exists_popescu_admissible_quotient_basis` by a complete
Lean reduction. The original signature and public imports are unchanged. Moved the eight original proof-only
enlargement imports to the new denominator-basis module. Added proof-only
imports of Mathlib's vector-space bases, Hopkins–Levitzki, common-denominator
lemmas, and `Sheaf.RingTheory.PopescuDenominatorBasisEnlargement`.

The proved private helper `exists_residue_differential_basis` obtains an essentially-finite-type
residue field by the quotient surjection, uses differential finiteness and exact-differential
spanning, extracts a finite basis, and lifts it through the residue map. The proved private
helper `common_denominator` lifts a finite quotient family to the localization and clears all
its denominators at once. The proved private helper `span_range_mul_unit` shows that multiplying
all generators by a unit preserves their ideal span.

The main proof chooses finite generators of the original admissible subalgebra's maximal ideal,
maps their span using admissibility, and clears their denominators together with those of the
initial differential basis. It proves contraction of the quotient maximal ideal to the original
prime, hence membership of the cleared generator numerators in that prime. After applying the
new enlargement theorem, it explicitly constructs `ys i = μ (Sum.inr i) * s^(N-1)` and the
corresponding elements of A, and proves both their prime membership and their quotient span.
No definition, instance, existing interface, target, unit, or chapter was changed.

Both modules compile together without warnings through lcompile.py. The edge cases n = 1,
q = 0, an empty initial differential basis, and a zero maximal ideal are allowed. In particular,
the generator construction needs no separate n = 1 branch: the mapped span is already zero.

## Proved and sorry left

Closed the original hole in `Algebra.exists_popescu_admissible_quotient_basis` (1 of 1).
Its body is now complete, including finite basis extraction, common-denominator selection,
prime contraction, construction of the generator lifts, and equality of their ideal span.

Added one hole: `Algebra.exists_popescu_denominator_basis_enlargement`, in the new module
`Sheaf.RingTheory.PopescuDenominatorBasisEnlargement`, with node
`lem-weil-pbc-popescu-denominator-basis-enlargement`. Its proof is exactly `by sorry` and its
public docstring gives the full transcendental/separable enlargement argument and differential
rescaling. This is a decomposition (one original hole closed, one strictly narrower hole added),
not a sorry-free proof of the whole construction. The new theorem assumes the already-selected
initial differential basis and common denominator, and asserts no ideal-generator conclusion.
All generator choices and generation assertions are proved in the main module.

There are no other sorries in the delivered modules, and no public data definitions were added.

## No longer needed

Removed from the parent module (and retained as proof-plan imports in the new denominator-basis
module):

- `Sheaf.RingTheory.ArtinianLocalEssentiallyFiniteTypeResidue`
- `Sheaf.RingTheory.FlatAndFlatOfFlatFibreNoetherian`
- `Sheaf.RingTheory.HenselianEtaleRetraction`
- `Sheaf.RingTheory.HenselianFiniteEtaleEquivalence`
- `Sheaf.RingTheory.JacobiZariskiHomologySequence`
- `Sheaf.RingTheory.KaehlerDifferentialsPolynomialExtension`
- `Sheaf.RingTheory.LocalDimensionZeroHenselian`
- `WeilConjectures.Mathlib.RingTheory.Etale.Field`

The old parent proof dependencies no longer used directly by its completed Lean proof are:

- `lem-weil-pbc-localization-noetherian`
- `lem-weil-pbc-noetherian-local-quotient-artinian-local`
- `lem-weil-pbc-artinian-local-unique-prime`
- `def-weil-algebraic-element`
- `lem-weil-pbc-finite-type-algebra-noetherian`
- `lem-weil-pbc-criterion-flatness-fibre-noetherian`
- `def-weil-pbc-flat-ring-map`
- `lem-weil-pbc-flat-local-hom-faithfully-flat`
- `lem-weil-pbc-faithfully-flat-ideal-contraction`
- `def-weil-pbc-finite-type-algebra`
- `lem-weil-pbc-artinian-local-essentially-finite-type-residue`
- `lem-weil-pbc-kahler-differentials-polynomial-extension`
- `lem-weil-pbc-kahler-differentials-localization`
- `lem-weil-pbc-separable-first-purely-inseparable`
- `def-weil-pbc-separable-algebraic-extension`
- `lem-weil-pbc-finite-separable-extension-etale`
- `lem-weil-pbc-local-dimension-zero-henselian`
- `lem-weil-pbc-henselian-finite-etale-equivalence`
- `lem-weil-pbc-etale-ring-base-change`
- `lem-weil-pbc-henselian-etale-retraction`
- `lem-weil-pbc-etale-ring-map-iff-etale-affine`
- `lem-weil-pbc-jacobi-zariski-homology-sequence`

All of these dependencies remain in the new enlargement node's plan; none is claimed globally
unreached or pruned from the target closure. No unit-level node or route was removed.

## Where the brief, the DAG or earlier work was wrong

No statement error was found. The geometric regularity hypothesis is preserved in the original
signature; the reduction shows that the denominator-aware enlargement itself needs only the
admissibility hypotheses, not geometric regularity. The new narrower theorem therefore omits
that hypothesis without changing any existing interface.

The ancestor helper cannot follow the parent's `created.item`, which is a module name rather
than a DAG node id, and prints a null ancestor. The new node carries the known blueprint ancestor
`thm-weil-pbc-finite-etale-lifting` already recorded on the solution-modulo-choose node, with the
explicit intervening node chain. A whole-blueprint search for “denominator differential basis”
found no matching node. The LeanSearch service returned Internal Server Error; the failed search
is recorded as unavailable, and LeanFinder, Loogle, and source grep were also run.

## New nodes

`lem-weil-pbc-popescu-denominator-basis-enlargement` isolates steps 5–14 of the parent:
transcendental polynomial localization or finite separable residue lifting, admissibility of the
image, capture of a denominator power, and transport/rescaling of the differential basis. It
accepts the initial differential basis and its common-denominator equations as hypotheses, and
returns an enlarged admissible subalgebra with the differential basis and a denominator power.
The quotient generator argument is deliberately outside its statement and is proved in the
parent. Its source is the existing parent argument from Stacks 07FH/07FI, and its complete proof
is written in its docstring and DAG steps. No change record is needed because no existing
signature or definition changed.

## Second reading by T1

1. **Visible interface: PASS.** Read both delivered modules and compared the parent with
   the repository using `diff -u`. The only existing declaration is
   `Algebra.exists_popescu_admissible_quotient_basis`; its full signature is byte-identical.
   All original public imports and visibility are unchanged. No definition, instance,
   target, or statement was changed, so no change record is required. The parent node
   changes only `proof`, `proof_deps`, and `proof_origin`.

2. **Proof and axioms: PASS as a decomposition.** Compiled both modules in import order
   through `lcompile.py`, without errors or warnings. Scanned the delivered sources:
   the parent has no `sorry`, and the new module has exactly the reported named theorem
   ending `:= by sorry`. There is no forbidden axiom/compiler escape and no new data
   definition. Scratch copies with `#print axioms` show only `propext`, `Classical.choice`,
   and `Quot.sound` for the three private helpers; the two public theorems additionally
   use `sorryAx`, as expected for the remaining enlargement hole. Existential elimination
   in the parent's propositional proof exports no arbitrary witness as a definition.

3. **Split statement: PASS.** Checked every hypothesis and conclusion against its node
   and read the full docstring argument. Independently compared the construction with
   [Stacks 07FH](https://stacks.math.columbia.edu/tag/07FH) and
   [Stacks 07FI](https://stacks.math.columbia.edu/tag/07FI); the listed TeX source is absent
   on this machine, so these authoritative pages supplied the source text. The
   transcendental polynomial localization and finite separable étale lift preserve
   admissibility, and a sufficiently large positive p-power kills the nilpotent error.
   In the separable case the differential of the captured power is computed in
   F₀(β) as d(β^q′), so the argument does not assume α itself belongs to that field.
   Scaling the old basis and appending dα in the transcendental case gives the specified
   lifts. Checked n = 1, q = 0, s = 1, an empty initial basis, and a zero maximal ideal:
   no contradiction or missing nonzero/positivity assumption was found. The split lemma
   assumes a selected initial basis and denominator and proves no generator conclusion;
   it is strictly a part of the argument, not a renamed parent theorem. Its remaining
   field-extension construction cannot be closed by a few elementary tactics.
   Independent LeanFinder, Loogle, and grep searches used new wording (recorded on the
   new node), and `rg` searched both Lean roots. No equivalent available enlargement
   result was found; the downstream differential-basis theorem uses this parent and
   would be circular as a replacement.

4. **Route and pruning: PASS after repair.** The parent genuinely proves finite basis
   selection from exact differentials, finite ideal generation, common-denominator
   clearing, prime contraction, and unit rescaling of the ideal span. Reviewed each
   equality, including N − 1 + 1 = N and the contraction J^n ≤ J using n ≥ 1.
   The original eight enlargement imports belong to the remaining split construction:
   restored them as plain proof-plan imports in its new module. Removed the redundant
   parent import `Mathlib.LinearAlgebra.Dimension.Finite` after a scratch compilation
   without it succeeded. The report now lists every removed parent import and every
   removed direct old proof dependency, distinguishing relocation from global pruning.
   Read `dag/units/sk-thm-p1.json` and its `realized` route: neither this parent nor the
   split lemma replaces a realized unit step, and the existing unit route is unchanged.
   One hole is closed and one added: net zero; no globally pruned module is claimed.

5. **DAG/Lean agreement: PASS after repair.** Both nodes' verbatim Lean signatures match
   their source files; each `proof_deps` set equals the union of the proof steps' `uses`.
   The parent's revised steps describe the actual four-stage Lean reduction. The new
   node has its source, complete two-case proof, statement dependencies, chapter/unit,
   split status, creation record, blueprint ancestry, search results, and Lean record.
   Added the missing empty source-checkout `lean_audit` records and appended the
   independent second-reader searches. Its proof-only dependency imports are now in
   the module that owns the remaining construction.

Second-reading changes: repaired the new module's proof-plan imports; removed one redundant
Mathlib import from the parent; corrected the import/dependency accounting; completed new-node
audit/search metadata. No theorem statement or proof body was changed.
