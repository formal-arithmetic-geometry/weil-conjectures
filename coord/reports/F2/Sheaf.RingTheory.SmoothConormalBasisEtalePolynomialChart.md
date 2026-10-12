## What changed

Replaced the sole remaining sorry in
`Algebra.exists_etale_polynomial_chart_core` by a compiling reduction into the
unramified-localization and fibrewise-flatness parts of Stacks 07CH. The original
signatures and visibility are unchanged. The existing
`Algebra.exists_etale_polynomial_chart_of_conormal_basis` still projects this result.

The proved private helper `exists_conormal_matrix` constructs the Jacobian right
inverse from Mathlib's split conormal injection, polynomial differential basis,
and the supplied equation basis. It contains no sorry and uses only Mathlib.
The chart homomorphism is constructed explicitly by polynomial evaluation and
localization; no definition chooses data from an unproved existence theorem.

Added proof-only imports of `Mathlib.RingTheory.Kaehler.Polynomial`,
`Mathlib.LinearAlgebra.TensorProduct.Basis`, `Mathlib.RingTheory.Smooth.Fiber`,
`Sheaf.RingTheory.ConormalChartUnramifiedLocalization`, and
`Sheaf.RingTheory.UnramifiedSmoothConormalChartFlat`. The last two are new modules,
one remaining theorem each. Updated the core node's proof and dependencies.

All three modules compile together through lcompile.py without warnings. The
combination proves finite presentation over the corrected-coordinate polynomial
base using scalar restriction, applies the Mathlib flat-unramified criterion,
and proves the canonical-constants equation from the constructed AlgHom.

## Proved and sorry left

Closed the one existing hole: `Algebra.exists_etale_polynomial_chart_core`
(node `lem-weil-pbc-smooth-conormal-basis-etale-polynomial-chart-core`).
Its matrix step is proved, and its final assembly is complete Lean. This is a
**decomposition**, not an axiom-free proof: two strictly simpler holes were added.
There are no sorries left in the assigned module.

New holes:

- `Algebra.exists_unramified_conormal_polynomial_chart`
  (`lem-weil-pbc-conormal-chart-unramified-localization`): the explicit matrix
  identity implies differential vanishing after a zero-section-preserving
  localization. This lemma assumes neither smoothness nor a conormal basis and
  concludes formal unramifiedness, not flatness or etaleness.
- `Algebra.flat_of_unramified_smooth_conormal_chart`
  (`lem-weil-pbc-unramified-smooth-conormal-chart-flat`): conditional flatness of
  any already-unramified chart into the localized smooth extension. It constructs
  neither a chart nor a localization element and does not assume the specified
  equation classes are the given basis.

Each new hole is a public theorem whose whole proof is `by sorry`, with a source,
complete proof in words and a matching node. Their explicit edge-case checks
cover n=0, c=0, zero quotients, zero localizations and empty residue-field fibres.
The two holes replace one existing hole (net +1), with an actual matrix proof
and finite-presentation/etaleness assembly between them.

## No longer needed

No import present in the original module was removed: its four public imports
are retained unchanged.

The legacy proof plan's principal-localization conormal splitting lemma
`lem-weil-pbc-smooth-localization-conormal-split` and module
`Sheaf.RingTheory.SmoothLocalizationConormalSplit` are not needed on this route.
Both the proved matrix argument and the new flatness plan instead use Mathlib's
`Algebra.FormallySmooth.iff_split_injection` directly on the original quotient.
The temporary candidate proof import
`Sheaf.RingTheory.JacobiZariskiQuotientSmooth` was also removed; it was not an
original import and does not constitute a baseline pruning gain.

The legacy final scheme-theoretic detour through affine spectrum, the definitions
of locally finite presentation/flat/unramified/etale morphisms and the ring-map
versus affine-morphism comparisons is unnecessary for the proof: Mathlib's
`Algebra.Etale.of_formallyUnramified_of_flat` supplies the ring conclusion directly.
The unchanged statement dependencies retain the original meaning of etaleness.
No unit statement or unit proof step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The core node's proof was one undivided instruction with no proof dependencies,
although the module's legacy docstring explains the substantial matrix,
Nakayama, and fibrewise-flatness work. The updated core node now records the
actual compiled matrix calculation, the two separate unfinished arguments,
and the final Mathlib assembly.

The localization has an existing polynomial scalar action through the original
quotient as well as the corrected-coordinate action. Flatness must use the latter.
The new flatness signature explicitly installs the Module structure induced by
its AlgHom; the assigned proof explicitly installs that Algebra, SMul and Module.
Without this, typeclass search can choose the original quotient action. No
existing interface was changed to resolve this issue.

The local literature file was unavailable on this machine; the source proof was
read at https://stacks.math.columbia.edu/tag/07CH. LeanSearch returned Internal
Server Error for both new claims; LeanFinder, Loogle and local source searches
were available and are recorded. No existing exact statement was found.

## New nodes

`lem-weil-pbc-conormal-chart-unramified-localization`, in
`lean/Sheaf/RingTheory/ConormalChartUnramifiedLocalization.lean`, separates the
explicit-coordinate differential calculation and Nakayama localization. Its
matrix hypothesis is supplied by the proved private helper, not by another sorry.

`lem-weil-pbc-unramified-smooth-conormal-chart-flat`, in
`lean/Sheaf/RingTheory/UnramifiedSmoothConormalChartFlat.lean`, separates the
conditional fibrewise flatness argument of the source. Its proof plan records
the split conormal rank calculation, regular local fibres, miracle flatness,
and fibrewise flatness criterion.

Both nodes inherit chapter `sec-proper-base-change` and unit `sk-thm-p1`.
No change record is necessary: existing signatures, definitions and public
imports are unchanged.

## Second reading by F2

1. Compared the delivered item module with the repository version. Existing
declaration signatures and visibility are unchanged; the core proof and
proof-only imports are the only item changes.

2. Compiled all three delivered modules with `lcompile.py`; they compile
without errors or warnings. The item has no remaining `sorry`; the two new
public split theorems are the only intentional `sorry`s, with matching nodes
and source/docstring proofs. No forbidden declarations or hollow definitions
were found.

3. Checked both split statements against the edge cases recorded in their
docstrings (empty variable/equation sets, zero rings, zero quotients and empty
fibres). They are strictly simpler conditional reductions and do not restate
the item. Searches found no existing theorem with either statement.

4. The proof follows the shortest available Mathlib route for the matrix and
étale assembly, while retaining the unit's corrected-coordinate and flatness
steps. The added imports are proof-only; no baseline public import was removed.
The legacy conormal-splitting route is no longer used, as recorded above.

5. Audited the DAG node statements, proof steps, dependencies and origins
against the Lean declarations. The core node records the matrix, unramified,
flatness and assembly route; the two new nodes record their corresponding
open holes and unit/chapter. Verdict: the delivery is consistent.

I changed only this report by adding this second-reading record; no Lean
statements or proofs were changed during review.
