## Worker report

The module `lean/Sheaf/Paper/QbarIdempotentComplete.lean` states
`WeilConjectures.qbar_idempotent_complete`. It uses the corrected node scope: a
finite-type `k`-scheme `Y` over the fixed global finite-field datum. Its conclusion
is that the raw common-stage category
`generalAlgebraicallyClosedConstructibleCategory l Qbar Y` is
`IsIdempotentComplete`, and that Mathlib's canonical
`CategoryTheory.Idempotents.toKaroubi` functor on this category is both an
 equivalence and triangulated (the exact-equivalence assertion).

The Lean binders render the statement clauses as follows. `D : FiniteFieldDatum.{u}`
fixes `(p,a,q,k₀,k)`; `l : ℕ` with `[Fact l.Prime]` and `hl : l ≠ D.p` render
`ell ≠ p`; `Qbar : Type v` with `[Field Qbar]`, `[Algebra (Padic l) Qbar]`, and
`[IsAlgClosure (Padic l) Qbar]` renders the chosen algebraic closure. The scheme
`Y : AlgebraicGeometry.Scheme.{u}` and `[Y.Over (Spec (CommRingCat.of D.k))]`
give the `k`-scheme structure. The binders
`[LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of D.k))]` and
`[QuasiCompact (Y ↘ Spec (CommRingCat.of D.k))]` render finite type using the
recorded Mathlib interface. The category is the published declaration
`WeilConjectures.generalAlgebraicallyClosedConstructibleCategory`; the first
conclusion is `IsIdempotentComplete ...`; the two clauses about the canonical
functor are `(toKaroubi ...).IsEquivalence` and `(toKaroubi ...).IsTriangulated`.

Statement dependencies used: `def-weil-finite-field-fiber` via
`Sheaf.Paper.FiniteFieldFiber`, declaration `WeilConjectures.FiniteFieldDatum`;
`def-weil-algebraically-closed-coefficients` via
`Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients`, declaration
`WeilConjectures.generalAlgebraicallyClosedConstructibleCategory` and its
`GeneralAlgebraicallyClosedCoefficients.Pair` construction;
`def-weil-rationalization-karoubi` via `Sheaf.Paper.RationalizationKaroubi`,
declaration `WeilConjectures.rationalConstructibleCategory`;
`def-weil-karoubi-envelope` via Mathlib's
`CategoryTheory.Idempotents.Karoubi`; `def-weil-triangulated-category` via
Mathlib's `CategoryTheory.Pretriangulated`/`CategoryTheory.IsTriangulated`; and
`def-weil-finite-type-morphism` via Mathlib's
`AlgebraicGeometry.LocallyOfFiniteType` and `AlgebraicGeometry.QuasiCompact`.
The proof-plan imports are `WeilConjectures.rationalization_idempotent_complete`
from `Sheaf.Paper.RationalizationIdempotentComplete` and the published
Karoubi triangulation framework from
`WeilConjectures.CategoryTheory.Idempotents.Triangulated`.

Edge cases checked against the statement and definitions: the global datum may
have any allowed prime `p` and exponent; `l ≠ p` is retained explicitly; `Y` may
be empty; no nonemptiness or positive-dimensional assumption is added; zero and
identity idempotents are included by `IsIdempotentComplete`; `Qbar` has an
independent universe `v`; and the category is the raw pair category, with no
Karoubi completion hidden in its definition. The finite-type hypotheses are
exactly the two recorded Mathlib classes and impose no separatedness assumption.

Searches for an existing whole-item declaration or definition: `msearch.py`
LeanFinder query “exact equivalence canonical functor common-stage coefficient
category Karoubi envelope” returned only generic Karoubi equivalence and
functor-extension results; no whole-item match. `msearch.py` Loogle query
`CategoryTheory.Idempotents.toKaroubi, CategoryTheory.IsIdempotentComplete,
CategoryTheory.Functor.IsTriangulated` returned no hit (the local generic
results were then inspected). `msearch.py` grep query
`toKaroubi|IsIdempotentComplete|IsTriangulated` in `CategoryTheory/Idempotents`
returned Mathlib Karoubi, simplicial-object and homological-complex declarations,
none for this finite-coefficient common-stage theorem. Direct `rg` searches of
`lean/Sheaf` and the read-only `WeilConjectures` source found no declaration with
this item id or this whole statement. The existing rationalization and PBC
idempotent-completeness theorems are distinct categories and were not reused as
an exact whole-item match.

No new definition nodes or dependency-module repairs were needed. The node
already contains the source-based finite-type scope correction from the retained
review; this delivery changes only its `lean` record. The statement is not marked
`STATEMENT-DISPUTED` because the current node copy already records and explains
that correction.

## Second reading by Q40

The source node is the order-2115 lemma in
`literature/blueprint/master/blueprint/sec-six-functors/sk-prop-sf-biduality-general/lem-weil-qbar-idempotent-complete.md`.
Its objects and clauses, checked against the Lean signature, are:

1. The fixed global finite-field datum is rendered by
   `D : FiniteFieldDatum.{u}`; this supplies `p`, the finite base field, and its
   algebraic closure. Verdict: exact.
2. The coefficient prime `ell` and the hypothesis `ell ≠ p` are rendered by
   `l : ℕ`, `[Fact l.Prime]`, and `hl : l ≠ D.p`. Verdict: exact; no
   characteristic or positivity hypothesis beyond primality is added.
3. The chosen algebraic closure of `Q_l` is rendered by
   `Qbar : Type v`, `[Field Qbar]`, `[Algebra (Padic l) Qbar]`, and
   `[IsAlgClosure (Padic l) Qbar]`. Verdict: exact, with an independent
   closure universe.
4. The finite-type `k`-scheme is rendered by
   `Y : Scheme.{u}`, `[Y.Over (Spec (CommRingCat.of D.k))]`,
   `[LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of D.k))]`, and
   `[QuasiCompact (Y ↘ Spec (CommRingCat.of D.k))]`. Verdict: exact under
   the recorded Mathlib convention; no separatedness or Noetherian assumption
   is added.
5. The common-stage coefficient category is exactly the published
   `generalAlgebraicallyClosedConstructibleCategory l Qbar Y` from
   `def-weil-algebraically-closed-coefficients`; its stages use the recorded
   raw rationalized coefficient category. Verdict: exact; the category is the
   pair/common-stage category and no Karoubi completion is hidden in its
   definition.
6. The first conclusion, idempotent completeness of `C_Y`, is rendered by
   `IsIdempotentComplete (...)`. Verdict: exact.
7. The canonical functor `C_Y → Kar(C_Y)` is Mathlib's
   `toKaroubi (...)`; the remaining conclusion is rendered by
   `.IsEquivalence ∧ .IsTriangulated`. Verdict: exact: these are respectively
   equivalence and exact/triangulated preservation, matching the source's
   “exact equivalence” clause.

Edge cases were checked. The empty scheme and zero object are allowed by the
scheme and category binders; zero and identity idempotents are included by
`IsIdempotentComplete`; no index set or integer `n` is introduced; arbitrary
allowed characteristic `p` and every prime `l ≠ p` remain possible; and the
closure universe `v` is independent of the scheme/data universe `u`.

I re-read the declarations recorded for all six statement dependencies:
`FiniteFieldDatum`, `generalAlgebraicallyClosedConstructibleCategory`, the raw
rationalized stage interface, Mathlib's `Karoubi`/`toKaroubi`, the triangulated
category classes, and `LocallyOfFiniteType`/`QuasiCompact`. The common-stage
module's stages are the intrinsic rationalized interface recorded by the
repaired rationalization node, while its finite-field specialization preserves
the source convention; this does not change the item statement. I also read the
source place and the full proof text, including finite-stage splitting and the
exact Karoubi inclusion argument.

The required searches are recorded in `searches.jsonl`: LeanFinder searches for
the common-stage Karoubi equivalence, Loogle searches for `toKaroubi`,
`IsIdempotentComplete`, and `IsTriangulated`, and repository/Mathlib `rg` searches
for the item and its declaration. They found only generic Karoubi and
functor-extension results, not this theorem. No existing whole-item declaration
was found, so the module is retained. No mismatch was found and no source
statement, dependency, or Lean signature needed changing; the node copy's
`lean.statement` is byte-for-byte the theorem signature. The module compiled via
the required `scompile.py` wrapper with only the expected `sorry` allowance.
