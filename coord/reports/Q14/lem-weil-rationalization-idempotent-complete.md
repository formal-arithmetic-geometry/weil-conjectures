## Worker report

The module `Sheaf.Paper.RationalizationIdempotentComplete` states
`WeilConjectures.rationalization_idempotent_complete` with one `sorry` and no definitions.
It states idempotent completeness of the existing raw rationalization and exact equivalence
of its canonical inclusion into Mathlib's Karoubi envelope. No node statement, dependencies,
proof, or proof dependencies changed; only the item's `lean` record is supplied.

The node and both proof steps were read against the source
`sec-six-functors/sk-prop-sf-biduality-general/lem-weil-rationalization-idempotent-complete.md`,
order 2114, and the enclosing unit's `_section.md`, order 2113. The source files are available
in the launcher's literature mirror (the shared clone omits untracked literature).
The reviewed node already makes the finite-field and finite-type setting explicit; this
worker makes no further correction. The proof docstring follows exactly the node's two-step
bounded-t-structure route. No identification with the separate PBC coefficient category is
used.

Hypotheses and conclusions, clause by clause:

| Node clause | Lean rendering |
| --- | --- |
| Finite-field datum p,a,q,k₀,k; p prime, a≥1, q=p^a, k₀ of cardinality q, k its fixed algebraic closure | `(D : FiniteFieldDatum.{u})`; its recorded fields `prime`, `exponent_pos`, `cardinality_eq`, `card_base`, and `isAlgClosure` impose exactly these conditions. |
| Prime ℓ distinct from p | `(l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)` |
| A fixed algebraic closure Qbar of Q_l | `(Qbar : Type v) [Field Qbar] [Algebra (Padic l) Qbar] [IsAlgClosure (Padic l) Qbar]` |
| A finite extension E/Q_l contained in Qbar | `(E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (_ι : E →ₐ[Padic l] Qbar)`. A field algebra homomorphism is automatically injective; it records the specified embedding, without adding an arbitrary extra coefficient map. |
| Valuation ring O_E | The category's existing definition uses `Padic.coefficientExtensionIntegers l E`, its spectral-absolute-value valuation ring, and its recorded uniformizer. No independent ring or uniformizer is introduced. |
| Y a k-scheme | `(Y : AlgebraicGeometry.Scheme.{u}) [Y.Over (Spec (CommRingCat.of D.k))]` |
| Y of finite type over k | `[LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of D.k))] [QuasiCompact (Y ↘ Spec (CommRingCat.of D.k))]`, precisely the dependency's conjunction. No separatedness assumption is added. |
| D^b_c(Y,E) the raw rationalized category | `rationalConstructibleCategory D l hl E Y`, from the recorded dependency; its objects are the integral objects and its Homs are scalar-localized, with the tensor-E identification. |
| D^b_c(Y,E) is idempotent complete | `IsIdempotentComplete (rationalConstructibleCategory D l hl E Y)`, whose Mathlib field splits every idempotent. |
| The canonical functor to its Karoubi envelope is an equivalence | `(toKaroubi (rationalConstructibleCategory D l hl E Y)).IsEquivalence` |
| That equivalence is exact | `(toKaroubi (rationalConstructibleCategory D l hl E Y)).IsTriangulated`, for the existing raw shift/triangles and the canonical Karoubi shift/retract triangles. |

Dependency declarations read and used:

- `Sheaf.Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum`; its full structure and
  instance attributes were read. This supplies the datum, not a private bundled replacement.
- `Mathlib.FieldTheory.IsAlgClosed.Basic` (through the recorded AlgebraicClosure module):
  `IsAlgClosure`, expressing algebraic and algebraically closed extension, exactly the
  `mathlib_match.how` of `def-weil-algebraic-closure`.
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`: the recorded theorem
  `Padic.finite_coefficientExtensionRing` and its public import of
  `Sheaf.NumberTheory.Padics.CoefficientExtension`. That latter module's complete definitions
  `Padic.coefficientExtensionIntegers` and `Padic.coefficientExtensionUniformizer` are used
  through the rational category; the finite-dimensional field extension is their hypothesis.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType` and `...QuasiCompact`:
  `AlgebraicGeometry.LocallyOfFiniteType`, `AlgebraicGeometry.QuasiCompact`; both full class
  signatures and docstrings were read, as well as the node's recorded conjunction convention.
- `Sheaf.Paper.RationalizationKaroubi`: `WeilConjectures.rationalConstructibleCategory`,
  `rationalConstructibleShift`, `rationalConstructibleShiftAdditive`,
  `rationalConstructibleZero`, `rationalConstructiblePretriangulated`, and
  `rationalConstructibleTriangulated`. The complete module was also checked via
  `scompile.py --source Sheaf.Paper.RationalizationKaroubi` against the server.
- `Mathlib.CategoryTheory.Idempotents.Karoubi`: `CategoryTheory.Idempotents.Karoubi`, its
  `Hom`, category structure, and `CategoryTheory.Idempotents.toKaroubi`, read in full.
  The latter has object map K ↦ (K,id_K) and unchanged underlying morphisms.
- `WeilConjectures.CategoryTheory.Idempotents.Pretriangulated`: canonical Karoubi shift and
  pretriangulation and `CategoryTheory.Idempotents.toKaroubi.isTriangulated` used to type
  exactness. `Mathlib.CategoryTheory.Idempotents.Basic.IsIdempotentComplete` is reused.
- Proof-only import `WeilConjectures.CategoryTheory.Idempotents.TStructure`: the recorded
  `CategoryTheory.Triangulated.TStructure.isEquivalence_toKaroubi_and_isTriangulated_of_bounded`
  and its public dependency
  `CategoryTheory.Triangulated.TStructure.isIdempotentComplete_of_bounded`. Their signatures,
  including all surrounding category/shift/triangulation hypotheses, were read. The other
  proof input `prop-constructible-truncations` currently has no recorded Lean module, so its
  proof-only import remains for stage 3; it is not a notion needed to type this statement.

Edge cases checked before drafting: the empty finite-type scheme is permitted; zero objects
and both zero and identity idempotents are covered by the universal Mathlib splitting
predicate; no nonempty scheme or nonzero-object hypothesis appears. The base finite extension
E=Q_l is included with its canonical embedding into Qbar. Every prime ℓ≠p is allowed,
including ℓ=2 where applicable. A finite-type nonseparated scheme remains included. The
coefficient closure has independent universe `v`; the scheme, base datum, and integral
coefficient type use the existing category interface's common ambient universe `u`, which
can be taken arbitrarily large. All variables and universes are explicitly bound, with
`autoImplicit false`; no local notation or private interface is introduced.

Searches for an existing statement (actual msearch calls are recorded in `searches.jsonl`):

- LeanSearch: “The raw rationalized constructible derived category is idempotent complete and
  the inclusion into its Karoubi envelope is an exact equivalence” — service returned Internal
  Server Error; unavailable, hence no absence conclusion is drawn from it.
- LeanFinder: “The raw rationalized bounded constructible derived category of a finite type
  scheme over an algebraic closure of a finite field is idempotent complete and its canonical
  functor to the Karoubi envelope is an exact equivalence” — eight hits, on Karoubi envelopes
  of complex categories and ordinary derived-category representatives. None is this theorem.
- Loogle: `CategoryTheory.IsIdempotentComplete, CategoryTheory.Idempotents.toKaroubi` — four
  hits, including the generic `toKaroubi_isEquivalence` conditional on idempotent completeness;
  none establishes the raw constructible rationalization's completeness.
- msearch grep, correctly rooted at `CategoryTheory/Idempotents`:
  `rational.*[Ii]dempotent|[Ii]dempotent.*rational|toKaroubi|IsIdempotentComplete` — 25 displayed
  hits, general Karoubi infrastructure and complexes; no exact statement.
- `rg` over upstream `WeilConjectures`, shared `lean/Sheaf`, and the upstream-name index for
  `rationalization.*[Ii]dempotent|[Ii]dempotent.*rationalization|rationalConstructibleCategory|rationalization_idempotent_complete`
  found the published raw category and coefficient extension modules, not this theorem.
  `grep -rn 'lem-weil-rationalization-idempotent-complete'` over upstream source found no hit.
  Older upstream `ClosedImmersionStages` uses a formally Karoubi-completed rational stage;
  it does not give the raw category statement and is not substituted for it.

Validation: `scompile.py Q14 lem-weil-rationalization-idempotent-complete` compiled the draft
in both sandbox and library positions cleanly, under the prescribed 60-second per-file
limit. The final dry run below recompiles the delivered file and runs server preflight.
No statement dispute, dependency repair, new node, or node correction is needed.

## Second reading by Q14

I independently read the reviewed DAG node, the entire sandbox module, all six statement
 dependency records, and the declarations below. I also read the blueprint source lemma
(order 2114) and its enclosing `_section.md` (order 2113) directly from the server literature
mirror. This item is sourced to the blueprint, not a Stacks lemma. The source's final
bounded-t-structure argument is the route recorded by the reviewed node. The node already
exposes its finite-field and finite-type setting; this delivery makes no further statement
correction. The enclosing unit's separatedness is not added to this already reviewed lemma.

My statement checklist, written independently before comparing the signature:

| Object, hypothesis, or conclusion in the node | Actual Lean and verdict |
| --- | --- |
| Fixed prime p, positive exponent a, q=p^a, finite field k0 of size q, fixed algebraic closure k/k0 | `D : FiniteFieldDatum.{u}`. I opened `FiniteFieldFiber.lean`: `prime`, `exponent_pos`, `cardinality_eq`, `finite_base`, `card_base`, and `isAlgClosure` give precisely these data. PASS. |
| Prime ell different from p | `l : ℕ`, `[Fact l.Prime]`, `hl : l ≠ D.p`. No further restriction on ell. PASS. |
| Fixed algebraic closure Qbar of Q_l | `Qbar : Type v`, `[Field Qbar]`, `[Algebra (Padic l) Qbar]`, `[IsAlgClosure (Padic l) Qbar]`. I read `IsAlgClosure` in Basic.lean: algebraically closed and algebraic over the base. This is explicitly included in the dependency's `mathlib_match.how`. PASS. |
| Finite field extension E/Q_l inside that closure | `E : Type u`, field and algebra instances, `[FiniteDimensional (Padic l) E]`, `_ι : E →ₐ[Padic l] Qbar`. An algebra homomorphism between fields is injective, so this records an embedded finite extension; no surjectivity or normality is required. PASS. |
| Its actual valuation ring O_E | `rationalConstructibleCategory` uses `Padic.coefficientExtensionIntegers l E` and `Padic.coefficientExtensionUniformizer l E`. I opened the coefficient module: the former is the subring of elements of spectral extension absolute value at most one; the latter is the recorded DVR uniformizer. They are not extra arbitrary parameters. PASS. |
| Scheme Y with its k-structure | `Y : Scheme.{u}`, `[Y.Over (Spec (CommRingCat.of D.k))]`. This binds a structure morphism without requiring descent to k0 or geometric nonemptiness. PASS. |
| Finite type over k | `[LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of D.k))]` and `[QuasiCompact (Y ↘ Spec (CommRingCat.of D.k))]`. I read both Mathlib classes and the dependency's conjunction convention. No extra separatedness, smoothness, properness, or explicit Noetherian instance is assumed. PASS. |
| D^b_c(Y,E) is the raw rationalization of the integral category | `rationalConstructibleCategory D l hl E Y`. Its dependency is an abbreviation for `ScalarLocalization (Padic.coefficientExtensionIntegers l E) (boundedConstructibleDerivedCompleteIntegralCategory D l hl E Y) (Padic.coefficientExtensionUniformizer l E)`. It is not a Karoubi envelope or the separate PBC category. PASS. |
| Every idempotent in that category splits | `IsIdempotentComplete (rationalConstructibleCategory D l hl E Y)`. I opened the class: it quantifies over each object and idempotent and asks for a section and retraction with both equations. PASS. |
| The functor is specifically the canonical inclusion into Karoubi | `toKaroubi (rationalConstructibleCategory D l hl E Y)`. I read the object map `(X,𝟙 X)`, unchanged underlying morphism map, and Karoubi Hom/category definitions. PASS. |
| That functor is an equivalence | Its `.IsEquivalence` conjunct; neither an arbitrary equivalence nor only full faithfulness. PASS. |
| That equivalence is exact | Its `.IsTriangulated` conjunct uses the imported canonical commutation with shift and retract-triangle pretriangulation of Karoubi. I read `toKaroubi.isTriangulated` in the upstream Pretriangulated module and the exact bounded-t theorem in TStructure. PASS. |

All data are universally quantified before the three conclusions, in the node's order.
`Qbar` and `_ι` remain explicit binders even though the abstract category is independent
of the chosen embedding. The shared universe `u` is the published rational-category
interface for the scheme and coefficient type and the scheme-over-k interface for the base;
it ranges over arbitrarily large universes. The closure's universe `v` is independent.
No unbound variable or implicit universe was found. In particular no test-algebra binder
with a too-small independent universe is present.

Edge cases: empty finite-type Y is included, and no inhabitance or nonzero hypothesis is
present. The zero object, zero projector, and identity projector all lie under the same
universal splitting predicate. E=Q_l, degree one, and ell=2 when different from p are
included. The prime and positive-a assumptions exclude exactly the invalid finite-field
data. There is no index set, finite-level n, or dimension bound in this theorem; it does
not accidentally impose a positive-level or positive-dimension condition.

Independent H4 searches (recorded by msearch in searches.jsonl):

- LeanFinder: “Splitting projectors in the scalar localization of bounded constructible
  adic complexes; the identity-projector embedding into the Karoubi category is an exact
  equivalence”. Eight hits, about Karoubi envelopes of homological complexes and their
  chain-complex variants, not this scalar-localized constructible category.
- Loogle: `CategoryTheory.Idempotents.toKaroubi, CategoryTheory.Functor.IsEquivalence`.
  Two hits: generic `toKaroubi_isEquivalence`, conditional on idempotent completeness,
  and a functor-extension equivalence. Neither supplies this category's completeness.
- msearch grep in `CategoryTheory/Idempotents`:
  `projector|split.*idempotent|karoubian|isIdempotentComplete`. The 25 displayed hits
  concern generic splitting, functor categories, complexes, and Karoubi itself.
- Independent `rg` in the project's `lean/Sheaf/Paper`, upstream
  `WeilConjectures/CategoryTheory/Idempotents`, and its derived-complete coefficient
  directory, using `split.*(projector|idempotent)|karoubian|isIdempotentComplete|toKaroubi`,
  found the abstract bounded-t result and canonical Karoubi infrastructure, not this
  theorem. The raw category is already declared by its recorded dependency and is reused.
  The worker's LeanSearch service failure is retained as unavailable, not absence evidence.

H5/H6/H8/H9: this delivery contains one named theorem with exactly one `sorry`, and no
new definition, instance, axiom, private copy, notation, or proof. The declaration and module
both identify source order 2114 and the exact blueprint id. The proof docstring follows
the two node steps: the rational-stage truncation theorem supplies a bounded t-structure
on this same raw category, then the bounded-t Karoubian theorem splits idempotents and
gives exact equivalence of the canonical inclusion. The latter is imported as a proof
 dependency. `prop-constructible-truncations` still has no recorded module to import.
There are no new nodes or dependency modules in this delivery to audit under H12/H13.

Mismatches found: none in the statement or its dependencies. I preserved the Lean module,
node statement, dependencies, and proof unchanged, and added this independent reading and
search record. The node's `lean.statement` is byte-for-byte the theorem signature before
`:=`. Compilation uses only the prescribed scompile wrapper; delivery dry run and final
preflight provide the final validation below.

Second-reader validation: scompile compiled the exact file cleanly in sandbox and library
positions. The deliver2 `--no-push` dry run printed OK: compilation and current server
stage-2 preflight passed, with no warnings. The report-only second-reading additions do
not change the checked Lean signature.
