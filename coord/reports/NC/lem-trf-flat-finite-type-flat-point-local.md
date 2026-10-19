## Worker report

The module `Sheaf.TraceFormula.FlatFiniteTypeFlatPointLocal` states
`Module.finitePresentation_localizedModule_atPrime_of_flat`. It formalizes Tag 05I7
for an affine ring map: `A` and `B` are commutative rings, `Algebra A B` carries the
map, `[Algebra.FinitePresentation A B]` is the finitely presented algebra hypothesis,
`N` is an additive commutative group with a `B`-module structure and
`[Module.Finite B N]` is finite type, and `q : Ideal B` with `[q.IsPrime]` is the
chosen prime. The flatness hypothesis is explicitly
`@Module.Flat A (LocalizedModule q.primeCompl N) _ _
(Module.compHom (LocalizedModule q.primeCompl N) (algebraMap A B))`, so it is exactly
flatness of the localized module at `q` as an `A`-module. The conclusion is
`Module.FinitePresentation (Localization.AtPrime q)
(LocalizedModule q.primeCompl N)`, finite presentation over `B_q`.
The theorem proof is `sorry`, as required at stage 2.

The explicit universes `u`, `v`, and `w` keep the base ring, target algebra, and module
independent. No Noetherian, nonzero, domain, nonempty-spectrum, or separation hypothesis
was added. The zero ring, zero module, and arbitrary prime (when one exists) are allowed;
`q.primeCompl` is the canonical localization complement and the target module structure
is Mathlib's canonical localized-module structure. The affine translation in the source
identifies `N_q` with this `LocalizedModule` and `B_q` with `Localization.AtPrime q`.

Dependencies used for the corrected statement are all existing Mathlib notions:

- `def-weil-pbc-finitely-presented-algebra`: `Algebra.FinitePresentation` in
  `Mathlib.RingTheory.FinitePresentation`.
- `def-weil-finitely-generated-module`: `Module.Finite B N` in
  `Mathlib.RingTheory.Finiteness.Defs`. The old citation to the finite-type algebra
  node was incorrect: polynomial generation is a different notion.
- `def-weil-pbc-flat-ring-map`: `Module.Flat` and `RingHom.Flat` in
  `Mathlib.RingTheory.Flat.Basic` and `Mathlib.RingTheory.RingHom.Flat`.
- `def-sc-finitely-presented-module`: `Module.FinitePresentation` in
  `Mathlib.Algebra.Module.FinitePresentation`, recorded in this delivery. The old
  citation describes sheaves on ringed spaces, rather than ordinary modules.
- `def-weil-pbc-localization-at-prime`: `Localization.AtPrime` in
  `Mathlib.RingTheory.Localization.AtPrime.Basic` and the canonical
  `LocalizedModule` construction in `Mathlib.Algebra.Module.LocalizedModule.AtPrime`.

Source check: the statement and the three proof paragraphs were read in
`literature/stacks-project/flat.tex`, Tag 05I7 (`lemma-finite-type-flat-at-point-local`),
with Tag 05I6 supplying the etale-neighborhood argument and Tag 03C4(2) the faithful-flat
descent. The affine objects in the proof are `Spec B`, `Spec A`, the sheaf associated to
`N`, and the point `q`; the resulting stalk and local ring are exactly the two Mathlib
localizations in the conclusion.

Searches made:

- `msearch.py NC lem-trf-flat-finite-type-flat-point-local leanfinder "finite type flat module at prime finitely presented localized module"`: hits included `instFlatAtPrime`, `Module.flat_of_localized_maximal`, `RingHom.Flat.ofLocalizationPrime`, and `instFinitePresentationLocalizationLocalizedModule`; none states the Tag 05I7 theorem.
- `msearch.py NC lem-trf-flat-finite-type-flat-point-local loogle "Module.FinitePresentation LocalizedModule Module.Flat"`: no hits (the query also reports the expected polymorphic-application mismatch for `LocalizedModule`).
- `msearch.py NC lem-trf-flat-finite-type-flat-point-local grep "flat.*finite.*presentation.*prime" Mathlib/RingTheory`: no hits.
- The node's recorded LeanFinder, LeanSearch, Loogle, and grep searches were re-read; they likewise found only component localization and finite-presentation declarations, with no exact stalk theorem.
- `rg` over `WeilConjectures/` and shared `lean/Sheaf` found no declaration with this node id or an equivalent theorem; the only related declaration is the separate flat-localization helper `Module.Flat.localizedModule_atPrime_of_flat`.

No Mathlib or project declaration states this theorem exactly, so a new module is
provided and retained unchanged from the returned packet. The repair corrects only
definition citations and records the existing ordinary-module prerequisite; it adds no
Lean definition, theorem, or module. There is no `STATEMENT-DISPUTED` issue.


## Dependency modules

`def-sc-finitely-presented-module` already exists, has status `mathlib`, and records
`Module.FinitePresentation` in `mathlib_match`, but had no `lean` field. The packet
adds only its `lean` record, with `existing: true`, branch `mathlib`, module
`Mathlib.Algebra.Module.FinitePresentation`, and a note explaining its role. No
module is introduced. The existing source class at lines 67-69 requires a finite
set of generators with finitely generated kernel. The source theorem
`Module.FinitePresentation.exists_fin'` at lines 95-99 explicitly produces a
surjective map `A^n → M` and a map `A^m → A^n` exact at `A^n`; conversely such a
sequence gives a finitely generated kernel (the image of the finite free module),
as used by `Module.finitePresentation_of_free_of_surjective`. This is exactly the
node's finite free presentation, including zero generators and relations.
The pre-existing match is usable and is retained verbatim; no new node is needed.

Repair search: `msearch.py ... loogle "Module.FinitePresentation"` returned 12 hits,
including the class in `Mathlib.Algebra.Module.FinitePresentation`, its zero-module
instance, and its finite/free consequences. Reading the class and `exists_fin'`
confirmed the exact ordinary-module notion; no alternate sheaf notion was used.
The existing finite-module node `def-weil-finitely-generated-module` already binds
`Module.Finite`, so no copy or modification of that dependency is delivered.

## Statement corrected

The old statement, verbatim, was:

Let $A\to B$ be a finitely presented homomorphism of commutative rings [def-weil-pbc-finitely-presented-algebra], let $N$ be a finite $B$-module [def-weil-pbc-finite-type-algebra], and let $\mathfrak q$ be a prime of $B$ [def-weil-pbc-localization-at-prime]. If the localization $N_{\mathfrak q}$ is flat as an $A$-module [def-weil-pbc-flat-ring-map], then $N_{\mathfrak q}$ is a finitely presented $B_{\mathfrak q}$-module [def-weil-pbc-module-finite-type-presentation].

The hypothesis's `[def-weil-pbc-finite-type-algebra]` is replaced with
`[def-weil-finitely-generated-module]`; the conclusion's
`[def-weil-pbc-module-finite-type-presentation]` is replaced with
`[def-sc-finitely-presented-module]`. Those are the only changes to the statement.
The statement-dependency list makes the same replacements. The proof and its
proof-dependency list remain unchanged: their sheaf finite-presentation citation
is appropriate in the geometric proof. The source remains Stacks Tag 05I7,
`flat.tex`, `lemma-finite-type-flat-at-point-local`, affine translation. This is a
correction of definition references, without any change to the source theorem's
hypotheses or conclusion. `statement_change` records the old statement and old
statement-dependency list.

Citer audit: an exact-id search across all node JSON files, followed by filtering
`stmt_deps` and `proof_deps`, finds exactly one citer:

- `lem-trf-flat-finite-type-dense-presentation`: holds. Its Tag 081N proof applies
  precisely this affine theorem to deduce finite presentation of `N_q` from
  `A`-flatness; the theorem is unchanged. Other exact-id hits are provenance or
  descriptive text, not dependency edges. No citer is edited.

## Second reading by NC

This is the repair worker's direct self-check, not a claim of an independent
second agent. I reopened the node, its dependency records, the delivered Lean
file, and Stacks Tag 05I7. The maintainer's return had already accepted the
Lean theorem and its compilation. The saved node and current shared main differ
only by the saved `lean` field; the repaired node is rebuilt from current main,
retaining the delivered theorem. The delivery wrapper rebases the packet on the
current published `newtargets-dag`.

Clause-by-clause check:

- Commutative rings `A, B` are `{A : Type u} {B : Type v}` with `[CommRing A]`
  and `[CommRing B]`; `[Algebra A B]` gives exactly the ring map via `algebraMap`.
- Finite presentation of this map is `[Algebra.FinitePresentation A B]`, the
  recorded algebra notion; its source definition is a polynomial quotient by a
  finitely generated ideal. It is distinct from finite presentation of a module.
- An ordinary `B`-module is `{N : Type w} [AddCommGroup N] [Module B N]`.
  Its finite generation is exactly `[Module.Finite B N]`, matching the corrected
  `def-weil-finitely-generated-module` citation. No finite underlying set is assumed.
- A prime of `B` is `(q : Ideal B) [q.IsPrime]`; `q.primeCompl` is its multiplicative
  complement. `LocalizedModule q.primeCompl N` represents the stalk `N_q`, and
  `Localization.AtPrime q` is `B_q`, both canonical Mathlib constructions.
- The sole additional hypothesis `hflat` is `Module.Flat` on that localized module,
  with its `A`-module structure explicitly restricted along `algebraMap A B` by
  `Module.compHom`. There is no independent or arbitrary action on the stalk.
- The sole conclusion is `Module.FinitePresentation (Localization.AtPrime q)
  (LocalizedModule q.primeCompl N)`, using the canonical localized-ring action.
  This matches the corrected ordinary finitely presented module dependency.
- The source applies to `Spec B → Spec A` and the quasi-coherent sheaf associated
  to `N`. Finite generation makes that sheaf finite type, and `A`-flatness of its
  stalk gives flatness over the corresponding base local ring; the source's
  local-ring conclusion is exactly this ordinary localized-module conclusion.

Edge cases: zero modules have the empty presentation; no positivity of ranks is
assumed. Zero `B` has no prime ideal, so the prime-quantified assertion has no
instance in that case, as in the source. Zero `A`, or an arbitrary non-Noetherian
base and arbitrary prime when these data exist, are not excluded. All three
universes are explicitly declared and independent. Both auto-implicit options
are disabled. The only theorem proof remains `sorry`; there is no data definition.

Return repair checklist: (1) the finite-module hypothesis now cites the existing
finite-generation node; (2) the conclusion now cites ordinary finite presentation;
(3) that existing prerequisite's exact Mathlib declaration is recorded in this
same packet, without modifying its mathematical statement or match; (4) this
concrete source-and-signature reading replaces the placeholder second reading.
