## Worker report

The module `Sheaf.RingTheory.QuasiFiniteAtPrimePermanence` states
`Algebra.IsQuasiFiniteAtPrime.of_restrictScalars`, with proof `sorry`.
No definitions, dependency modules, new nodes, or statement corrections are needed.

Hypothesis and clause matching:
- Commutative rings A, B, C: three type binders in independent explicit universes
  `u v w`, and `[CommRing A] [CommRing B] [CommRing C]`.
- Ring maps A → B and B → C, and their composite A → C:
  `[Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]`.
  Algebras over commutative rings encode arbitrary unital ring maps; the scalar
  tower imposes exactly compatibility of the third map with the composite.
- A → C of finite type: `[FiniteType A C]`.
- The parenthetical consequence B → C of finite type: the explicit proof term
  `FiniteType.of_restrictScalars_finiteType A B C` supplies the finite-type argument
  of the conclusion's predicate. This is derived, never an added hypothesis.
- Prime ideal r of C: `r : PrimeSpectrum C`, including primality in the bundled point.
- A → C quasi-finite at r: `hr : IsQuasiFiniteAtPrime A C r`.
- B → C quasi-finite at the same r: `@IsQuasiFiniteAtPrime B C _ _ _
  (FiniteType.of_restrictScalars_finiteType A B C) r`.
  This is the recorded isolated-fibre-point predicate, not Mathlib's different
  localization-based `Algebra.QuasiFiniteAt`.

Dependency declarations read and used:
- `Mathlib.RingTheory.FiniteType`, `Algebra.FiniteType`: finitely generated top
  subalgebra, exactly the finite algebra generator condition. Also uses its
  `Algebra.FiniteType.of_restrictScalars_finiteType` to supply the conclusion's
  finite-type instance.
- `Sheaf.RingTheory.QuasiFiniteAtPrime`, `Algebra.IsQuasiFiniteAtPrime`: its full
  definition takes finite type as an instance and tests openness of the singleton
  of the corresponding prime of the fibre ring, via
  `PrimeSpectrum.preimageHomeomorphFiber`. This module imports the finite-type module,
  so no redundant import is needed.

Source verification: the local `literature/stacks-project/algebra.tex` is absent on
this machine. Read https://stacks.math.columbia.edu/tag/0C6H instead: Lemma 10.122.10
has exactly these assumptions and conclusion; its proof first notes finite type over B.
The declaration docstring carries all four steps of the node's proof, including its
fibre-ring comparison argument and the node references used at each step.

Edge cases checked before writing: no injectivity, domains, nontriviality,
Noetherianity, finite type of B over A, or finiteness assumptions are imposed.
If C is the zero ring, there is no prime r and the statement is vacuous. A zero
source ring mapping unitally to C also forces C zero. Identity maps and arbitrary
intermediate rings are allowed. The three rings can lie in unrelated universes;
there is no quantification over a smaller universe of test rings. Finite algebra
generators may be empty. The derived finite-type proof does not change the predicate,
since finite type is Prop-valued and proofs are irrelevant.

Searches (2026-10-11):
- msearch leansearch, query `quasi finite at prime descends intermediate algebra tower
  finite type`: unavailable, Internal Server Error.
- msearch leanfinder, query `A to B to C finite type A algebra C isolated point of fibre
  at prime implies isolated point over B`: eight hits, including discrete/finiteness
  of whole fibres, `PrimeSpectrum.preimageEquivFiber`, and fibre prime comparison;
  no theorem for the recorded predicate.
- msearch loogle, query `Algebra.QuasiFiniteAt, IsScalarTower`: three hits, concerning
  surjectivity on stalks, residue fields and fibre lift surjectivity, no exact match.
- msearch grep, query `of_restrictScalars|QuasiFiniteAt.of_` in
  `RingTheory/QuasiFinite`: whole-map `Algebra.QuasiFinite.of_restrictScalars` and
  `WeaklyQuasiFiniteAt.of_restrictScalars`, not the isolated-point predicate.
- rg on `lean/Sheaf` and upstream `WeilConjectures` for `QuasiFiniteAt` and
  `IsQuasiFiniteAtPrime`: read the existing predicate and its consumers; no permanence
  theorem. Target-id grep in upstream returned no hits. Name search for
  `IsQuasiFiniteAtPrime.*restrict|isQuasiFiniteAtPrime.*restrict` in both libraries
  and `dag/lean_names_upstream.json` returned no hits.
- Read Mathlib `FiniteType.lean` lines 38–40 and 74–83: the finite-type definition
  and its intermediate-algebra permanence theorem are usable directly.

No node fault or disputed statement found.

## Second reading by M1

Independently read the item node, its four proof steps, the delivered Lean module,
both statement-dependency nodes, and the declarations those nodes record.
The statement is unchanged and has no `statement_change`; there are no new nodes
or dependency modules to review.

Source: the local Stacks checkout is absent. Read the actual `algebra.tex` from
https://raw.githubusercontent.com/stacks/stacks-project/master/algebra.tex,
including `section-quasi-finite`, `lemma-quasi-finite-permanence`, and
`definition-quasi-finite`. Also checked the tagged pages
https://stacks.math.columbia.edu/tag/0C6H,
https://stacks.math.columbia.edu/tag/00PL, and
https://stacks.math.columbia.edu/tag/00PK. The section assumes finite-type ring
maps, not Noetherian rings or fields. The source's primes p and q are uniquely
determined contractions of r, so need no additional binders.

Node objects, hypotheses, and conclusions, matched individually:
- Arbitrary commutative rings A, B, C: `{A : Type u} {B : Type v} {C : Type w}`
  and `[CommRing A] [CommRing B] [CommRing C]`. Exact; no domain or nonzero assumption.
- Unital maps A → B and B → C: `[Algebra A B] [Algebra B C]`.
  Over commutative rings, algebra structures encode arbitrary such maps. Exact.
- Their composite A → C: `[Algebra A C] [IsScalarTower A B C]`.
  The scalar tower identifies its algebra map with the composite, without adding
  restrictions on the two given maps. Exact.
- Composite of finite type: `[FiniteType A C]`. Read `Algebra.FiniteType` in
  `Mathlib.RingTheory.FiniteType`: `(⊤ : Subalgebra A C).FG` is exactly finite
  algebra generation as in `def-weil-pbc-finite-type-algebra`. Exact.
- Parenthetical consequence B → C of finite type: the conclusion supplies
  `FiniteType.of_restrictScalars_finiteType A B C` explicitly. Read that theorem's
  full signature and proof: it needs only the displayed tower and finite type
  over A. This is a derived consequence, not an extra instance hypothesis. Exact.
- Prime ideal r of C: `(r : PrimeSpectrum C)` bundles the ideal and its primality.
  It ranges over every prime, not a chosen maximal ideal. Exact.
- A → C quasi-finite at r: `(hr : IsQuasiFiniteAtPrime A C r)`.
  Opened `Sheaf.RingTheory.QuasiFiniteAtPrime` and checked its definition: it
  contracts r by `algebraMap`, uses `PrimeSpectrum.preimageHomeomorphFiber` to
  select the corresponding fibre prime, and requires its singleton to be open.
  Read Mathlib's homeomorphism, its underlying `preimageEquivFiber`, and the
  inverse given by contraction along `TensorProduct.includeRight`; hence this
  is precisely the prime over r specified by the dependency node. Exact.
- B → C quasi-finite at the same r: `@IsQuasiFiniteAtPrime B C _ _ _
  (FiniteType.of_restrictScalars_finiteType A B C) r`. It uses the same recorded
  predicate with the B-algebra map and its own contracted prime. Exact, with
  quantifiers and implication in the node's order. The finite-type proof is
  Prop-valued and cannot alter the meaning of this predicate.

Edge cases: independent universes u, v, w are all explicitly bound; no test-ring
universe restriction occurs. Zero C has no prime r, so is correctly vacuous.
Zero A or B mapping unitally to C forces C zero; these cases are not excluded.
Empty sets of algebra generators (n = 0), identity maps, arbitrary intermediate
rings, and every characteristic are admitted. There is no scheme, module, or
independent index set here; empty spectra are covered by the prime binder.

Independent duplicate searches, using different words from the worker:
- msearch LeanSearch `isolated fiber point remains isolated intermediate base ring`:
  service unavailable (Internal Server Error); no verdict inferred from failure.
- msearch Loogle `IsOpen, PrimeSpectrum.comap`: three hits, namely
  `Polynomial.isOpen_image_comap_of_monic`,
  `Algebra.QuasiFiniteAt.of_isOpen_singleton_fiber`, and
  `Algebra.quasiFiniteAt_iff_isOpen_singleton_fiber`. None is tower permanence.
  Opened the latter two in `Mathlib.RingTheory.ZariskisMainTheorem`: they concern
  the localization-based predicate and its equivalence with subspace openness.
- rg over Mathlib/RingTheory, upstream WeilConjectures, and project lean/Sheaf
  for `IsQuasiFiniteAtPrime`, `isolated.*(fibre|fiber)`, and pointwise
  `quasiFiniteAt`/`QuasiFiniteAt` with `restrict` or `tower`: no existing theorem
  with this statement. Project hits are the shared definition and its consumers.
  Opened `Algebra.QuasiFiniteAt` in Mathlib: it is quasi-finiteness of the
  localization, not the recorded isolated-point predicate. Thus the whole-map
  restriction theorem is not an exact declaration for this node.
- Exact full-name and blueprint-id search in `dag/lean_names_upstream.json` and
  upstream WeilConjectures returned no hits.

No mismatch found; no Lean or node edits needed. The only change is this appended
review. The module has one theorem with proof `sorry`, no definitions or private
copies, and one used import of the shared predicate. Its module and declaration
docstrings name 0C6H and the blueprint id, and its declaration docstring carries
all four node proof steps: finite type, fibre comparison, uniqueness of the prime,
and continuity giving the open singleton. All variables and universes are bound;
the recorded `lean.statement` matches the file signature verbatim.

Validation: `scompile.py M1 lem-weil-pbc-quasi-finite-at-prime-permanence`
compiled the delivered module cleanly (1.4 s, exit 0, no warnings).
`deliver2.py M1 lem-weil-pbc-quasi-finite-at-prime-permanence --no-push`
printed OK: preflight passed and the module compiled, with nothing pushed.
