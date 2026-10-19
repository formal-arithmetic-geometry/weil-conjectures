## Worker report

This repairs the returned stage-2 delivery at immutable head `2a5c390df9c7`.
The retained sandbox contained only dispatcher marker files, so the item node was
copied from the current shared DAG. The current node's `split_report` is preserved
verbatim. The delivery wrapper rebases the packet on current `newtargets-dag`.

The new module `Sheaf.RingTheory.AffineDimensionInequality` states
`Ideal.height_add_trdeg_residueField_le`. Its entire proof is `sorry`.
No definitions or additional theorem nodes are needed. I read Stacks Algebra,
Tag 02IJ, label `algebra-lemma-dimension-formula`, in `literature/stacks-project/algebra.tex`,
including its hypotheses, inequality and generator-induction proof. The theorem
states only its inequality clause; the universally-catenary equality is another node.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- Commutative domains R and S: `{R : Type u} {S : Type v}`, `[CommRing R]`,
  `[CommRing S]`, `[IsDomain R]`, `[IsDomain S]`. Universes u and v are independent
  and explicitly declared. The zero ring is excluded exactly by the domain hypotheses.
- Inclusion R ⊆ S: `[Algebra R S]` and
  `(hinj : Function.Injective (algebraMap R S))`. The inclusion is an injective ring
  map, with no unnecessary literal equality of carrier types or universe restriction.
- R Noetherian: `[IsNoetherianRing R]`, the recorded dependency declaration.
  There is no extra Noetherian hypothesis on S; it follows from finite type.
- S a finite type R-algebra: `[Algebra.FiniteType R S]`, the recorded dependency
  declaration, meaning finitely many algebra generators, equivalently a polynomial
  presentation. This imposes no finiteness as an R-module.
- Primes p and q: `(p : Ideal R) (q : Ideal S) [p.IsPrime] [q.IsPrime]`.
- q lies over p: `(hpq : p = q.comap (algebraMap R S))`; comap is precisely
  contraction under the inclusion. No maximality or nonzero-prime condition is imposed.
- Height is the supremum of lengths of strict prime chains ending at the prime:
  `p.height` and `q.height` are Mathlib's `Ideal.height : ℕ∞`.
  `PrimeSpectrum.height_eq_orderHeight` identifies this with chain height for a prime.
- κ(p) = Frac(R/p) and κ(q) = Frac(S/q): `p.ResidueField`, `q.ResidueField`.
  In `Mathlib.RingTheory.LocalRing.ResidueField.Ideal`, the definition at lines 28–34
  is the residue field of the prime localization, and the instance at line 108 is
  `IsFractionRing (R ⧸ I) I.ResidueField`. Thus these are actual fraction fields
  of the stated quotients, with their canonical quotient-algebra structures.
- The specified field extension κ(p) ⊆ κ(q), rather than an arbitrary algebra
  structure, is `(Ideal.ResidueField.map p q (algebraMap R S) hpq).toAlgebra`.
  Its signature and docstring at lines 36–40 state exactly the embedding induced by
  contraction; `map_algebraMap` at lines 43–49 verifies its compatibility with R → S.
  This concrete structure is passed explicitly to `@Algebra.trdeg`.
- Both transcendence degrees use the dependency's `Algebra.trdeg`, with R and S
  themselves as arguments to `Algebra.trdeg R S`. `Cardinal.toENat` converts both
  cardinal values to `ℕ∞`, without collapsing a finite value or mixing universes.
- The conclusion is
  `q.height + Cardinal.toENat (@Algebra.trdeg p.ResidueField q.ResidueField _ _
  (Ideal.ResidueField.map p q (algebraMap R S) hpq).toAlgebra) ≤
  p.height + Cardinal.toENat (Algebra.trdeg R S)`.
  This is the source's ordinary subtraction inequality, rearranged additively.
  Using truncated subtraction alone could make `0 ≤ a - b` vacuous if b > a;
  the additive formulation retains the source's full content in the zero-height case.
  Heights are finite: R is Noetherian, S is Noetherian by finite type, and
  `Ideal.finiteHeight_of_isNoetherianRing` applies to their proper primes. The total
  transcendence degree is finite by `trdeg_lt_aleph0_of_finiteType`. For the residue
  degree, images of a finite list of S-generators generate S/q over R/p; after
  adjoining Frac(R/p) their fraction field is Frac(S/q), so it is a finitely
  generated field extension. Thus all four quantities are ordinary finite integers,
  and moving the residue degree across the inequality is exactly equivalent to the
  displayed formula in the node. No nonnegativity assumption is added, no clause is
  weakened, and no statement correction is needed.

Recorded statement dependencies used:

- `def-weil-pbc-noetherian-ring`:
  `Mathlib.RingTheory.Noetherian.Defs`, `IsNoetherianRing` (lines 193–198 read).
- `def-weil-pbc-finite-type-algebra`:
  `Mathlib.RingTheory.FiniteType`, `Algebra.FiniteType` (lines 37–40 read;
  its polynomial-presentation equivalent is `iff_quotient_mvPolynomial''`).
- `def-kun-transcendence-degree`:
  `Mathlib.RingTheory.AlgebraicIndependent.Basic`, `Algebra.trdeg`
  (lines 38–46 read; cardinal supremum of algebraically independent subsets).

All statement dependencies are public imports. The already recorded proof inputs
are ordinary non-public imports, including the polynomial-domain, flatness,
finite-type Noetherianity, flat height formula, field/domain transcendence towers,
polynomial PID, simple algebraic power basis, and
`Sheaf.RingTheory.LocalizationPrimeResidueFieldIso` /
`IsLocalization.prime_localRing_residueField_iso`. The four numbered paragraphs in
the theorem docstring reproduce the node's proof route and name these DAG inputs:
polynomial case, polynomial fibre, nonzero prime quotient, finite-generator induction.

Edge cases checked before writing:

- R = S: residue fields agree and both transcendence degrees vanish, so the bound
  is height ≤ itself, even for the zero prime.
- k ⊆ k[T], p = 0, q = 0: heights are zero and both transcendence degrees are one;
  the additive statement is 1 ≤ 1. This tests the zero-height subtraction issue.
- k ⊆ k[T], q = (T): heights are 0 and 1, total degree one and residue degree zero;
  the bound is again equality. Maximal and nonmaximal primes are both allowed.
- Z ⊆ Z[i], q = (1+i), p = (2): both heights are one and both degrees zero.
- Z_(p) ⊆ Z_(p)[T], q = (p) and q = (p,T): respectively (height,residue degree)
  is (1,1) and (2,0), total degree one, base height one; both yield equality.
- Z_(p) ⊆ Z_(p)[1/p] at q = 0: p contracts to zero, all degrees and heights vanish.
- A finite-type Noetherian domain need not have finite global Krull dimension;
  only the individual prime heights are used. No finite-global-dimension hypothesis
  or catenarity condition is introduced.

Searches actually run for this repair (through `msearch.py NH
lem-trf-affine-dimension-inequality`, not copied from the earlier report):

- LeanFinder: `height inequality for finite type algebra over Noetherian domain with
  residue field transcendence degree`. Eight hits; the closest were
  `Ideal.height_le_height_add_of_liesOver`, `trdeg_lt_aleph0`,
  `Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown` and tower bounds.
  None states the finite-type dimension inequality.
- Loogle: `Ideal.height, Algebra.trdeg`. Zero hits.
- Mathlib grep: `height.*trdeg|trdeg.*height|dimension-formula`. Zero hits.
- LeanSearch: `height dimension inequality finite type algebra Noetherian domain
  transcendence degree`. Eight hits, including `Ideal.height`, height versus Krull
  dimension and Krull height-theorem bounds; no exact statement.
- Direct rg in `WeilConjectures/`, `lean/Sheaf/` and `dag/lean_names_upstream.json`:
  node id, `height.*trdeg|trdeg.*height`, and affine-dimension/name variants. No
  upstream declaration states this inequality. The side module
  `Sheaf.RingTheory.UniversallyCatenaryDimensionFormula` was opened in full; it
  states an equality under the additional universally-catenary hypothesis and thus
  does not replace this node. Its canonical residue-field interface is reused.
- `grep -rn 'lem-trf-affine-dimension-inequality' WeilConjectures/`: zero hits.
  Direct searches for `height_add_trdeg_residueField_le`, `height_le_add_trdeg`,
  and `affine_dimension_inequality` in Mathlib, upstream and side sources had no hits.

No disputed statement, dependency repair, new node, or non-lean node edit remains.

## Second reading by NH

This is a fresh rereading by the same NH worker after drafting, not an independent
agent review. The dispatcher's instruction forbids starting other agents; the
maintainer supplies the independent review. I reopened the natural statement,
Stacks 02IJ and the completed Lean module and checked each binder and conclusion.

The two domain instances, injective algebraMap, Noetherian R and finite type S
match all four source assumptions. Both primes and their contraction equality
match the source's first sentence. The residue-field-map expression uses this
same hpq and ring map, so its algebra is fixed rather than universally quantified.
The quotient fraction-field instance ensures that κ has the intended meaning.
The bound uses `Algebra.trdeg R S`, with neither a field-only specialization nor an
unrelated numerical invariant. Independent u and v exclude no size case. There are
no lets, auto-implicit binders, local notation, private copies or extra assumptions.

The main point checked a second time was subtraction. The additive inequality
is equivalent to the source's signed inequality for the finite quantities here;
it does not silently replace subtraction by truncated cardinal/natural subtraction.
In particular q = 0 still asserts the required residue-degree bound. The example
module for the universally-catenary equality uses the same additive convention.
No mathematical mismatch was found in this pass, and no hypothesis was changed.

Return-point repair checklist:

- H1: supplied the actual stage-2 module, item lean record, Worker report and this
  second-reading section, replacing the earlier stage-1-only packet.
- H2: recopied the current item node and changed only `lean`; `split_report`, proof,
  statement and dependency lists are byte-for-byte equivalent as JSON values.
- H8: module and theorem docstrings cite Stacks 02IJ and the blueprint id, and the
  theorem docstring carries all four node proof steps with their dependency ids.
- H10/H11: compile and delivery validation are recorded below; this section gives
  the concrete rereading of the Lean binders and conclusion that was previously absent.
- The proof is exactly `by sorry`; there is no proof work or hollow definition.
  The lean record's signature is extracted verbatim from the module.

## Validation

The prescribed `scompile.py NH lem-trf-affine-dimension-inequality` check succeeded
for `lean/Sheaf/RingTheory/AffineDimensionInequality.lean`, exit code 0,
with no warnings or errors (sandbox probe 21.6 s, library-file check 3.5 s).
The node differs from current main only in `lean`, and its recorded signature
matches the source verbatim.

The prescribed `deliver2.py NH lem-trf-affine-dimension-inequality --no-push`
completed successfully: `OK (dry run): commit f915b534cf passes the preflight and
compiles; nothing pushed`. Its staged paths were exactly the module, the item node
and the stage-2 report. This report-only validation update is followed by the
normal delivery command, which repeats preflight and compilation before pushing.
