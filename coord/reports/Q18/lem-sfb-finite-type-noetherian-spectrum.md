## Worker report

The module `Sheaf.AlgebraicGeometry.FiniteTypeNoetherianSpectrum` states
`AlgebraicGeometry.noetherianSpace_primeSpectrum_of_finiteType`, with its sole
proof `by sorry`, as required for stage 2. This resumed worker retained the prior
signature, added the missing statement/proof dependency imports, and replaced the
short proof summary with the complete seven-step natural-language DAG argument.
The node was refreshed from the shared read-only copy; only `lean` differs.
There are no new nodes, dependency repairs, statement corrections, or disputes.

The node is rendered hypothesis by hypothesis and clause by clause:

- Commutative rings with identity: `(R : Type u) (B : Type v)` with
  `[CommRing R] [CommRing B]`. Both universes are explicitly declared and
  independent, so rings of arbitrary sizes are included.
- A unital homomorphism: `(f : R →+* B)`. The induced algebra structure is the
  one belonging to this specific map, not an unrelated algebra structure.
- Finite generation as an R-algebra: `(hf : f.FiniteType)`. The definition
  `RingHom.FiniteType` in `Mathlib.RingTheory.FiniteType`, lines 215–218,
  is `@Algebra.FiniteType R B _ _ f.toAlgebra`; `Algebra.FiniteType` means that
  the top subalgebra is finitely generated. The node's polynomial-surjection
  phrase is an equivalent description of this hypothesis, not a second
  independent requirement. It includes zero generators.
- Noetherianity of the underlying Zariski space of Spec R:
  `[NoetherianSpace (PrimeSpectrum R)]`.
- The conclusion for Spec B: `NoetherianSpace (PrimeSpectrum B)`.
- The ascending-open-chain meaning is exactly Mathlib's
  `TopologicalSpace.NoetherianSpace`, defined as `WellFoundedGT (Opens X)` in
  `Mathlib.Topology.NoetherianSpace`, lines 51–52. No `IsNoetherianRing`
  hypothesis appears. Zero rings are not excluded by any binder.

Dependency interfaces read and used:

- `def-weil-affine-spectrum`: its recorded declaration is
  `AlgebraicGeometry.Spec`, with `AlgebraicGeometry.Spec.map`, in
  `Mathlib.AlgebraicGeometry.Scheme`, publicly imported. Their full definitions
  and docstrings at lines 469–480 were read. The carrier and topology of
  `Spec (CommRingCat.of R)` are the existing `PrimeSpectrum R`, so the
  statement uses that underlying space directly, without duplicating Spec.
- `lem-weil-pbc-spec-quotient-homeomorphism-zero-locus`:
  `PrimeSpectrum.isClosedEmbedding_comap_of_surjective` and
  `PrimeSpectrum.range_comap_of_surjective` in
  `Mathlib.RingTheory.Spectrum.Prime.Topology` (available through the public
  Scheme import).
- `lem-weil-pbc-spec-irreducible-components-minimal-primes`:
  `PrimeSpectrum.zeroLocus_minimalPrimes` in that same topology module.
- `def-weil-ring-localization-away`: `Localization.Away` in
  `Mathlib.GroupTheory.MonoidLocalization.Away`, and its ring interface
  `IsLocalization.Away` in `Mathlib.RingTheory.Localization.Away.Basic`.
  The latter is explicitly imported for the proof plan.
- `lem-weil-pbc-monic-quotient-free`: `AdjoinRoot.powerBasis'`,
  `Polynomial.Monic.free_adjoinRoot`, and `Polynomial.Monic.finite_adjoinRoot`
  in `Mathlib.RingTheory.AdjoinRoot`, explicitly imported for the proof.
- `lem-weil-pbc-spec-localization-away-basic-open`:
  `PrimeSpectrum.isTopologicalBasis_basic_opens`,
  `PrimeSpectrum.localization_away_isOpenEmbedding`, and
  `PrimeSpectrum.localization_away_comap_range`, again in the topology module.

The seven proof steps and all five proof dependencies appear in the theorem
comment: closed-chain facts, the exact Noetherian induction claim, reduction of
an irreducible closed set to Spec of a domain, the least-degree polynomial and
denominator argument, stabilization on a principal open, stabilization on its
proper closed complement, and finite-variable induction followed by a quotient.
The Ohm–Pendleton paper remains unavailable in the local collection; the module
explicitly attributes this proof to the node's independent agent argument.
The current blueprint paragraph (2), the node's source and proof_origin, and all
statement/proof dependency records were read. No repair note for this item exists.

Edge cases checked mathematically: if R is zero, a unital map forces B zero;
if B is zero, its spectrum is empty and Noetherian; zero generators gives a
quotient of R; a field base includes usual affine spaces. An infinite square-zero
thickening of a field has a one-point spectrum despite being a non-Noetherian
ring, so this formulation preserves the essential distinction between the
node's hypothesis and the stronger search hits. No nontriviality or domain
hypothesis was added; the domain appears only inside the proof's reduction.

Searches run for this resumed attempt with
`python3 /home/ubuntu/weil-launcher-nt/msearch.py Q18
lem-sfb-finite-type-noetherian-spectrum <tool> <query>`:

- `leanfinder`: `finite type algebra over a ring with Noetherian prime spectrum
  has Noetherian prime spectrum`. Eight hits, including
  `Algebra.FiniteType.isNoetherianRing`,
  `Algebra.EssFiniteType.isNoetherianRing`, and Noetherian scheme instances.
  All applicable spectrum hits require the stronger `IsNoetherianRing R`.
- `loogle`: `"NoetherianSpace", "PrimeSpectrum"`. One hit,
  `PrimeSpectrum.instNoetherianSpace`, with `[IsNoetherianRing R]`.
- `grep`: `NoetherianSpace|noetherianSpace`, restricted to
  `RingTheory/Spectrum/Prime`. Three lines in `Prime/Noetherian.lean`:
  import line 11 and instance lines 30–31. The enclosing base-ring hypothesis
  at line 28 was read, confirming the stronger assumption.
- `leansearch`: `A finite type algebra over a ring with Noetherian prime
  spectrum has Noetherian prime spectrum`. Eight hits, again only the
  stronger ring-Noetherian results and related equivalences.
- `rg -n -i` over `WeilConjectures/`, shared `lean/Sheaf/`, and
  `dag/lean_names_upstream.json`, using
  `noetherian.*(spectrum|finitetype)|finitetype.*noetherian` and the item id:
  only stronger Noetherian-ring results, uses thereof, and the parent module's
  prose reference. Upstream `noetherianSpace` results over fields are special
  cases. No exact theorem found.
- Exact-name `rg` over Mathlib, upstream, shared Sheaf sources and the name
  index found no existing `noetherianSpace_primeSpectrum_of_finiteType`.
  `grep -rn` for the node id in upstream `WeilConjectures/` found no match.

The repaired module compiles cleanly with the prescribed `scompile.py`, both as
its sandbox module and at its library module path. Every variable/universe is
explicitly bound. There are no declarations beyond the single named theorem.
The independent second reader following this worker must recheck the updated
imports and expanded documentation. The earlier reading below is retained as
historical material and does not claim to review this worker's new edits.

## Earlier second reading (a previous round; superseded)

I reread the node and the module independently.  The binders `R`, `B`, and
`f` match the node's commutative rings and unital map.  The typeclass
`NoetherianSpace (PrimeSpectrum R)` matches the stated Zariski topological
hypothesis, while `f.FiniteType` is exactly the finite-generation condition
(the polynomial-surjection formulation in the node).  The conclusion has the
same spectrum and the same Noetherian-space predicate for `B`.  No hypothesis,
clause, zero-ring case, or d = 0 case is omitted or strengthened; no mismatch
was found.

## Second reading by Q18

I read the current node copy at
`dag/nodes/sec-six-functors-basics/lem-sfb-finite-type-noetherian-spectrum.json`,
its source entry (Ohm--Pendleton, *Rings with Noetherian spectrum*, Theorem 2.5 and
Corollary 2.6), the complete theorem file, and every recorded statement dependency.
The source paper is unavailable locally; the node records the independent proof route
from blueprint paragraph (2).

The node's objects, hypotheses, and conclusion match the Lean declaration
`AlgebraicGeometry.noetherianSpace_primeSpectrum_of_finiteType` item by item:

- The commutative rings with identity are `(R : Type u)` and `(B : Type v)` with
  `[CommRing R]` and `[CommRing B]`; both universes are explicit and independent.
- The specified unital map is `(f : R →+* B)`, so the statement uses the given map rather
  than choosing an unrelated algebra structure.
- Finite generation as an `R`-algebra is `(hf : f.FiniteType)`.  This is Mathlib's
  `RingHom.FiniteType` (the finitely generated top subalgebra condition), equivalent to
  the node's finite polynomial-surjection formulation and allowing zero generators.
- The sole hypothesis on the source spectrum is the instance
  `[NoetherianSpace (PrimeSpectrum R)]`, exactly topological Noetherianity; there is no
  added `IsNoetherianRing R` assumption.
- The conclusion is exactly `NoetherianSpace (PrimeSpectrum B)`, with no extra ring or
  scheme conclusion.  `NoetherianSpace` is the ascending-open-chain condition used by
  the node (equivalently the descending-closed-chain form in the proof).

The recorded dependency `def-weil-affine-spectrum` is Mathlib's
`AlgebraicGeometry.Spec` (and `Spec.map`), whose underlying topological space is the
existing `PrimeSpectrum`; no private spectrum definition is introduced.  I also read
the recorded declarations for the quotient-spectrum, minimal-prime, localization-away,
monic-quotient, and localization-basic-open proof dependencies.  The theorem docstring
uses each of these only in the seven proof steps recorded by the node; the statement
itself needs no additional dependency hypothesis.

Edge cases are covered by the binders and hypotheses: the zero ring is allowed; a unital
map out of a zero ring forces the target to be zero; the zero target has empty spectrum;
zero polynomial generators give the identity/quotient case; and no domain, characteristic,
nonemptiness, or finiteness assumption is imposed.  The proof's temporary domain and
nonzero leading-coefficient assumptions occur only after reduction to an irreducible
closed subset and are not hypotheses of the theorem.  Independent universes `u` and `v`
exclude no valid ring sizes.

I searched Mathlib, the upstream `WeilConjectures` sources, shared `lean/Sheaf`, and
`dag/lean_names_upstream.json` by exact name and by finite-type/Noetherian-spectrum
keywords.  LeanFinder and LeanSearch returned ring-Noetherian results requiring the strictly
stronger `IsNoetherianRing R`, together with unrelated Jacobson-ring results; Loogle returned only
`PrimeSpectrum.instNoetherianSpace` under that stronger assumption.  Grep of
`Mathlib/RingTheory/Spectrum/Prime`, upstream, and shared declarations found no exact
match for this theorem.  Thus the module is required and is not an existing declaration.

No mathematical mismatch was found, so no statement, dependency, or source change was made.
The sandbox node omitted the current base’s inherited `lean_audit` field; I refreshed
the node from the read-only shared copy while preserving its `lean` record, removing
that unintended metadata delta.  Only `lean` now differs from the current base.  The
module has one theorem with a `sorry` proof and complete source/blueprint documentation;
all variables and universes are bound and no line exceeds 100 characters.  The prescribed
`scompile.py` check succeeds for both the sandbox and library module paths with no errors
or warnings.

Independent second-reader search log (this session):

- LeanFinder: `Polynomial extension preserves the ascending chain condition on radical
  ideals of a commutative ring`; eight hits, chiefly `Polynomial.isNoetherianRing`,
  `MvPolynomial.isNoetherianRing`, `AdjoinRoot.instIsNoetherianRing`, and
  `Algebra.FiniteType.isNoetherianRing`, all with ring-Noetherian hypotheses; the
  Jacobson-ring hits concern another property.
- LeanSearch: `Hilbert basis theorem for topologically Noetherian spectra without a
  Noetherian ring assumption`; eight hits, all polynomial/affine Noetherian-ring results.
- Loogle: `"NoetherianSpace", "PrimeSpectrum"`; one hit,
  `PrimeSpectrum.instNoetherianSpace`, explicitly requiring `IsNoetherianRing R`.
- Wrapper grep: `radical.*[Ff]inite|NoetherianSpace` in `RingTheory/Spectrum/Prime`;
  three lines, all in `Prime/Noetherian.lean`.  I read its surrounding binders.
- Direct `rg -n -i` with `noetherianSpace_primeSpectrum_of_finiteType`,
  `noetherian.*spectrum`, `spectrum.*noetherian`, and `radical.*finite.*generat`
  across upstream `WeilConjectures`, shared `lean/Sheaf`, Mathlib's spectrum directory,
  and the upstream name index: no duplicate theorem.  The upstream candidate
  `PrimeSpectrum.finite_irreducibleComponents_of_finiteType` was opened and requires a
  field base, so is only a special case.

Source details opened for this reading: Stacks `topology.tex:1244` (definition-noetherian)
through the proof of Tag 0052; `algebra.tex:3207` (00E4, lemma-standard-open), `:3227`
(00E5, lemma-spec-closed), and `:4665` (00ES, lemma-irreducible).  These impose no
Noetherian-ring, field, domain, or nonzero-ring assumption on the theorem's original
rings.  I opened the corresponding Mathlib quotient/comap and localization declarations,
`zeroLocus_minimalPrimes`, `AdjoinRoot.powerBasis'`, and `IsLocalization.Away`; their
signatures support the uses in the docstring.  The seven numbered docstring paragraphs
match the seven DAG proof steps, including the precise induction claim, denominator
clearing, proper closed complement, and zero-variable quotient case.  No new nodes,
dependency modules, or `statement_change` are present, so H12/H13 and the citer audit
for a correction are inapplicable.  No repair note exists for the item.
