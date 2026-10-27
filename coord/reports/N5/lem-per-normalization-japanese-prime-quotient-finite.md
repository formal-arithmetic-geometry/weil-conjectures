## Worker report

The module `Sheaf.RingTheory.NormalizationJapanesePrimeQuotientFinite` states
`RingTheory.normalization_primeQuotient_finite_of_isN2`, with its only proof
postponed by `sorry`. No definitions, helper nodes, dependency repairs, or
statement corrections are needed. The existing node is changed only in `lean`.

Source read: Marot, *Sur les anneaux universellement japonais*, Bulletin de la
SMF 103 (1975), printed p.104 (PDF p.3), Lemma 1.1 and the paragraph immediately
above it. The PDF was downloaded from the node's Numdam article URL into this
item's sandbox and its third page read using pdftotext. The standing hypotheses
are a Noetherian domain A, its fraction field K, a finite extension K', and its
integral closure A'. Lemma 1.1 assumes the contracted quotient Japanese and
concludes finite generation of the prime quotient as a module. This agrees
with the node without correction. Also read the latest blueprint ancestor
`lem-per-artin-gabber-affine-curve` and its proof; this item is an auxiliary
commutative-algebra input, not the blueprint unit's statement.

Hypothesis and conclusion correspondence:

- Commutative Noetherian integral domain R: `(R : Type u) [CommRing R]
  [IsDomain R] [IsNoetherianRing R]`. In particular the zero ring is excluded
  exactly as in the source's domain hypothesis.
- Fraction field K: `(K : Type v) [Field K] [Algebra R K]
  [IsFractionRing R K]`.
- Finite field extension L/K: `(L : Type w) [Field L] [Algebra K L]
  [FiniteDimensional K L]`. The scalar action of R on L is the composite,
  expressed by `[Algebra R L] [IsScalarTower R K L]`; this compatibility is
  structural data of the source's inclusion R in K in L, not an additional
  mathematical restriction.
- T is the integral closure of R in L: the actual Mathlib construction
  `integralClosure R L` is used everywhere. T is not an arbitrary algebra or a
  separately chosen ring. This definition is a subalgebra of L with carrier
  the elements integral over R.
- P is a prime ideal of T: `(P : Ideal (integralClosure R L)) [P.IsPrime]`.
- The contracted p is exactly `P.comap (algebraMap R (integralClosure R L))`.
  It is written out, avoiding a hidden let-bound object in the statement.
- The hypothesis that R/p is Japanese N-2 is `hJapanese : IsN2
  (R ⧸ P.comap (algebraMap R (integralClosure R L)))
  (FractionRing (R ⧸ P.comap (algebraMap R (integralClosure R L))))`.
  Primality of p and the domain/fraction-field instances are inferred from P.
- The sole conclusion is `Module.Finite
  (R ⧸ P.comap (algebraMap R (integralClosure R L)))
  ((integralClosure R L) ⧸ P)`, exactly finite generation as an R/p-module.
  Mathlib's `Ideal.quotientAlgebra` supplies the canonical scalar action.
  Its ring map is `Ideal.quotientMap P (algebraMap R (integralClosure R L))
  le_rfl`, taking a base class to its image class. It is injective by the
  existing `Ideal.quotientMap_injective`; injectivity is not introduced as an
  extra hypothesis or a redundant extra conclusion.
- There are no hypotheses on Noetherianity of T, normality of R, separability
  of L/K, or completeness, matching the final sentence of the node.

Dependency declarations read and used:

- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing` and its
  ideal-finite-generation characterization.
- `Mathlib.Algebra.Algebra.Defs`: `Algebra` and `algebraMap`; field extensions
  are algebras with field structures as specified by def-pc-field-extension.
- `Mathlib.RingTheory.IntegralClosure.Algebra.Basic`: `integralClosure`, whose
  full construction has carrier `{r | IsIntegral R r}`.
- `WeilConjectures.RingTheory.JapaneseDomain`: `IsN2`, read with its full
  signature, scalar-tower condition and finite-extension quantifier.
- `Mathlib.RingTheory.Finiteness.Defs`: `Module.Finite`, finite generation of
  the top submodule. `FiniteDimensional` is the field specialization.
- `Mathlib.RingTheory.Ideal.Quotient.Operations`: `Ideal.quotientMap`,
  `Ideal.quotientMap_injective`, and `Ideal.quotientAlgebra`, read with their
  definitions/signatures to check the quotient scalar action.

All five stmt_deps use their recorded declarations; each recorded module is
publicly imported. Proof dependencies are plain imports:
`Mathlib.RingTheory.Noetherian.Basic` gives
`isNoetherianRing_of_surjective` and `Submodule.FG.of_le` (both dependency
nodes are Mathlib leaves), and
`Sheaf.TraceFormula.AlmostFiniteResidueFieldDegree` gives
`RingTheory.almostFinite_residueField_fractionDegree`. The latter's full
signature and proof docstring were read; it allows any integral subalgebra
of the finite fraction-field extension and imposes no finiteness on T.
The theorem's docstring carries the four accepted proof steps, including the
canonical fraction-field identification needed for the supplied K.

Edge cases checked mathematically before writing: P=0 asks finiteness of T
only when R itself is Japanese; R a field gives T=L and the prime P=0, hence
ordinary finite-dimensionality. Maximal P is allowed with no stronger
hypothesis. An inseparable finite extension is allowed. L=K is allowed with
no proper-extension requirement. A nonnormal R is allowed. Prime ideals
exclude an improper quotient, so the Japanese premise is never applied to
the zero ring. The universes u, v, w of R, K, L are independent and explicitly
bound; no equality of universes or countability assumption is imposed. The
recorded IsN2 definition uses extensions in the universe of its fraction
field, as in the dependency; finite extensions in other universes have
isomorphic small models, so this does not require restricting w to u.

Searches actually run:

- msearch leanfinder: `quotient of integral closure in finite field extension
  by a prime is module finite over Japanese contracted base quotient`.
  Eight hits, including `module_finite_of_liesOver`,
  `algebra_finiteType_of_liesOver`, and quasi-finite residue-field instances.
  None matches: the first already assumes the whole algebra module finite,
  and the other hits either give only algebra finite type or assume
  quasi-finiteness/Dedekind hypotheses. Read
  `Mathlib/RingTheory/Finiteness/Quotient.lean:23` and surrounding signatures.
- msearch loogle: `"IsIntegralClosure", "Quotient", "Finite"`: zero hits.
- msearch grep: `[Jj]apanese|[Nn]agata|finite.*[Qq]uotient|[Qq]uotient.*finite`
  in `RingTheory/IntegralClosure`: zero hits.
- Direct rg in `lean/WeilConjectures` and `lean/Sheaf` for Japanese/N-2 and
  normalization/prime/quotient names found the reusable JapaneseDomain
  definition and related normalization lemmas, but no exact statement.
  Direct grep for this item id in WeilConjectures found no declaration.
- Exact-name rg for `normalization_primeQuotient_finite_of_isN2` across
  Mathlib, WeilConjectures, and Sheaf found no declaration. The upstream
  names index was also searched. Read
  `IsIntegralClosure.finite` in DedekindDomain/IntegralClosure.lean: it
  requires an integrally closed base and separability, so cannot replace
  this statement.

No STATEMENT-DISPUTED flag or node fault was found. The initial prescribed
scompile.py run compiled both sandbox and library module forms cleanly
(1.5 s and 1.4 s), with no errors or warnings.

The prescribed deliver2.py --no-push dry run passed the server preflight and
per-file compile, printing OK. The delivery contains only this module, the
item's lean record, and this report.

## Second reading by N5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
