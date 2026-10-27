## Worker report

The module `Sheaf.AlgebraicGeometry.MonicPrincipalOpenFppf` defines the canonical
`AlgebraicGeometry.polynomialPrincipalOpenProjection` and states
`AlgebraicGeometry.polynomialPrincipalOpenProjection_fppf`. The latter has `sorry`
as its entire proof; its docstring contains all four DAG proof steps and their
named inputs. The definition has real data and uses no postponed theorem.
Only the item's `lean` record changes. No new nodes, dependency repairs, or
statement corrections are needed.

Clause-by-clause correspondence:

- A commutative ring A: `{A : Type u} [CommRing A]`, with explicit universe `u`.
- P in A[T]: `(P : Polynomial A)`.
- P monic, including degree zero: `(hP : P.Monic)`. Mathlib defines this as
  `P.leadingCoeff = 1`, where the coefficient is at `P.natDegree`. Over a
  nonzero ring this is precisely the displayed leading-term expansion in the
  node. Over the zero ring every polynomial is zero and is also monic because
  `0 = 1`; the displayed expansion exists with d = 0. Thus no case is lost.
- A[T,1/P] = A[T,Y]/(YP-1): the source of the helper is
  `Spec (CommRingCat.of (AdjoinRoot (Polynomial.C P * Polynomial.X - 1)))`.
  `AdjoinRoot f` is definitionally `Polynomial R / Ideal.span {f}`; here
  `R = Polynomial A`, so the outer variable is Y and the inner variable is T.
  The product P Y equals Y P in this commutative ring. This is the concrete
  quotient in the node, without an arbitrary localization model or chosen map.
- The canonical morphism to Spec A: the helper is `Spec.map` of
  `(AdjoinRoot.of (Polynomial.C P * Polynomial.X - 1)).comp Polynomial.C`.
  `AdjoinRoot.of` is the outer coefficient inclusion followed by the quotient
  homomorphism, so this composite is exactly the canonical A-algebra map.
- Flatness: `Flat (polynomialPrincipalOpenProjection P)`.
- Locally of finite presentation:
  `LocallyOfFinitePresentation (polynomialPrincipalOpenProjection P)`.
- Surjectivity: `Surjective (polynomialPrincipalOpenProjection P)`, the standard
  scheme class asserting surjectivity of the underlying point map.
- Fppf cover: these three conclusions are conjoined, exactly the node's explicit
  definition of an fppf cover. There is no extra quasi-compactness, positive
  degree, nontriviality, or chosen-cover hypothesis.

Statement dependency declarations, read with their full signatures and docstrings:

- `def-weil-polynomial-ring`: `Mathlib.Algebra.Polynomial.Basic`, `Polynomial`;
  its recorded degree/leading-coefficient interface is in
  `Mathlib.Algebra.Polynomial.Degree.Defs`, including `Polynomial.Monic`.
- `def-weil-affine-spectrum`: `Mathlib.AlgebraicGeometry.Scheme`,
  `AlgebraicGeometry.Spec` and `AlgebraicGeometry.Spec.map`.
- `def-weil-flat-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Flat`,
  `AlgebraicGeometry.Flat`; `Flat.iff_flat_stalkMap` identifies its affine-open
  definition with the node's stalkwise one.
- `def-sbc-locally-finite-presentation`:
  `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`,
  `AlgebraicGeometry.LocallyOfFinitePresentation`.

The auxiliary map reuses `AdjoinRoot`, `AdjoinRoot.of` and `Polynomial.C` from
Mathlib; it introduces no alternative ring, polynomial, flatness or fppf notion.
It belongs to the item's own construction and is recorded in `lean.declarations`.

Proof dependency interfaces were also read, and their modules are imported:

- `lem-weil-pbc-localization-away-polynomial-quotient`:
  `Mathlib.RingTheory.MvPolynomial.Localization`,
  `IsLocalization.Away.mvPolynomialQuotientEquiv` and its apply lemma.
- `lem-nagata-polynomial-projection-flat`:
  `Mathlib.AlgebraicGeometry.Morphisms.Flat`, `Flat.SpecMap_iff`, with
  `MvPolynomial.basisMonomials` and the free instance in
  `Mathlib.RingTheory.MvPolynomial.Basic`, and `Module.Flat.of_free`.
- `lem-weil-pbc-localization-flat`: `Mathlib.RingTheory.Flat.Localization`,
  `IsLocalization.flat`.
- `lem-weil-pbc-flat-ring-map-iff-flat-affine`:
  `Mathlib.AlgebraicGeometry.Morphisms.Flat`, `Flat.SpecMap_iff`.
- `lem-pc-flat-compose`: the same module, `Flat.comp`.
- `def-sbc-locally-finite-presentation`: the public statement import above.
- `lem-weil-pbc-spec-localization-away-basic-open`:
  `Mathlib.RingTheory.Spectrum.Prime.Topology`,
  `PrimeSpectrum.isTopologicalBasis_basic_opens`,
  `PrimeSpectrum.localization_away_isOpenEmbedding`, and
  `PrimeSpectrum.localization_away_comap_range`.
- `lem-sfb-polynomial-basic-open-image-coefficients`:
  `Mathlib.RingTheory.Spectrum.Prime.Polynomial`,
  `Polynomial.mem_image_comap_C_basicOpen`.

Edge cases checked before writing: for d = 0 the monic polynomial is 1 and
A[T,Y]/(Y-1) is A[T], whose projection is flat, finitely presented and
surjective. If A is the zero ring, its polynomial and quotient rings are zero;
both spectra are empty, and all three conclusions hold. Arbitrary positive
degree, nilpotents, finite residue fields and arbitrary characteristic cause no
restriction: modulo every prime, the leading coefficient remains 1. There is
no requirement for P to take a unit value at an A-rational point. All rings and
schemes in this concrete construction live in the explicit ring universe u;
no test objects are quantified in a smaller universe.

Sources checked: `literature/stacks-project/algebra.tex`,
`lemma-affineline-open` (Tag 00FB), including its entire proof: the image of D(P)
is the union of the coefficient basic opens. In particular, the monic case is
surjective. The accepted DAG supplies flatness by polynomial/localization
flatness and composition, and local finite presentation by two generators and
one relation. No statement dispute or node fault was found.

Searches for existing statements (all via the prescribed `msearch.py Q62
lem-sfb-monic-principal-open-fppf` wrapper):

- LeanFinder: "The principal open defined by a monic polynomial over any
  commutative ring is flat locally finitely presented and surjective over the
  base". Eight hits: monic image openness, universal coprime factorizations,
  finite presentation and smoothness tools; none states all three conclusions
  for this quotient projection.
- Loogle: `"Monic", "Surjective"`. No hits.
- Mathlib grep: `monic.*(fppf|[Ff]aithfully|[Ss]urjective)|[Ff]aithfully.*monic`.
  One unrelated universal-factorization proof hit.
- LeanSearch: "The principal open of the affine line defined by a monic
  polynomial is flat locally of finite presentation and surjective over the
  base ring". Eight hits: open-immersion/smooth finite-presentation facts,
  general flatness/openness facts, and affine-space surjectivity. No full match.
- `rg` in both `lean/WeilConjectures` and `lean/Sheaf` for that same regex and
  the exact node id. Hits concern adjoining roots of monic polynomials,
  Kummer covers and Artin--Schreier covers; none is this principal-open theorem.
  The exact node id has no existing source match.
- Name-clash search for `polynomialPrincipalOpenProjection` in Mathlib, both
  project roots and `dag/lean_names_upstream.json`: no hits before writing.

Validation: the prescribed scompile.py compiled both the sandbox and the
library-mode module cleanly. The first compile requested `noncomputable` for
`Spec.map`; the canonical map definition was marked accordingly. The final
compile has no errors or warnings. Every variable and universe is explicitly
bound, and no diagnostic declarations remain.

## Second reading by Q62

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
