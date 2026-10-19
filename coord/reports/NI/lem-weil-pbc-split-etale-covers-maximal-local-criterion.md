## Worker report

Existing declaration: `IsStrictlyHenselianLocalRing.localization_atPrime_of_forall_retraction`
in `WeilConjectures.RingTheory.ProEtale.RetractionsStrictlyHenselian`, lines 483–492
of the read-only slopmaster2 source. No new module or theorem is needed. The full
signature and preceding docstring were read. The source is Stacks Tag 097V,
`proetale.tex`, lemma-have-sections-strictly-henselian (lines 1443–1490), which was
also read directly. Only the item's lean record changes.

Hypotheses and clauses:

- A commutative ring: `{A : Type u} [CommRing A]`.
- Every commutative A-algebra: `∀ (B : Type u) [CommRing B] [Algebra A B]` in H.
  There is no Nontrivial assumption. Same-universe test algebras suffice: finite
  presentation supplies a quotient of a finite polynomial algebra over A, hence
  a representative in A's universe for every etale algebra. Thus this does not
  remove any isomorphism class of tests, even for larger-universe presentations.
- Etale: `Algebra.Etale A B`. The node explicitly identifies ring etaleness with
  affine-scheme etaleness. The bridge is the `HasRingHomProperty @Etale
  RingHom.Etale` instance in `Mathlib.AlgebraicGeometry.Morphisms.Etale` and the
  algebraMap ring-map encoding. This is the same notion as the dependency's
  `AlgebraicGeometry.Etale`, not a new definition.
- Faithfully flat: `Function.Surjective (PrimeSpectrum.comap (algebraMap A B))`.
  Since the algebra is etale it is flat. For flat algebras this condition is
  equivalent to `Module.FaithfullyFlat A B`, by
  `Module.FaithfullyFlat.of_comap_surjective` (lines 48–50) and
  `PrimeSpectrum.comap_surjective_of_faithfullyFlat` (lines 146–147) in
  `Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra`; their signatures/docstrings
  were read. Hence H quantifies over exactly the node's covers.
- An A-algebra retraction: `∃ f : B →+* A, f.comp (algebraMap A B) = RingHom.id A`.
  This equation is exactly the scalar-compatibility law for a ring homomorphism
  from B to the identity A-algebra A; thus it is equivalent to an A-algebra
  homomorphism B →ₐ[A] A. The equation is the requested composition identity.
- Every maximal ideal: `(m : Ideal A) [m.IsMaximal]`. The arbitrary m is universally
  bound, and maximal implies prime for the localization.
- Conclusion: `IsStrictlyHenselianLocalRing (Localization.AtPrime m)`. These are
  the recorded dependency declarations, not private copies.
- The final finite-presentation clause is part of `Algebra.Etale` itself:
  its `finitePresentation : Algebra.FinitePresentation A B` field. No separate
  finite-presentation assumption restricts the maps and no clause is lost.

Dependency declarations inspected:

- `Mathlib.RingTheory.Flat.FaithfullyFlat.Basic`, `Module.FaithfullyFlat`:
  flatness plus nonvanishing at all maximal ideals; the node's exactness
  characterization is the equivalent recorded Mathlib interface.
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`, `AlgebraicGeometry.Etale`:
  affine-locally ring-etale; the ring-map property bridge above applies.
- `Mathlib.RingTheory.Localization.AtPrime.Basic`, `Localization.AtPrime`:
  localization at `m.primeCompl`.
- `WeilConjectures.Mathlib.RingTheory.Henselian`, `IsStrictlyHenselianLocalRing`:
  extends `HenselianLocalRing` with separably closed residue field.
- `Mathlib.RingTheory.FinitePresentation`, `Algebra.FinitePresentation`:
  finite polynomial presentation with finitely generated kernel. The actual
  ring-etale interface is `Algebra.Etale` in `Mathlib.RingTheory.Etale.Basic`.

Edge cases checked: the zero ring has no maximal ideals, so the conclusion is
vacuous without excluding it; no characteristic is fixed. Arbitrary maximal
ideals, disconnected rings, and all finite-presentation etale covers (not only
finite etale algebras) are retained. B = A gives the identity retraction. The zero
algebra over a nonzero ring is not surjective on spectra, and is correctly not a
faithfully flat test. No node faults or statement dispute were found.

Searches performed on 2026-10-15:

- msearch.py leanfinder: "Every faithfully flat etale algebra admits a retraction
  implies localizations at maximal ideals are strictly henselian". Eight hits,
  all component results (Algebra.IsEtaleAt, localizations, HenselianLocalRing).
- msearch.py loogle: "HenselianLocalRing". Seven component hits; no recognition
  theorem in Mathlib.
- msearch.py grep: "[Hh]enselian.*[Rr]etraction|[Rr]etraction.*[Hh]enselian"
  in RingTheory: zero Mathlib hits.
- rg over slopmaster2 WeilConjectures and project lean/Sheaf for
  `forall_retraction|lem-weil-pbc-split-etale-covers-maximal-local-criterion`:
  found the exact upstream theorem at line 483 and its two component lemmas at
  lines 316 and 362; no project duplicate. The node itself already suggested
  precisely this declaration in lean_candidates; the complete signature and
  equivalences above confirm that suggestion.

Validation: deliver2.py --no-push checks the existing declaration with a server
#check and runs server preflight; no local compilation is performed.

## Second reading by NI

I reread the node statement, its Stacks source (Tag 097V, lines 1443--1490),
and the existing declaration.  The objects and clauses match item by item:

- The commutative ring `A` is `{A : Type u} [CommRing A]`.
- The universal commutative `A`-algebra `B` is `∀ (B : Type u) [CommRing B]
  [Algebra A B]`.
- The two cover hypotheses are `Algebra.Etale A B` and surjectivity of
  `PrimeSpectrum.comap (algebraMap A B)`, which is equivalent to faithful
  flatness for this etale map.
- The splitting clause is the ring retraction
  `∃ f : B →+* A, f.comp (algebraMap A B) = RingHom.id A`.
- The conclusion is quantified over every maximal ideal
  `(m : Ideal A) [m.IsMaximal]` and is exactly
  `IsStrictlyHenselianLocalRing (Localization.AtPrime m)`.
  `Algebra.Etale` carries the finite-presentation condition mentioned in the
  final sentence of the node, so no separate hypothesis is omitted or added.

The declaration uses the recorded notions rather than private copies.  The
zero ring and rings with no maximal ideals make the conclusion vacuous;
`B = A` supplies the identity retraction; no characteristic, nontriviality,
connectedness, or universe restriction beyond the node is imposed.  Searches
of Mathlib, `WeilConjectures`, and project `lean/Sheaf` found no competing
statement.  I found no mismatch and changed no statement or module; only the
node's existing declaration record is retained.
