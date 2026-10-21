## Worker report

The module `Sheaf.AlgebraicGeometry.SNCFiniteRootFaceRegular` states
`AlgebraicGeometry.isRegularRing_snc_finiteRoot_face`, with its sole proof `sorry`.
No definition or auxiliary theorem is introduced. The node changes only in `lean`.
The previous worker mistook Q37's stage-1 split review for a Lean attachment:
the base node has a reviewed seven-step proof plan but no `lean` record. This
packet supplies the missing statement, rather than resubmitting an unchanged node.

I read the item, all three statement-dependency nodes, their recorded definitions
and docstrings, and the full sibling statement `isRegularRing_snc_finiteRoot`.
I read ILO Expose IX Proposition 2.1 and its proof on printed pp.133–134 and
Stacks Tag 0BIA, `etale.tex`, `lemma-strict-normal-crossings`. ILO displays the
simultaneous root algebra over a regular parameter chart. The item's existing
agent-written seven-step proof extends that calculation to all coordinate faces;
the declaration docstring includes every step and its named dependencies.

The hypothesis and conclusion correspondence is:

- A commutative ring A: `(A : Type u) [CommRing A]`, with arbitrary explicit universe u.
- Regular affine X = Spec A: `hA : IsRegularScheme (Spec (.of A))`. The recorded
  definition includes both local Noetherianity and regularity of every stalk.
- A finite family t_1,...,t_r, including r = 0: `(r : ℕ) (t : Fin r → A)`.
  Fin uses zero-based labels for the same finite tuple; no positive-r assumption.
- An SNC boundary on X: `(H : (Spec (.of A)).IdealSheafData)` and
  `hH : IsStrictNormalCrossingsBoundary H`, using the dependency's exact predicate.
- The branches V(t_i) are reduced closed subschemes: `hreduced` states
  `IsReduced (A ⧸ Ideal.span ({t i} : Set A))` for every i.
- Pairwise distinct branches: `hdistinct` is injectivity of
  `i ↦ PrimeSpectrum.zeroLocus ({t i} : Set A)`.
- These are precisely the irreducible branches of H: `hbranches` equates their
  range with the irreducible components of H.support, mapped from the support
  subtype to the ambient spectrum. Each V(t_i) therefore is an irreducible
  component, not an arbitrary union. Together with hreduced this identifies
  the reduced closed subscheme structure, not just its point set. This is the
  same branch interface as the existing empty-face sibling theorem.
- Positive integer n: `(n : ℕ) (hn : 0 < n)`. Invertibility of n times 1_A:
  `hnunit : IsUnit (n : A)`. There is no field or characteristic assumption added.
- The specified simultaneous root ring C_n is the actual quotient of
  `MvPolynomial (Fin r) A` by `Ideal.span (Set.range (fun i ↦ X i ^ n - C (t i)))`.
  No arbitrary algebra or map substitutes for this construction.
- Every subset J: `(J : Set (Fin r))`, universally bound. No decidability,
  nonemptiness, irreducibility, or connectedness assumption is imposed on J or
  its intersection.
- Killing x_j for j in J: the conclusion takes the second quotient by
  `Ideal.map (Ideal.Quotient.mk rootIdeal) (Ideal.span (X '' J))`.
  The definition of Ideal.map is the ideal spanned by the image, so this is
  exactly the ideal generated in C_n by the root coordinates indexed by J.
  Both occurrences of rootIdeal are written in full in the Lean signature.
- Regular Noetherian face ring, with every prime localization regular local:
  `IsRegularRing` of that double quotient. Mathlib's class extends
  `IsNoetherianRing` and its field requires `IsRegularLocalRing` of each prime
  localization. Thus both parts of the conclusion are present. The equivalent
  regularity of the affine closed subscheme expresses the same ring assertion;
  the module retains the node's primary ring form.

Statement dependencies actually used:

- `Sheaf.AlgebraicGeometry.IsRegularScheme`,
  `AlgebraicGeometry.IsRegularScheme` = `IsLocallyNoetherian X ∧ IsRegular X`.
- `Sheaf.AlgebraicGeometry.StrictNormalCrossingsBoundary`,
  `AlgebraicGeometry.IsStrictNormalCrossingsBoundary`: effective Cartier,
  radical boundary; finite distinct integral regular components and the
  regular-intersection dimension condition.
- `Mathlib.Algebra.MvPolynomial.Basic`, `MvPolynomial`, `MvPolynomial.X`,
  `MvPolynomial.C`; the dependency's `aeval` and `algHom_ext` describe its
  universal property but are not needed to write the quotient presentation.
- `Mathlib.RingTheory.RegularLocalRing.Defs`, `IsRegularRing`, as recorded in
  the regular-scheme node's ring-level mathlib_match. Standard `Ideal.span`,
  `Ideal.Quotient.mk`, `Ideal.map`, and quotients supply the literal constructions.

All already stated proof dependencies are included as plain proof imports:
`Mathlib.AlgebraicGeometry.AffineScheme` (affine stalk localization),
`Mathlib.AlgebraicGeometry.Noetherian` (Noetherian affine sections),
`Mathlib.RingTheory.FiniteType` (`Algebra.FiniteType.isNoetherianRing`),
`Mathlib.RingTheory.Localization.Ideal` (localized quotient),
`Mathlib.RingTheory.AdjoinRoot` (`AdjoinRoot.powerBasis'`),
`Mathlib.RingTheory.RegularLocalRing.Polynomial`
(`MvPolynomial.isRegularRing_of_isRegularRing`),
`WeilConjectures.RingTheory.RegularLocalLocalization`
(`IsRegularLocalRing.localization_at_prime_and_isRegularRing`),
`WeilConjectures.Mathlib.RingTheory.RegularLocalRing.Defs`
(`IsRegularLocalRing.isDomain`),
`WeilConjectures.RingTheory.RootAlgebraRegularAtRoot`
(`AdjoinRoot.isRegularLocalRing_atPrime_of_root_mem`),
`WeilConjectures.RingTheory.LocalizationOfRegularRing`
(`RingTheory.isRegularRing_of_localization`), and
`WeilConjectures.RingTheory.HypersurfaceDerivationRegular`
(`IsRegularRing.quotient_span_singleton_of_isUnit_derivation`).

Edge cases checked before writing:

- J empty gives the zero coordinate ideal and recovers the already stated
  regularity of C_n. J all indices yields A/(t_1,...,t_r).
- r = 0 gives a polynomial ring in no variables, no root relations, and only
  J empty, hence A. No branch nonemptiness is introduced.
- n = 1 identifies the root coordinates with t_i, giving exactly the regular
  SNC intersection quotient.
- A = 0, with the empty boundary family, gives the zero ring. No Nontrivial or
  IsDomain binder excludes it. Its spectrum has no primes, as required.
- In characteristic zero with A = k[s], branches s and s-1 are disjoint; killing
  both roots gives zero. The assertion has no nonempty-intersection binder.
- In A = k[s,t], branches s and s-t(t-1) meet transversally at two points.
  Killing both roots gives k[t]/(t(t-1)), a disconnected regular ring, and the
  statement imposes no integral/domain condition on this face.
- An exponent divisible by the residue characteristic is correctly excluded
  by hnunit; it is used in the unit-derivative step of the recorded proof.

Searches run in this attempt (all external searches through msearch.py):

- LeanFinder: “Coordinate faces of simultaneous roots of strict normal crossings
  parameters over a regular Noetherian ring are regular” returned eight results:
  MvPolynomial.isRegular_prod_X, standard smooth presentations, weak regular
  sequences and standard etale algebras. None states coordinate-face regularity.
- Loogle: `IsRegularRing, MvPolynomial` returned only
  `MvPolynomial.isRegularRing_of_isRegularRing`, for the polynomial ring without
  root relations or coordinate quotient; not this statement.
- Mathlib grep: `IsRegularRing|IsRegularLocalRing` restricted to
  RingTheory/RegularLocalRing returned definitions and polynomial regularity,
  no root-coordinate quotient regularity.
- LeanSearch: “Regularity of quotients of simultaneous Kummer root algebras by
  subsets of root coordinates” returned eight root-presentation, quotient,
  integral algebra and Kummer-equivalence declarations; none asserts regularity.
- rg of the source project for the item id found no declaration. Source searches
  for finiteRoot, root regularity and normal crossings found the one-root
  regular-at-root theorem and specialized cyclic-root charts, not this
  simultaneous all-faces theorem.
- rg of lean/Sheaf for isRegularRing_snc, SNCFiniteRootFace, and coordinate-face
  regularity found the existing SNCFiniteRootRegularRing empty-face sibling,
  whose full signature I read; it is strictly the J-empty case. The finite
  root-ring abbreviation sncRootLevel and coordinate definition in
  SNCUniversalResidualCharts were also read. This delivery adds no competing
  definition: it writes the primary polynomial-and-quotient construction directly.

No new nodes, dependency repairs, statement correction, or mathematical dispute.
All binders and universes are explicit. The sole theorem retains the stage-2
sorry proof, and no data is postponed.

Validation: scompile.py compiled both the sandbox and actual library module
successfully (2.5 s and 2.8 s respectively), with no warnings or errors.

## Second reading by NS

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
