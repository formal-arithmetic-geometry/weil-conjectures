## Worker report

The module defines four predicates on one scheme morphism `i : T ⟶ T'`.
The source is Stacks Project, More on Morphisms, Definition 37.2.1
(Tag 04EX), with the affine-over-base usage in Definition 37.11.1
(Tag 02H0). The repository's `literature/stacks-project/` checkout is
absent on this machine; I read the local source copy at
`/home/ubuntu/c1-stacks-review/more-morphisms.tex` and checked the two tags
against the Stacks website.

- The schemes `T`, `T'` and closed immersion `i` are `T T' : Scheme.{u}`
  and `IsClosedImmersion i` in each predicate (directly or through
  `IsNthOrderThickening`). `i.ker : T'.IdealSheafData` is the defining
  quasi-coherent ideal sheaf.
- Clause (1), equality of underlying spaces, is `Surjective i` together
  with `IsClosedImmersion i` in `IsThickening`. A closed immersion is already
  a homeomorphism onto its closed image.
- Clause (2), square zero, is `i.ker ^ 2 = ⊥` in
  `IsFirstOrderThickening`. Mathlib's zero ideal sheaf is `⊥`.
- Clause (3), nilpotence, is `∃ n : ℕ, IsNthOrderThickening n i` in
  `IsFiniteOrderThickening`, and the latter expands to
  `IsClosedImmersion i ∧ i.ker ^ (n + 1) = ⊥`.
- Clause (4), the `n`th order condition, is exactly
  `IsNthOrderThickening n i` for `n : ℕ`. A thickening over `S` adds
  `[T.Over S]`, `[T'.Over S]`, and `[i.IsOver S]` to the appropriate
  predicate; Mathlib's `i.IsOver S` expresses the commuting structure
  morphisms. A thickening of affine schemes adds `[IsAffine T]` and
  `[IsAffine T']`. These are existing notions, so the module does not
  define copies of them. The node's comments that finite order implies
  surjectivity and affine `T'` implies affine `T` are consequences, not
  additional conditions in these predicates.

Dependencies read and used: `AlgebraicGeometry.Scheme` and `Scheme.Hom`
(`Mathlib.AlgebraicGeometry.Scheme`), `IsClosedImmersion`
(`Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`), `Scheme.Hom.ker`
and `Scheme.IdealSheafData` with its `Pow` and `Zero` instances
(`Mathlib.AlgebraicGeometry.IdealSheaf.Basic`), `Surjective`
(`Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap`), `Spec`
(`Mathlib.AlgebraicGeometry.Scheme`), `Scheme.Over` and `Hom.IsOver`
(`Mathlib.AlgebraicGeometry.Over`), and `IsAffine`
(`Mathlib.AlgebraicGeometry.AffineScheme`). The last four are used to
interpret the source's over-base and affine restrictions; the base
predicates need no extra parameters.

Edge cases: `n = 0` gives `i.ker ^ 1 = ⊥`, so a zeroth order thickening
has zero ideal as required; first order is the `n = 1` case. The empty
scheme is allowed because no nonemptiness hypothesis is imposed. The
universe `u` is arbitrary and covers any scheme size supported by Mathlib.

Searches for an existing declaration:

- `msearch.py ... leanfinder "first order thickening of schemes closed
  immersion with square zero ideal sheaf"`: returned subscheme and
  closed-immersion declarations, but no thickening predicate.
- `msearch.py ... loogle "IsClosedImmersion,IsNilpotent,IsThickening"`:
  zero hits; Loogle reported an unknown identifier for the unqualified
  `IsClosedImmersion` query.
- `msearch.py ... grep "thickening|FirstOrderThickening|IsThickening"
  AlgebraicGeometry`: only the informal phrase "infinitesimal
  thickening" in `FormallyUnramified.lean`.
- `rg` over `WeilConjectures/`, `lean/Sheaf/`, and Mathlib's
  `AlgebraicGeometry/`: there are uses of thickening terminology and a
  dual-number construction, but no general predicate with these names.
- `rg -n "def-sbc-first-order-thickening"` over `WeilConjectures/`:
  no hits.

Server compile: clean, exit 0, 49 lines, 1.5 seconds.

## Second reading by C1

The node introduces schemes `T` and `T'`, a morphism `i : T ⟶ T'`, and
the closed-immersion hypothesis. In Lean these are the implicit scheme
binders `{T T' : Scheme.{u}}`, the morphism argument `(i : T ⟶ T')`, and
the `IsClosedImmersion i` conjunct in each predicate. The universe `u` is
unrestricted.

- The ideal sheaf `𝓘 = ker(O_{T'} → i_* O_T)` is rendered by `i.ker`,
  whose type is `T'.IdealSheafData` (`Scheme.Hom.ker`). This is the
  dependency declaration for the closed-immersion ideal sheaf.
- Node clause (1), equal underlying spaces/surjectivity, is exactly
  `IsThickening i := IsClosedImmersion i ∧ Surjective i`. `Surjective i`
  is Mathlib's surjectivity of `i.base`; closed immersion supplies the
  closed embedding, so this has the stated topological meaning.
- Node clause (2), square-zero ideal, is exactly
  `IsFirstOrderThickening i := IsClosedImmersion i ∧ i.ker ^ 2 = ⊥`.
- Node clause (3), finite order, is exactly
  `IsFiniteOrderThickening i := ∃ n : ℕ, IsNthOrderThickening n i`, and
  `IsNthOrderThickening n i` expands to
  `IsClosedImmersion i ∧ i.ker ^ (n + 1) = ⊥`. The quantifier and
  exponent agree with the node. In particular `n = 0` gives the zero
  ideal condition, and first order is the square-zero (`n = 1`) case.
- Node clause (4), “over `S`”, is represented by adding Mathlib's
  `[T.Over S]`, `[T'.Over S]`, and `[i.IsOver S]` instances to the
  corresponding predicate; `Scheme.Hom.IsOver` is precisely the required
  commuting structure-map condition. “Of affine schemes” is represented
  by `[IsAffine T]` and `[IsAffine T']`. These are restrictions on use of
  the four predicates, not extra assumptions in the node's core notions.

The parenthetical consequences in the node do not add hypotheses: nilpotent
ideal powers force surjectivity on affine spectra, and a closed subscheme of
an affine scheme is affine. Empty schemes and zero ideal sheaves remain
allowed; no nonemptiness, characteristic, finiteness, or Noetherian
hypothesis is present. The arbitrary universe covers all scheme universes
allowed by the dependencies.

I independently searched Mathlib AlgebraicGeometry, `WeilConjectures/`, and
`lean/Sheaf/` with `rg`, and ran `msearch.py` LeanFinder/Loogle searches for
thickening, first-order thickening, square-zero ideal, and nilpotent ideal
predicates. The only existing occurrence is informal documentation of a
closed immersion with `IsNilpotent i.ker`; no declaration states these four
notions. Therefore no existing declaration supersedes this module.

No mismatch was found and no Lean change was required in this second
reading. The module compiled cleanly with `scompile.py`.
