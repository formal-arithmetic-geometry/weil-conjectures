## Worker report

The module `Sheaf.Algebra.Homology.GoodCoresolutionCohomologyRows` states
`CochainComplex.GoodCoresolution.homology_rows_exact`, with its sole proof `sorry`.
No definition, auxiliary theorem, new node, dependency repair, or statement correction
is needed. The node is unchanged except for `lean`.

Hypothesis and clause correspondence:

- The size convention is rendered by explicit `universe u` and `AddCommGrpCat.{u}`.
  The dependency `def-weil-size-convention` has a convention-only record with null
  module/declaration: it expressly tells citers to bind universes directly. There
  is no site, derived category, or size-dependent construction in this statement.
- `M : CochainComplex AddCommGrpCat.{u} ℤ` and
  `E : ℕ → CochainComplex AddCommGrpCat.{u} ℤ` are exactly the integer-indexed
  complexes of abelian groups. Mathlib packages additive differentials, their
  degree shift, and the square-zero identities in these objects.
- `u : M ⟶ E 0` and `f : ∀ i : ℕ, E i ⟶ E (i + 1)` are the specified chain
  maps, including additivity and commutation with differentials.
- Exactness of the term row is `h_inj` (injectivity on `M`), `h₀` (image of
  `u` equals kernel of `f 0`), and `h` (image of each `f i` equals kernel of
  `f (i + 1)`), all quantified over every `n : ℤ`.
- `C^n(V)` is Mathlib's `V.opcycles n`: the cokernel of the differential from
  degree `n - 1`, as confirmed by `opcyclesIsCokernel`. Its induced maps are
  `HomologicalComplex.opcyclesMap`. Exactness of this row is respectively
  `hc_inj`, `hc₀`, and `hc`, with precisely the same positions and degrees.
- `H^n(V)` is Mathlib's `V.homology n` and the induced maps are
  `HomologicalComplex.homologyMap`. The conclusion, for each integer `n`, is
  `Function.Injective (homologyMap u n)`, then `Function.Exact` of the augmented
  pair, then `∀ i : ℕ, Function.Exact` of each consecutive pair. This includes
  every position, in particular `E 0`, with no terminal surjectivity clause.
- `Function.Exact` means the outgoing zero fibre equals the incoming range;
  this is exactly the node's image-equals-kernel convention. There are no
  boundedness predicates or hidden category/acyclicity hypotheses.

The Mathlib declarations used are `CochainComplex` and its morphisms (under
`Mathlib.Algebra.Homology.HomologicalComplex`), `HomologicalComplex.opcyclesMap`
and `HomologicalComplex.homologyMap` from
`Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex`, `AddCommGrpCat` and
its abelian category instance from `Mathlib.Algebra.Category.Grp.Abelian`, and
`Function.Exact` from `Mathlib.Algebra.Exact.Basic`. The full definitions and
signatures of the homology/opcycles constructions and maps were read. All
variables are explicitly bound, and `autoImplicit` is disabled.

Source checked: `literature/stacks-project/homology.tex`, Tag 09J0,
`lemma-good-right-resolution-gives-qis`, especially its displayed infinite
cohomology row at lines 6989ff, and Tag 09IZ, the first paragraph of
`lemma-good-resolution-gives-qis`. The quotient index is shifted from the source's
`Coker(d^p)` to degree `n = p + 1`; both hypotheses quantify over all integers.
The declaration docstring carries all six steps of the node's elementary chase,
including the initial two exceptional positions.

Edge cases checked by reading the types and the element chase: the all-zero
complexes; all differentials zero (where the result reduces to term-row
exactness); `M = 0`; negative cochain degrees; the augmented position; `E 0`
(the correction uses injectivity of the augmentation); `E 1` (the correction
uses injectivity of its quotient map); and arbitrary later positions. The
horizontal family is infinite and no final surjectivity is imposed. A common
universe for the countable family imposes no mathematical restriction, by
universe enlargement. The elementary chase needs only three adjacent cochain
degrees, so unbounded complexes remain included.

Searches (2026-10-24, through the prescribed `msearch.py` wrapper):

- LeanFinder: "An exact augmented sequence of cochain complexes exact on
  differential cokernels induces exact cohomology rows" returned eight hits,
  principally group-cohomology short exact sequences, `homology_exact₁/₃`, and
  `HomologySequence.composableArrows₂_exact`. None states the infinite-row result.
- Loogle: `"homology", "Exact"` returned twelve hits, principally exactness
  of a single short complex or functorial preservation of homology, not this claim.
- Mathlib grep: `cokernel.*(homology|exact)|homology.*cokernel`, restricted to
  `Algebra/Homology`, returned 25 hits. Read
  `ShortComplex.ShortExact.homology_exact₂` in `HomologySequence.lean`: it
  requires a short exact sequence, whereas a consecutive triple here need be
  neither left injective nor right surjective. The spectral-object cokernel
  sequences likewise do not state this row theorem.
- LeanSearch: "Good right resolution exact differential cokernel rows imply
  exact cohomology rows" returned eight hits concerning cokernels, exact short
  complexes, and projective resolutions, with no exact match.
- Direct `rg` of `lean/WeilConjectures` and `lean/Sheaf` for cohomology rows,
  good coresolutions, `exact.*opcycles`, and `opcycles.*exact` found the parent
  `GoodCoresolutionProductTotal.lean`, whose proof cites this item but does not
  state it. Its existing assumptions use exactly the same `opcyclesMap` and
  `Function.Exact` encoding chosen here. Searches for this node id in
  `lean/WeilConjectures` and the proposed declaration name in Mathlib,
  `WeilConjectures`, `Sheaf`, and `dag/lean_names_upstream.json` found no match.

There is no STATEMENT-DISPUTED flag and no identified node fault. The prescribed
example `CompactObject.lean` is now a withdrawn module containing no declarations;
its node records an existing Mathlib declaration. The delivered file follows the
current module-mode convention and the adjacent good-coresolution module instead.

## Second reading by Q29

A second pass by the same worker compared the node, source, and completed file;
the dispatcher brief forbids starting another agent and reserves independent
review for the maintainer. The six hypotheses match respectively the initial
injectivity, augmented exact pair, and all subsequent exact pairs in the term
and quotient rows. The three conclusion clauses repeat precisely those positions
on cohomology. The input and output maps all come from the specified `u` and `f`,
not arbitrary replacement maps. The quotient is by incoming boundaries, not the
outgoing differential, and cochain degree remains an arbitrary integer. No
mismatch was found and no mathematical change was made during this second pass.
