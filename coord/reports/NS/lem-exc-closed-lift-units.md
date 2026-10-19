## Worker report

The module `Sheaf.RingTheory.ProEtale.ClosedLiftUnits` states
`Algebra.ClosedLift.isUnit_of_isUnit_toAlgHom`, with proof `sorry`. No definitions or
proofs are added, and the node changes only in `lean`.

Hypotheses and conclusion, clause by clause:

- The commutative ring A is `{A : Type u} [CommRing A]`.
- The source's ideal I is `(I : Ideal A)`.
- The source's commutative ind-etale A/I-algebra C-bar is
  `{C : Type u} [CommRing C] [Algebra (A ⧸ I) C]
  [Algebra.IndEtale (A ⧸ I) C]`. Its induced A-algebra structure is
  `[Algebra A C] [IsScalarTower A (A ⧸ I) C]`. These are the setting of the
  cited construction, not new restrictions on that setting.
- An element of H_A(C-bar) is `(h : Algebra.ClosedLift A C)`.
- Its image in C-bar is `(Algebra.ClosedLift.toAlgHom A C) h`, the retained map
  induced by the indexing cocone, not an arbitrary algebra map.
- The hypothesis that this image is invertible is
  `(hh : IsUnit (toAlgHom A C h))`.
- The conclusion that the original element is invertible is `IsUnit h`.

Dependency declarations: `def-exc-ind-etale-closed-lift` records
`Sheaf.RingTheory.ProEtale.ClosedLiftMap`, which is imported publicly. Its full source
and the group clone's exact upstream module
`WeilConjectures.RingTheory.ProEtale.ClosedLift` were read, including `Index`,
`Index.Hom`, `diagram`, `coconeC`, `Algebra.ClosedLift`, and `toAlgHom`.
The actual objects used are `Algebra.ClosedLift` and `Algebra.ClosedLift.toAlgHom`.
`Algebra.ClosedLift.map` is the recorded primary declaration for the construction's
functorial part; no functoriality is needed for this lemma.

The proof docstring carries all four node proof steps: representative in the filtered
ring colimit, extension to the principal localization, etaleness and finite presentation
of that localization, and passage of its inverse to the colimit. Stated proof leaves are
imported as ordinary imports: `Mathlib.Algebra.Category.Ring.FilteredColimits`,
`Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic`,
`Mathlib.RingTheory.Localization.Away.Basic`, and `Mathlib.RingTheory.Etale.Basic`.
These supply the concrete representative lemmas, localization construction and universal
property, and etale finite-presentation/localization facts. The filteredness node has no
Lean record yet; the already imported construction contains the upstream
`Algebra.ClosedLift.isFiltered_index` instance. No unavailable sibling module is invented.

Edge cases checked: no `Nontrivial` assumption excludes zero rings. If C is the zero ring,
the zero algebra is an indexing stage, and the colimit is zero; unit reflection still holds.
I = bottom and I = top are allowed. Neither C nor A needs to be a field or Noetherian.
The zero element and the element one are included; the hypothesis on zero is possible only
when its image ring is zero, which the construction handles. There is no empty-index or
finite-dimensional assumption. The single universe matches the existing closed-lift and
ind-etale declarations and can be raised jointly for any pair of input ring sizes.

Searches made with `msearch.py NS lem-exc-closed-lift-units`:

- `leanfinder`: "An element of the colimit of etale A algebras mapping to C is a unit if
  its image in C is a unit" returned eight supporting standard-etale/ring-hom results,
  including `StandardEtalePresentation.hasMap` and `RingHom.etale_algebraMap`;
  none states this lemma.
- `loogle`: `IsUnit, AlgHom` returned twelve hits, including
  `IsLocalization.Away.liftAlgHom`; none states unit reflection for this colimit.
- `grep`: `ClosedLift|closedLift|closed_lift` across Mathlib returned no hits.
- `leansearch`: "An element of an ind etale closed lift is a unit if its image is a unit"
  was attempted; the service returned Internal Server Error (no result relied on).
- `rg` for `ClosedLift|closedLift|closed_lift` in upstream `WeilConjectures` and
  project `lean/Sheaf` found the construction, its functorial extension, and downstream
  cover uses, but no unit-reflection declaration. Searching the item id upstream found
  no occurrence. Searching `dag/lean_names_upstream.json` found no additional match.
- `rg` for the proposed full declaration's final name across upstream, project Lean,
  and the upstream-name index found no collision.

Read the blueprint statement, its construction, and the group framework isolation notes.
No statement correction, missing notion, dependency repair, or disputed statement arose.

Validation: `scompile.py NS lem-exc-closed-lift-units` compiled the delivered module cleanly
on the server (1.4 seconds, nice 19, two threads, 60-second per-file limit), after privately
compiling its two side-only dependencies. No local compiler or library build was run.

## Second reading by NS

I independently opened the immutable node, its blueprint source and the source of
`def-exc-ind-etale-closed-lift`, then matched them with the delivered theorem.
The complete list of objects, hypotheses and conclusions is:

- A commutative ring A: `{A : Type u} [CommRing A]`. Exact.
- An arbitrary ideal I of A: `(I : Ideal A)`. Exact; no properness assumption.
- A commutative ind-etale A/I-algebra C-bar: `{C : Type u} [CommRing C]`,
  `[Algebra (A ⧸ I) C]` and `[Algebra.IndEtale (A ⧸ I) C]`. Exact.
- Its A-algebra structure is induced through A/I: `[Algebra A C]` and
  `[IsScalarTower A (A ⧸ I) C]`. The tower enforces precisely this compatibility;
  it is not an independent extra restriction on the source's algebra.
- The constructed algebra H_A(C-bar): `Algebra.ClosedLift A C`. Exact.
- An arbitrary element of that algebra: `(h : Algebra.ClosedLift A C)`. Exact.
- Its retained image in C-bar: `toAlgHom A C h`. This is the canonical colimit
  descent of the factorization cocone, not an unspecified algebra map. Exact.
- The sole element hypothesis, invertibility of the image:
  `(hh : IsUnit (toAlgHom A C h))`. Exact.
- The whole conclusion, invertibility of the original element: `IsUnit h`.
  Exact, with no extra conjunction, converse, or existential restriction.

I read `ClosedLiftMap.lean` and the exact group-clone upstream `ClosedLift.lean`,
including the signatures and bodies of `Index`, `Index.Hom`, `diagram`, `coconeC`,
`Algebra.ClosedLift`, and `toAlgHom`. The construction is a real colimit in
`CommAlgCat A`; its data is not sorry. The upstream index uses arbitrary relation
ideals of finite-variable polynomial rings, with the etale condition. Etaleness
implies finite presentation, so those ideals admit finite generating lists; this
is the same indexing category up to the redundant choice of those lists, as the
recorded dependency explains. All compatible algebra maps remain morphisms.
The dependency's additional `map` is induced by postcomposition and is not used
in this lemma. I also opened `IndPrincipalZariski.lean` and the imported upstream
`Algebra.IndEtale` definition: the latter is a filtered colimit of etale algebras,
and `Algebra.Etale` includes finite presentation. There is no missing notion,
private copy, new node or dependency module in this delivery.

The source is the blueprint node, not a Stacks theorem with an unstated ambient
hypothesis. I additionally read Stacks algebra.tex at 00CP, 00U1 and 00U2,
including the preceding localization context. They apply to arbitrary commutative
rings; neither Noetherianity nor a field hypothesis occurs. The proof docstring
matches all four DAG steps: a representative in the filtered colimit, extension
to principal localization, etaleness and finite presentation of that stage, and
its inverse mapped to the colimit. I checked the proof-dependency records and
opened the concrete representative, localization lift, etale finite-presentation
and localization declarations. The plain Mathlib imports expose those leaves;
the construction already exposes upstream `isFiltered_index`. No nonexistent
module is imported for the still-unrecorded filteredness node.

Edge cases: zero A and zero C are permitted, as are I = bottom and I = top.
When C is zero, the zero algebra is an available etale finitely presented stage,
and the argument sends each representative to zero there; H is zero too.
Thus h = 0 is covered even when its image is a unit. The indexing category is
not empty (the identity A-algebra maps to C), and presentations with n = 0 are
allowed. No characteristic is fixed and no scheme nonemptiness is assumed.
All variables and the universe u are explicitly bound. The common universe is
the existing construction's and IndEtale's universe; cumulativity permits choosing
a common larger universe for any two ring sizes. No lower-universe test-object
quantifier or bound on cardinality has been introduced.

Independent searches used different words from the worker:

- `msearch.py ... leanfinder`: "The canonical map from the etale approximation of
  an algebra reflects invertible elements" returned eight standard-etale
  presentation results, including `StandardEtalePresentation.hasMap` and
  `StandardEtalePair.homEquiv`; none states unit reflection for H.
- `msearch.py ... loogle`: `IsUnit, RingHom, _ → _` returned twelve results,
  including `RingHom.isUnit_map` (the opposite implication for arbitrary maps)
  and localization lift results; no exact match.
- `msearch.py ... grep`: `reflect.*[Uu]nit|isUnit.*[Cc]olimit|[Cc]olimit.*isUnit`
  returned general local-ring and unrelated category-theory results, no match.
  Direct `rg` over Mathlib's RingTheory and Algebra/Category confirmed only the
  local-ring characterization, which needs different objects and hypotheses.
- Direct `rg` over upstream WeilConjectures, project lean/Sheaf and the upstream
  name index for `ClosedLift|closedLift|closed_lift|isUnit_of_isUnit_toAlgHom`
  found the existing construction, its functorial extension and downstream cover
  applications, but no duplicate of this statement or collision with its name.

Verdict: no mismatch found. I preserved the Lean module and node record verbatim;
only this independent reading was appended. The module has one theorem with
proof `sorry`, no new definition or proved assertion, compliant source/proof
 docstrings and lines within 100 characters. The node's `lean.statement` is
verbatim the file signature before `:= sorry`.

Validation: independently compiled the delivered module with `scompile.py` on
the server: ClosedLiftUnits 1.4 seconds, with side dependencies
IndPrincipalZariski 1.3 seconds and ClosedLiftMap 1.8 seconds. All passed without
warnings, using nice 19, two threads and the 60-second per-file limit.
