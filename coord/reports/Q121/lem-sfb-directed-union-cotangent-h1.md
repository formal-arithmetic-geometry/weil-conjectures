## Worker report

The module `Sheaf.RingTheory.H1CotangentDirectedUnion` states
`Algebra.H1Cotangent.directed_union`, with its sole proof `sorry`. It defines no
new notion. Only the item's `lean` field changes; its statement, dependencies,
and accepted four-step proof remain verbatim. There is no statement dispute.

Source read: `literature/stacks-project/algebra.tex`, Tag 07BQ,
`lemma-colimits-NL`, lines 35556–35578. The source constructs the canonical
polynomial presentation, identifies its polynomial ring and evaluation kernel
with their filtered colimits, and concludes continuity of the two-term complex.
The node supplies the elementwise expansion for constant base and injective
subalgebra maps. The module docstring records all four steps, including the
partial-derivative test and finite sum of products witnessing the zero relation.

Hypotheses and clauses are rendered as follows:

- The commutative-ring map `R → S` is `[CommRing R] [CommRing S] [Algebra R S]`.
  Every ring map gives such an algebra structure; injectivity, flatness, and
  finite type are not assumed. The independent universes `u` and `v` allow rings
  of arbitrary sizes.
- The nonempty family of R-subalgebras is `(ι : Type w) [Nonempty ι]
  (A : ι → Subalgebra R S)`. Repetition of the same subalgebra at different
  indices is allowed. An arbitrary index universe is harmless here: the
  conclusion is elementwise and no category-theoretic colimit is constructed.
- Directedness under inclusion is `hdir : Directed (· ≤ ·) A`; for each pair of
  indices this gives a member containing both associated subalgebras. No order
  or monotonicity on the indexing type is imposed.
- Having union S is `hunion : ∀ s : S, ∃ i : ι, s ∈ A i`. Since the members are
  already subalgebras of S, this is exactly the stated union condition.
- For each algebra D, `H1Cotangent R D` unfolds to
  `(Algebra.Generators.self R D).toExtension.H1Cotangent`.
  `Generators.self` has variable set D, evaluation on the identity labeling,
  and section `MvPolynomial.X`; its polynomial ring is `MvPolynomial D R`.
  `Extension.H1Cotangent` is `LinearMap.ker` of `Extension.cotangentComplex`.
  The latter has domain the evaluation-kernel conormal module and target
  `D ⊗[MvPolynomial D R] KaehlerDifferential R (MvPolynomial D R)`;
  `cotangentComplex_mk` sends a representative f to `1 ⊗ D f`. Thus this is
  exactly the node's T_1, rather than a replacement by another homology model.
- Clause (i) is the first conjunct, `∀ h : H1Cotangent R S, ∃ i hᵢ, ... = h`.
  Its map `H1Cotangent.map R R (A i) S` uses the canonical subalgebra inclusion
  into S and identity on R.
- Clause (ii) is the second conjunct. For every initial i and h, its hypothesis
  is exactly that the same map into S sends h to zero. Its conclusion supplies
  `j` and `hij : A i ≤ A j`, then says the map from i to j sends h to zero.
  The explicit instance `(Subalgebra.inclusion hij).toRingHom.toAlgebra` fixes
  that map to the actual inclusion. `IsScalarTower.of_algebraMap_eq'` applied
  to its `AlgHom.comp_algebraMap.symm` expresses compatibility with R; this is
  existing structural evidence, not an additional hypothesis or postponed lemma.
- `H1Cotangent.map` is the `Extension.H1Cotangent.map` of
  `Generators.defaultHom`. For canonical self-presentations its variable
  assignment is `X ∘ algebraMap`, so inclusion sends the variable labeled a
  to the variable labeled by that same element in the larger subalgebra.
  `Cotangent.map_mk` and `H1Cotangent.map_apply_coe` give exactly the representative
  formula stipulated by the node. No arbitrary comparison map is quantified.

Dependency declarations read and used:

- `def-weil-pbc-mv-polynomial-ring`: `MvPolynomial` and `MvPolynomial.algHom_ext`
  in `Mathlib.Algebra.MvPolynomial.Basic`, lines 80–83 and 432–438;
  `MvPolynomial.aeval` in `Mathlib.Algebra.MvPolynomial.Eval`, lines 590–614.
  The polynomial construction is used through `Generators.self`.
- `def-weil-pbc-kahler-differentials`: `KaehlerDifferential`,
  `KaehlerDifferential.D`, `KaehlerDifferential.linearMapEquivDerivation` in
  `Mathlib.RingTheory.Kaehler.Basic`, lines 143–157, 195–208, and 325–334.
  These are exactly the recorded definitions used by the cotangent differential.
- `lem-weil-pbc-nl-presentation-h1-functoriality`: its Mathlib match needs no
  repair. `Algebra.Extension.H1Cotangent.map`, `.map_eq`, `.map_id`, `.map_comp`
  in `Mathlib.RingTheory.Extension.Cotangent.Basic`, lines 378–418, implement
  the maps and three laws. Read also `Extension.Hom`, `.ofAlgHom`, and
  `Cotangent.map`, `.map_mk` in `Mathlib.RingTheory.Extension.Basic`,
  lines 196–249 and 459–485; `CotangentSpace.map` and `.map_cotangentComplex`
  in the cotangent module, lines 160–208; `Generators.self`, `.Hom`,
  `.defaultHom`, `.Hom.toExtensionHom` in `Mathlib.RingTheory.Extension.Generators`,
  lines 166–182, 398–423, 464–468, 595–605. The chosen map is the existing
  `Algebra.H1Cotangent.map`, defined at lines 560–570 of the cotangent module.
- Proof dependency `lem-weil-pbc-polynomial-ring-kahler-basis-any-variables`:
  `KaehlerDifferential.mvPolynomialBasis`, `.mvPolynomialBasis_repr_apply`,
  `.mvPolynomialBasis_apply` in `Mathlib.RingTheory.Kaehler.Polynomial`,
  lines 58–99. Its module is imported for the deferred proof.

Edge cases checked before writing: a singleton family equal to S gives the
identity maps and both clauses; the zero ring and noninjective R → S are allowed;
finite support can be empty and the ideal-square witness can be an empty sum;
nonemptiness supplies a stage in those cases. No finite-generation, domain,
characteristic, or nonzero condition occurs. Clause (ii) allows j = i, permits
duplicate family entries, and never assumes that maps on T_1 are injective.

Searches run with `msearch.py Q121 lem-sfb-directed-union-cotangent-h1`:

- `leanfinder`: “First cotangent homology commutes with directed unions of
  subalgebras; every class descends and a zero class vanishes at a later stage”.
  Eight hits: `Algebra.H1Cotangent.map`, `Generators.H1Cotangent.δ_eq`,
  `Extension.h1Cotangentι`, and extension cotangent/cotangent-space mapping
  lemmas. None states the directed-union result.
- `loogle`: `"H1Cotangent"`. Twelve hits, including the two H1 definitions,
  presentation maps and equivalences, and finite-generation results. No match
  for both clauses.
- `grep`: `H1Cotangent.*(colimit|[Dd]irect)|colimit.*H1Cotangent`. Zero hits.
- `leansearch`: “First cotangent homology classes descend along directed unions
  of subalgebras and vanish at some stage if zero in the union”. Eight hits:
  formal smoothness vanishing, H1 definitions/maps, `Ideal.mapCotangent`,
  a standard-smooth coordinate criterion, and the formally-etale criterion;
  none states this result.
- Direct `rg` in both `lean/WeilConjectures` and `lean/Sheaf` for
  `H1Cotangent.*(colimit|[Dd]irect)|directed.*[Cc]otangent|h1Cotangent_directed`:
  only a prose reference in `LocallyDenseCotangentH1.lean`; its existing
  sectionwise module maps were read, and it contains no directed-union theorem.
- Item-id search in `lean/WeilConjectures`: zero hits. Search in
  `dag/lean_names_upstream.json` for the homology/colimit pattern: zero hits.
  Final full-name search `H1Cotangent.directed_union` in Mathlib, both project
  Lean roots, and the upstream name index: zero hits before delivery.

Validation: the delivered module compiled cleanly with the prescribed
`scompile.py` server wrapper. All universes and variables are explicitly bound;
there are no local notations, local instances, helper definitions, or hidden
choice constructions. The one deferred theorem has the node's complete proof
in its declaration docstring.

## Second reading by Q121

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
