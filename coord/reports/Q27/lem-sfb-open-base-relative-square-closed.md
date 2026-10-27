## Worker report

The module `Sheaf.AlgebraicGeometry.OpenBaseRelativeSquareClosed` states
`AlgebraicGeometry.openBaseRelativeSquareClosed`, with one `sorry` and no definitions.
No node statement, dependency list, proof or other existing field is changed.

Source read: `literature/stacks-project/spaces-more-morphisms.tex`, lines 11566–11651,
Tag 05X9, `lemma-where-unramified-universally-injective`. Its first proof sentence says
that restriction to an open base preserves assumptions (2) and (3), ordinary closedness
of the source and relative-square maps. Its following paragraph uses base change of the
diagonal. The node supplies the detailed fibre-product universal-property argument,
which the theorem's docstring reproduces in its six steps. Local finite type belongs
to the larger lemma, but is not needed or asserted for this restriction/comparison
lemma, and has not been added. The source's algebraic-space statement is used only
for the scheme specialization that the DAG item explicitly states.

Hypotheses and clauses, in statement order:

- Schemes A, B, C are `{A B C : Scheme.{u}}`; their three morphisms are the explicit
  binders `p`, `q`, `f`. Commutativity `q ∘ f = p` is `hf : f ≫ q = p`.
- D is literally `pullback f f`; p₂ is `pullback.fst f f ≫ p`; δ is
  `pullback.diagonal f`. These are Mathlib objects, with no aliases or private copies.
- The first conjunct quantifies over every `T : Scheme.{u}` and `h : T ⟶ B`.
  A_T and C_T are `pullback p h` and `pullback q h`. The existential `fT` is uniquely
  specified by its two projection equations, with A-projection `pullback.fst p h ≫ f`
  and T-projection `pullback.snd p h`. Thus it is exactly the induced map.
- D_T is `pullback fT fT`. The isomorphism `e` has target
  `pullback (pullback.fst f f ≫ p) h`, exactly D ×_B T. Its next three equations
  give both A-projections and the T-projection. They uniquely specify the canonical
  isomorphism, since maps into each of the two nested pullbacks are determined by
  their projections. No arbitrary morphism is substituted for a canonical map.
- The next two equations specify the D- and T-projections of
  `pullback.diagonal fT ≫ e.hom`: they are the old diagonal after the A-projection,
  and the original T-projection. These characterize precisely the base change of δ.
  They assert equality of morphisms, not merely an isomorphism of their source objects.
- The second conjunct quantifies over all `W : B.Opens`, represented by the open
  subscheme `W.toScheme` with inclusion `W.ι`. It constructs the induced `fW` by
  the same two projection equations. The fixed Mathlib isomorphisms
  `pullbackRestrictIsoRestrict p W` and `pullbackRestrictIsoRestrict q W` identify
  A_W and C_W with the two inverse-image opens, over A and C respectively; both
  inclusion equations are expressly recorded.
- The equation using `morphismRestrict p W` identifies the map A_W → W with the
  restriction of p. The existential `dW` identifies D_W with the inverse-image open
  of p₂; its two inclusion/projection equations specify its map to D by both
  D-projections. Its next equation identifies D_W → W with `morphismRestrict p₂ W`.
  These equations determine `dW` uniquely. Equivalently it is the first conjunct's
  `e` followed by `pullbackRestrictIsoRestrict p₂ W`; uniqueness ensures the same
  relative square and diagonal are being identified in the two conjuncts.
- The implication assumes exactly `IsClosedMap p.base` and `IsClosedMap p₂.base`,
  and concludes `IsClosedMap` for precisely those two restricted structure maps.
  There is no `UniversallyClosed` assumption or assertion of closedness over
  arbitrary base changes. Under the displayed scheme isomorphisms these are
  exactly the two maps A_W → W and D_W → W in the node.
- A morphism h factoring through W is expressed by an arbitrary
  `k : T ⟶ W.toScheme`, with h written `k ≫ W.ι`. This covers every such h and
  every factorization; it imposes no new restriction on the original arbitrary h.
- The isomorphisms `a` and `c` have precisely the two iterated-pullback sources
  A_W ×_W T and C_W ×_W T and the direct-pullback targets A ×_B T and C ×_B T.
  Their four equations specify the A-, C- and T-projections, so they are the
  canonical iterated-base-change identifications.
- `F` and `g` have the direct and iterated induced-map types. Each is uniquely
  specified by its two projection equations. The equation `g ≫ c.hom = a.hom ≫ F`
  identifies those induced morphisms.
- The final isomorphism `d : pullback g g ≅ pullback F F`, with its two specified
  projections, identifies their relative self-products. The final equation
  `pullback.diagonal g ≫ d.hom = a.hom ≫ pullback.diagonal F` identifies the actual
  diagonals. This includes their domains and their two relative-square projections.

Existential maps appear only inside the theorem's conclusion, with full projection
characterizations and asserted existence. There is no chosen data definition, extra
input map, `Nonempty` choice, `let`, local notation, or auxiliary postponed theorem.
The projection characterizations are the exact universal-property meaning of
“canonical” in the node and its proof, and imply uniqueness without strengthening it.

Dependencies read and used:

- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`, `AlgebraicGeometry.Scheme`
  (lines 36–47) and `AlgebraicGeometry.Scheme.Hom` (lines 73–75).
- `def-pc-fibre-product`: `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`,
  `CategoryTheory.Limits.pullback`, `.fst`, `.snd`, `.lift`, `.map` (lines 94–132,
  272–278). Scheme pullback existence is exposed by the additional public import
  `Mathlib.AlgebraicGeometry.Pullbacks`; it is not an added hypothesis.
- `def-weil-open-immersion`: `Mathlib.AlgebraicGeometry.OpenImmersion`,
  `AlgebraicGeometry.IsOpenImmersion` (lines 35–39). Opens are represented by the
  library's open subschemes, rather than arbitrary maps assumed to be open immersions.
- Proof dependency `lem-weil-pbc-open-preimage-fibre-product` has status `mathlib`
  and `mathlib_match` equal to `AlgebraicGeometry.isPullback_morphismRestrict` in
  `Mathlib.AlgebraicGeometry.Restrict` (lines 587–590). Its `lean` is absent and is
  not required. Read the exact signature and the accompanying
  `pullbackRestrictIsoRestrict`, its projection equations, and `morphismRestrict`
  (lines 552–590). This module is public because the statement itself uses these
  canonical identifications and restrictions.
- `Mathlib.CategoryTheory.Limits.Shapes.Diagonal` supplies the actual
  `CategoryTheory.Limits.pullback.diagonal` (lines 35–44), the unique map with
  both projections the identity. This is the diagonal, not a replacement notion.

Edge cases checked before drafting: W empty gives empty open inverse images and
closed empty-to-empty restricted maps; W = top recovers the original triangle.
Empty A or C causes no obstruction to the universal-property maps. Arbitrary T,
including empty T and h = identity, is included; so are identity f and non-monic f.
No nonemptiness, finite type, separation, characteristic, or closedness condition
is placed on the first or iterated comparisons. Closedness is required only in its
own implication, over every open W. All schemes live in the same arbitrary explicit
universe `u`, as in Mathlib's scheme category; there is no independent smaller test
universe. `set_option autoImplicit false` forbids auto-bound variables.

Searches run with `msearch.py Q27 lem-sfb-open-base-relative-square-closed`:

- LeanFinder query: “Relative self fibre products of schemes commute with base change
  compatibly with diagonals; restriction to an open base preserves closed maps”.
  Eight hits, including `Scheme.Pullback.diagonalRestrictIsoDiagonal`,
  `isPullback_morphismRestrict`, and universally-closed projection theorems. The
  first concerns restrictions to pullback covers, the second only one restriction
  square, and the others require stronger closedness. None states the whole item.
- Loogle query: `"pullback", "diagonal"`. Twelve hits including
  `pullback.diagonalObj`, `pullback.diagonal`, and their projection identities;
  these supply the existing diagonal notion but not this result.
- Grep query: `IsClosedMap.*restrict|relative.*[Ss]quare|diagonal.*[Bb]ase[Cc]hange`.
  Twenty hits, including `IsClosedMap.restrictPreimage` in
  `Mathlib/Topology/LocalAtTarget.lean:68`; this covers the topological closedness
  clause alone, not the relative-square or diagonal identifications.
- LeanSearch query: “Base restriction of a triangle of schemes identifies relative
  self products and diagonals and preserves closed maps over an open subset of the
  base”. Eight hits led by `morphismRestrict`, `Scheme.Hom.resLE`, and restriction
  theorems for separated/proper morphisms; no whole-result match.
- `rg` of `lean/WeilConjectures` and `lean/Sheaf` for
  `openPreimage|open_preimage|relativeSquare|relative_square` found unrelated
  topological preimage lemmas and open-cover descent helpers, no such result.
  `grep -rn` for the item id in `lean/WeilConjectures` returned no match.
  `rg` for `openBaseRelativeSquareClosed` in Mathlib, the upstream-name index,
  `lean/WeilConjectures`, and `lean/Sheaf` returned no match.
- Direct Mathlib searches/readings found the existing pullback maps, diagonal and
  restriction isomorphisms described above. No new notion or node is needed.

Compilation uses only the prescribed `scompile.py`. The initial attempt diagnosed
missing publicly exposed scheme pullback instances and one long docstring line;
adding the public `Mathlib.AlgebraicGeometry.Pullbacks` import and wrapping that
line fixed both. The subsequent compile passed in sandbox and library modes.
No statement dispute or source correction was needed.

## Second reading by Q27

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
