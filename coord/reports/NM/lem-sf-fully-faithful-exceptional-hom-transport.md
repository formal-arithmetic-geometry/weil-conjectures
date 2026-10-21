## Worker report

Item: `lem-sf-fully-faithful-exceptional-hom-transport` (NM, stage 2).

The module `Sheaf.CategoryTheory.FullyFaithfulExceptionalHomTransport` supplies
`CategoryTheory.ExceptionalHomTransport.homMap`, the actual four-arrow composite;
`CategoryTheory.ExceptionalHomTransport.originMap`, the actual comparison-unit map;
and the statement `CategoryTheory.ExceptionalHomTransport.fullyFaithful_transport`.
The latter is the sole theorem and its entire proof is `sorry`. Both maps have real
data and are helpers of this node, not separately chosen comparisons. No new node,
dependency repair, or statement correction is needed. Only the item's `lean` field
changes. The three declarations are all recorded in `lean.declarations`.

Hypotheses and objects, clause by clause:

- The four locally small categories are `Xe`, `Te`, `Xp`, `Tp`, each a `Type` with
  `Category.{v} ...`. There are eight explicitly declared, independent object and
  morphism universes. This is the recorded Mathlib realization of
  `def-nagata-category`; no equality of universes, smallness class, nonemptiness,
  abelian structure, or existence of limits is assumed.
- The comparison functors are `(CZ : Xe ⥤ Xp)` and `(CT : Te ⥤ Tp)`.
  `[CZ.Full] [CZ.Faithful] [CT.Full] [CT.Faithful]` mean, respectively, surjectivity
  and injectivity of their maps on each Hom set, exactly the node's full
  faithfulness assumptions.
- The functors `(Fe : Xe ⥤ Te) (Ge : Te ⥤ Xe) (R : Tp ⥤ Te) (Fp : Xp ⥤ Tp)`
  have the stated domains and codomains. `(adjT : CT ⊣ R)` and
  `(adjE : Fe ⊣ Ge)` are the specified adjunctions, not assertions of the mere
  existence of some adjunction. Mathlib's `Adjunction.homEquiv` is the natural
  Hom bijection of that very unit-counit adjunction. Its inverse recovers the
  given counit from the identity; `mkOfHomEquiv` is the recorded equivalence
  from natural Hom-bijection data to this presentation.
- The given comparison is `(b : Fe ⋙ CT ≅ CZ ⋙ Fp)`. Mathlib composes functors
  in diagram order, so its component has source `CT.obj (Fe.obj H)` and target
  `Fp.obj (CZ.obj H)`, exactly the displayed `b_H`.
- `Gp` is written directly as `(R ⋙ Ge ⋙ CZ)`; this is exactly `CZ Ge R` in
  the node's function-composition convention. The specified `j` and `mu^e`
  are `adjT.unit` and `adjE.counit`.

The construction and every conclusion:

- For `H : Xe`, `L : Tp`, and `q : Fp.obj (CZ.obj H) ⟶ L`, `homMap` first
  forms `b.hom.app H ≫ q`, then applies
  `adjT.homEquiv (Fe.obj H) L`, then `adjE.homEquiv H (R.obj L)`, and finally
  `CZ.map`. Thus the middle arrows are exactly those of the supplied
  adjunctions and the map is definitionally the prescribed composite.
- The first conjunct says `Function.Bijective (homMap CZ adjT adjE b H L)`
  for every `H,L`. Bijectivity is a conclusion rather than an extra hypothesis.
- The second conjunct is naturality in `H`: transport of
  `Fp.map (CZ.map a) ≫ q` equals `CZ.map a ≫ homMap ... q` for every
  `a : H' ⟶ H` and every `q`.
- The third conjunct is naturality in `L`: transport of `q ≫ s` equals
  `homMap ... q ≫ (R ⋙ Ge ⋙ CZ).map s` for every `s : L ⟶ L'`.
- `originMap CZ Ge adjT N` is exactly `CZ.map (Ge.map (adjT.unit.app N))`.
  It is a public transparent abbreviation so the standard Mathlib unit-is-iso
  and functor-map-is-iso instances can construct the inverse used in the
  statement; no extra invertibility assumption or postponed data is involved.
  The `∀ N` conjunct explicitly asserts `IsIso` of this origin map.
- Its next clause is the precise evaluation
  `homMap ... (b.inv.app (Ge.obj N) ≫ CT.map (adjE.counit.app N)) = originMap ... N`.
  The order of these two factors is the node's `CT(mu) ∘ b^{-1}`.
- The `∀ H q` clause identifies the entire normalized chain:
  `homMap ... q ≫ inv (originMap ... N)` equals
  `CZ.map (adjE.homEquiv H N (CT.preimage (b.hom.app H ≫ q)))`.
  `CT.preimage` is the inverse to the fully faithful map on Hom sets;
  faithfulness makes its unique preimage independent of the implementation's
  choice. This clause compares the actual maps, rather than just asserting
  that some equivalence exists.
- The next equivalence says, for every candidate `q`, that its transported
  value equals `o_N` if and only if `q` equals the displayed transported
  counit. Together with the evaluation this is precisely the unique-preimage
  assertion.
- The last equivalence expresses the final identity-preimage interpretation:
  after postcomposition with `inv o_N`, the value is the identity on
  `CZ.obj (Ge.obj N)` if and only if the input is the same transported counit.
  Every Hom source in the entire statement is `CZ.obj H` for `H : Xe`.
  There is no extension to arbitrary objects of `Xp` and no ambient adjunction
  assumption or conclusion.

Dependency declarations and source reading:

- `def-nagata-category` is a Mathlib leaf, whose `mathlib_match` is
  `CategoryTheory.Category`, `Mathlib.CategoryTheory.Category.Basic`.
  I read its docstring, `CategoryStruct` data and the three category laws.
- The proof dependency `lem-weil-pbc-adjunction-of-natural-bijection` records
  `CategoryTheory.Adjunction.mkOfHomEquiv` in
  `Mathlib.CategoryTheory.Adjunction.Basic`. I read its complete signature,
  `CoreHomEquiv`, the unit/counit construction, `homEquiv`, and the formulas
  `homEquiv_unit` and `homEquiv_counit`.
- The proof dependency `lem-sp-adjunction-unit-fully-faithful-left` records
  `CategoryTheory.Adjunction.unit_isIso_of_L_fully_faithful` in
  `Mathlib.CategoryTheory.Adjunction.FullyFaithful`. I read its signature and
  component instance. This module is publicly imported because its instances
  also appear in the statement's construction of `inv o_N`; it publicly
  imports `Adjunction.Basic`, including the recorded category dependency.
- I read `Functor.Full`, `Functor.Faithful`, `Functor.preimage`, and
  `Functor.FullyFaithful.homEquiv` in
  `Mathlib.CategoryTheory.Functor.FullyFaithful`.
- I opened the local source `literature/stacks-project/categories.tex` at
  `definition-adjoint` (0037), `lemma-adjoint-fully-faithful` (07RB), and
  `lemma-compose-counits` (0DV0), including their proofs. The theorem's
  docstring carries all five proof steps of the node and names its two
  proof dependencies.
- There is no repair note for this item.

Searches for existing declarations:

- `msearch.py ... leanfinder` query: "Natural Hom bijections transported through
  fully faithful functors using two adjunctions and a natural isomorphism;
  normalization at the counit". Eight results included
  `Adjunction.restrictFullyFaithful_homEquiv_apply`, its counit-map theorem,
  `Adjunction.Triple.fullyFaithfulEquiv`, and `conjugateEquiv`. I read
  `Mathlib.CategoryTheory.Adjunction.Restrict` in full: it takes an already
  given ambient adjunction and two commuting squares, unlike this item.
- `msearch.py ... loogle` query:
  `CategoryTheory.Adjunction.homEquiv, CategoryTheory.Functor.FullyFaithful.homEquiv`.
  Zero hits for the combined query.
- `msearch.py ... leansearch` query: "Composite of adjunction Hom equivalences
  with a fully faithful functor, with evaluation at the counit and comparison
  unit". Eight hits, including `Adjunction.comp`, `comp_homEquiv`,
  `homEquiv`, `homEquiv_apply`, and `mkOfHomEquiv`; these supply constituent
  maps and adjunction construction, not this full statement.
- `msearch.py ... grep` query:
  `restrictFullyFaithful|homEquiv_counit|unit_isIso_of_L_fully_faithful`,
  subdirectory `CategoryTheory/Adjunction`. Twenty-three hits; these are
  the restriction construction and constituent formulas, already examined.
- `rg` on both `lean/WeilConjectures` and `lean/Sheaf` for
  `exceptionalHomTransport|fullyFaithful.*[Hh]om|[Hh]om.*[Tt]ransport|exceptional.*[Tt]ransport`
  found related specialized transport statements but no general four-category
  theorem. A focused follow-up for
  `fullyFaithfulExceptional|exceptionalHomTransport|fullyFaithful.*[Hh]omTransport|fully.faithful comparison functors`
  had no hits. The exact node-id search with `grep -rn` in
  `lean/WeilConjectures` had no hits.
- I checked proposed declaration names with `rg` in
  `dag/lean_names_upstream.json`, Mathlib, `lean/WeilConjectures`, and
  `lean/Sheaf`: no existing `CategoryTheory.ExceptionalHomTransport` namespace
  or these declarations. A broad `exceptionalOriginMap` query did find
  `AlgebraicGeometry.ProEtale.BoundaryComparison.exceptionalOriginMap`.
  I opened that declaration and `homTransport` and `CounitComparison` in
  `Sheaf.Paper.BoundaryExceptionalComparisonData`: those are specialized to
  fixed derived sheaf comparison functors, rings and schemes, rather than the
  arbitrary four categories and specified adjunctions of this node. Their
  formulas are the specialization of the generic helpers here.

Edge cases checked before writing and on rereading:

- Empty categories and empty Hom sets: there is no nonemptiness or choice of
  an origin object; all conclusions are universally quantified over existing
  objects and morphisms. Empty `Xe` makes its clauses vacuous; empty `Te`
  is compatible with `R` only when its source permits such a functor.
- Zero objects and zero morphisms, when available, are allowed without any
  additive structure being imposed.
- Identity functors, identity comparisons and identity adjunctions reduce
  the formulas to the expected Hom identity and identity counit.
- A nontrivial automorphism `b`, or a different specified adjunction structure
  on the same functors, remains in every relevant formula; no canonical or
  untwisted unit/counit assumption is introduced.
- `CZ` need not be essentially surjective. Objects of `Xp` outside its image
  receive no Hom-bijection or adjunction claim.
- All four object and Hom universe pairs are independent and compile as such;
  no small-site universe identification has been imposed.

Validation: `scompile.py NM lem-sf-fully-faithful-exceptional-hom-transport`
compiled both its sandbox and library module forms cleanly (2.6 s and 2.4 s).
The first attempt failed solely to synthesize `IsIso` through an opaque named
map; making `originMap` an abbreviation exposed the same real data to the
existing Mathlib instances. All Lean lines are at most 100 characters;
`autoImplicit` is disabled; there is exactly one `sorry`, the named theorem.
No disputed statement or node fault was found.

## Second reading by NM

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
