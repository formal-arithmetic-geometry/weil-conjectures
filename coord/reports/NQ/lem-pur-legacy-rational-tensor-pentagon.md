## Worker report

Existing declaration, no new Lean module:
`Sheaf.Paper.ScalarExtensionComposition`,
`WeilConjectures.rationalConstructibleScalar_coherence`, lines 1464–1553.
The item's assertion is exactly its third conjunct, obtained by
`(rationalConstructibleScalar_coherence l E L i Y M j D hl).2.2 N h K`.
The binding records the complete existing declaration's signature verbatim, including
its two packaged unit equations; the projection above specifies the clause owned by
this node. Nothing is proved, restated, or changed in the library.

Source read: current blueprint
`literature/blueprint/latest/blueprint/sec-smooth-purity/sk-def-sp-scalar-extension/sk-def-sp-scalar-extension-functor.proof.md`,
step (4), and the retained older tensor construction explicitly named by the node:
`ScalarExtensionComposition.lean`, particularly the comparison definition,
`completed_comp_formula`, and `rationalConstructibleScalar_coherence`.
The existing proof first proves the ordinary tensor equation, derives and restricts it,
localizes integral Hom arrows, and then conjugates by the specified completion
comparisons. Naturality and cancellation give the completed pentagon. These are the
six steps in the node's proof: ordinary realization (step 1), ordinary sheaf tensor
pentagon (2), exact derived pasting and full restriction (3), raw tensor localization
(4), the four-factor completed comparison formula (5), and naturality/cancellation (6).

Hypothesis and clause correspondence:

- The global datum is `D : FiniteFieldDatum.{d}`. Its structure in
  `Sheaf.Paper.FiniteFieldFiber` contains `p`, positive `a`, `q = p ^ a`, the finite
  base field and its algebraic closure. The datum universe `d` is independent of `u`.
- The coefficient prime is `(l : ℕ) [Fact l.Prime]`, with `hl : l ≠ D.p`.
- The scheme is `Y : AlgebraicGeometry.Scheme.{u}`. There is no base morphism,
  finite-type, separatedness or nonemptiness assumption.
- Each of `E`, `L`, `M`, `N` is `Type u` with `[Field _]`, `[Algebra (Padic l) _]`
  and `[FiniteDimensional (Padic l) _]`. The three arrows are arbitrary
  `i : E →ₐ[Padic l] L`, `j : L →ₐ[Padic l] M`, `h : M →ₐ[Padic l] N`.
  There is no assumption that these are distinct fields or proper inclusions.
- The specified older integral category is exactly
  `boundedConstructibleDerivedCompleteIntegralCategory D l hl E Y`, read in
  `Sheaf.Paper.DerivedCompleteIntegralDetailed`. Its predicate is `IsDerivedComplete`
  and `∃ r s : ℤ, r ≤ s ∧ ∀ n : ℕ, ...`; it tests
  `intrinsicFiniteTorsionConstructible` on `(integralDerivedReduction ... n).obj K`
  and confines its support to `r ≤ i ∧ i ≤ s`. Here the positive coefficient level
  is `n + 1`, so every positive level and a single uniform interval are retained.
- `rationalConstructibleCategory D l hl E Y`, in
  `Sheaf.Paper.RationalizationKaroubi`, is literally `ScalarLocalization` of that
  older integral category at its specified uniformizer. It preserves the objects;
  no Karoubi completion is introduced.
- `T_i` is exactly `rationalScalarExtension D l hl E Y L i`. Its recorded object
  map uses `constructibleIntegralScalarExtension` and its Hom scalar action uses
  the given algebra homomorphism, as the node demands.
- `a_{j,i}` is exactly `(rationalConstructibleScalarComp l E L i Y M j D hl)`.
  This is the existing normalized comparison, rather than a freely chosen iso.
- The universal object binder is
  `K : rationalConstructibleCategory D l hl E Y`.
- The left path is
  `(rationalScalarExtension D l hl M Y N h).map
    ((rationalConstructibleScalarComp l E L i Y M j D hl).hom.app K) ≫
    (rationalConstructibleScalarComp l E M (j.comp i) Y N h D hl).hom.app K`.
- The right path is
  `(rationalConstructibleScalarComp l L M j Y N h D hl).hom.app
    ((rationalScalarExtension D l hl E Y L i).obj K) ≫
    (rationalConstructibleScalarComp l E L i Y N (h.comp j) D hl).hom.app K`.
  Mathlib's `≫` composes in the written order. The targets agree definitionally
  since `(h.comp j).comp i` and `h.comp (j.comp i)` have the same algebra-map data;
  no comparison to a separately named composite map is inserted.
- The first and second conjuncts of the existing theorem are its unit laws. The
  third conjunct is the exact pentagon requested here; it needs no unit-law
  hypothesis, intrinsic/legacy identification, or further geometric assumption.

Statement dependencies inspected, including their complete recorded signatures and
docstrings:

- `def-weil-finite-field-fiber`: `Sheaf.Paper.FiniteFieldFiber`,
  `WeilConjectures.FiniteFieldDatum` (used directly by the existing theorem).
- `def-weil-l-adic-coefficient-extension`:
  `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`,
  `Padic.finite_coefficientExtensionRing`, and its imported coefficient constructions.
  The finite-extension binders and uniformizers above reuse those constructions.
- `def-weil-derived-complete-integral-detailed`:
  `Sheaf.Paper.SfIntegralConstructible`, `sfIntegralConstructible` and
  `sfIntegralConstructibleCategory`. The record now presents the intrinsic version.
  This item's statement instead explicitly fixes the retained older category, whose
  existing declaration is read above; no equivalence of these predicates is used.
- `def-weil-rationalization-karoubi`:
  `Sheaf.Paper.SfRationalizationKaroubi`, `sfRationalConstructibleCategory`, also
  inspected with its raw `ScalarLocalization` definition. The older exact
  `rationalConstructibleCategory` is reused through the selected existing theorem.
- `lem-weil-scalar-extension-composition`:
  `Sheaf.Paper.SfScalarExtensionComposition`, `sfRationalScalarComp`, inspected with
  its normalized construction. This module publicly imports the retained
  `Sheaf.Paper.ScalarExtensionComposition`, which contains precisely the old
  `rationalConstructibleScalarComp` required by the item. No intrinsic associator
  is substituted for it. The older declaration is retained and already states the
  item, so no dependency record is overwritten and no duplicate interface is added.

Edge cases checked against the complete existing signature: identity arrows,
repeated fields (including all four fields equal), zero objects, the empty scheme,
and arbitrary schemes with no structure map to the finite field datum. None is
excluded by any hypothesis. Positive reductions run over all `n + 1`, and the
cohomological support interval is uniform in that level. The scratch validation
includes the all-identity repeated-field specialization.

Searches actually run via `msearch.py NQ lem-pur-legacy-rational-tensor-pentagon`:

- LeanFinder: “Pentagon coherence for scalar extension on the raw rational
  localization of bounded constructible derived complete integral sheaves”:
  eight results, headed by `ModuleCat.extendScalars_assoc'`,
  `ModuleCat.extendScalars_assoc` and `SheafOfModules.map_ιFree_mapFree_hom_assoc`.
  These are not the older completed/rational category theorem.
- Loogle: `ModuleCat.extendScalars_assoc`: one hit, the ordinary module-category
  coherence theorem, not an exact match to this node.
- grep of Mathlib: `rationalConstructibleScalar_coherence|extendScalars_assoc`:
  four hits in `ModuleCat/ChangeOfRings.lean` and `ModuleCat/Pseudofunctor.lean`.
- LeanSearch: “Pentagon coherence for scalar extension functors on derived
  constructible sheaves”: eight hits headed by the same ordinary module lemmas
  and `CommRingCat.moduleCatExtendScalarsPseudofunctor_mapComp`.
- Direct `rg` over `lean/WeilConjectures` and `lean/Sheaf` for
  `rationalConstructibleScalar_coherence|lem-pur-legacy-rational-tensor-pentagon`:
  the exact retained theorem is at `Sheaf/Paper/ScalarExtensionComposition.lean:1474`.
  `AlgebraicallyClosedCoefficients.lean:91` already uses the exact `.2.2 N h K`
  projection before transporting to named coefficient-map composites.
  Broader `legacy.*pentagon|rational.*[Pp]entagon` search found the same coherence
  interface, not an additional definition. The literal item id has no declaration
  in the upstream `WeilConjectures` tree.

No new nodes, dependency modules, statement correction, or disputed statement.
Only the item's `lean` record changes. Existing proofs may rest on other postponed
results; this is a stage-2 binding, not a claim of axiom-free proof completion.

## Second reading by NQ

A second pass by the same worker, rather than an independent worker: this dispatch
explicitly forbids starting other agents. I reopened the node and existing theorem
and checked every binder and both sides of the third conjunct against the item.
The full record deliberately contains the verbatim packaged signature, while its
note and this report pinpoint `.2.2 N h K`; neither unit conjunct is mistaken for
an extra hypothesis. I checked that the scheme has no `Over` or structural arrow,
that the older `integralDerivedReduction` predicate is used unchanged, that
`rationalConstructibleCategory` has no idempotent completion, and that the four
components have exactly the written functor objects and composite algebra maps.
No statement mismatch or correction was found. The scratch file introduces no
library declaration and is not a delivery module.

## Validation

Server validation is performed with `scompile.py` on
`scratch/ExistingPentagonCheck.lean`: an explicit type ascription checks that the
third-conjunct projection has exactly the requested equation, with all variables
and universes explicitly bound; a second `#check` specializes all three arrows to
identity on the same field. The prescribed `deliver2.py --no-push` also compiles
its generated existing-declaration probe before checking the packet on the server.

Results: `ExistingPentagonCheck.lean` compiled cleanly on the server (17.3 s in
the private sandbox check, 3.4 s in the library check), including both the exact
equation ascription and the repeated-field identity specialization. The dry run
returned `OK (dry run): commit b0d25a8b3f4 passes the preflight and compiles;
nothing pushed`. A direct JSON comparison confirms that only `lean` changes;
there are no delivered Lean modules.
