## Worker report

Item: sk-lem-coprojection. Module:
`Sheaf.AlgebraicGeometry.EtaleClosedCoprojection`, declaration
`AlgebraicGeometry.Etale.closedImmersion_coprojection`.

The single theorem has four conjuncts, one for each displayed formula of the node.
Its proof is `sorry`; it introduces no definitions, auxiliary theorems or axioms.
The module docstring records the nine-step DAG proof, including the ambient Yoneda
argument that permits the base, twist and diagonal specializations.

Sources read: the complete node and its nine statement dependencies; current
main-20261015 blueprint section and proof; each dependency's declaration and docstring.
For upstream files absent or stale in the local checkout, the current source was
read using `scompile.py --source`: DerivedCategories, BoundedConstructibleComplexes,
EtaleInverseImageModulesExact, EtaleClosedAmbientAdjoint, and upstream Smooth.Coprojection
and Smooth.Conventions. There is no repair note for this item.

Hypothesis and clause correspondence:

| Node | Lean |
| --- | --- |
| Finite commutative coefficient ring | `(Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]` |
| Ordinary unbounded small-etale categories and size convention | `Scheme.{u}`, `DerivedCategoryModule Λ T`, the recorded abbreviation for `DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))`; no independent smaller universe or bounded ambient category |
| Tate datum supplies objects for every T and integer m | `twist : (T : Scheme.{u}) → ℤ → DerivedCategoryModule Λ T` |
| The inverse of the twist at m is the twist at -m, in both orders | `_twistInverse`, two `Nonempty` isomorphisms to `constantComplex Λ T` for every T,m |
| Specified pullback identifications | `_twistPullback`, for every scheme morphism and every integer m, an isomorphism from the derived inverse image of `twist V m` to `twist U m` |
| Closed immersion i | First three conjuncts bind `i : Z ⟶ X` and `[IsClosedImmersion i]` |
| K is bounded constructible with finite Tor amplitude | `DerivedCategory.isBoundedConstructible Λ X K` and `∃ a b : ℤ, DerivedCategory.hasTorAmplitudeIn Λ X a b K`; retained in each of the first three conjuncts |
| L is bounded constructible with finite Tor amplitude | The same two hypotheses for L in the first conjunct |
| L is invertible | `DerivedCategory.isInvertible Λ X L`, the existing predicate with an ambient two-sided tensor inverse |
| Ri! is the closed direct-image right adjoint | `(R(lowerStar (ModuleCat.{u + 1} Λ) i)).rightAdjoint`; the instance is the exact recorded theorem `isLeftAdjoint_rightDerivedLowerStar_of_isClosedImmersion` |
| First co-projection identity | The first `Nonempty` isomorphism, with Ri! applied to the K,L derived tensor on X and the Z-derived tensor of Ri!K and Li*L on the right |
| Base-pullback identity for f, invertible B, f'=f composed with i | Second conjunct binds arbitrary `f : X ⟶ Y`, `B : DerivedCategoryModule Λ Y` with `isInvertible Λ Y B`; left factor is `(L(upperStar ... f)).obj B`, right factor is `(L(upperStar ... (i ≫ f))).obj B` |
| Tate specialization for every integer m | Third conjunct has the literal shift of `K tensor twist X m` by `2 * m` inside Ri!, and the shift of `Ri!K tensor twist Z m` by the same integer on the right |
| Separated f and its actual self-fiber product W | Fourth conjunct binds `f : X ⟶ Y` and `[IsSeparated f]`; W is literally `pullback f f` |
| Its actual closed diagonal and both projections | Literally `pullback.diagonal f`, `pullback.fst f f`, `pullback.snd f f`; the closed-immersion instance follows from IsSeparated |
| Invertible omega_f | Fourth conjunct binds `omega : DerivedCategoryModule Λ X` and `DerivedCategory.isInvertible Λ X omega`; no smoothness or extra boundedness of intermediate factors |
| Iterated diagonal identity | Fourth `Nonempty` isomorphism, with both derived projection pullbacks on the left and the left-associated tensor `((RDelta! constantComplex) tensor LDelta*Lp1*omega) tensor LDelta*Lp2*omega` on the right |

The formal Tate assumption is written unbundled, using only existing types,
functors, isomorphisms and the coefficient unit. This is not a second definition
of Tate objects and does not construct data from a postponed existence theorem.
It spells out precisely the inverse-pair and pullback properties stipulated in
the final paragraph of this node. That paragraph does not require a Kummer model,
a coefficient-exponent restriction, rank-one geometric stalks, or normalization.
The two inverse witnesses and the pullback witnesses are hypotheses of the
mathematical datum, rather than an arbitrary map substituted for a canonical map.
The node's conclusion asserts existence of object isomorphisms, not normalization
of their morphisms, so `Nonempty (A ≅ B)` is its literal conclusion.

Dependency declarations used:

- `WeilConjectures.AlgebraicGeometry.DerivedCategories`:
  `AlgebraicGeometry.Etale.DerivedCategoryModule` (and the underlying derived category
  and homology functor). The size node is an explicitly recorded metatheoretic convention.
- `WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes`:
  `AlgebraicGeometry.Etale.DerivedCategory.isBoundedConstructible`.
- `Sheaf.AlgebraicGeometry.EtaleTorAmplitude` imports the exact bounded predicate
  `AlgebraicGeometry.Etale.DerivedCategory.hasTorAmplitudeIn` from
  `WeilConjectures.SixFunctors.Etale.Derived.Coefficients`.
- `WeilConjectures.SixFunctors.Etale.Derived.Tensor`:
  `AlgebraicGeometry.Etale.derivedTensor`. Coefficients also supplies
  `constantComplex` and `DerivedCategory.isInvertible`, which was read in full.
- `WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact`:
  `AlgebraicGeometry.etaleInverseImageModulesExact`, the recorded exact
  constant-coefficient inverse image. Its termwise derived functor is written
  with the existing `L(upperStar ...)` notation from Derived.UpperLowerStar.
- `Sheaf.AlgebraicGeometry.EtaleClosedAmbientAdjoint`:
  `AlgebraicGeometry.Etale.isLeftAdjoint_rightDerivedLowerStar_of_isClosedImmersion`.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`:
  `AlgebraicGeometry.IsClosedImmersion`.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`:
  `AlgebraicGeometry.IsSeparated`, including its closed diagonal.

All recorded proof-dependency modules are imported non-publicly when not already
public statement imports. The Mathlib leaves for quasi-inverse adjunction, finite
closed immersions and Yoneda are imported from Adjunction.Basic,
Morphisms.Finite, and Yoneda. The properness instance needed in the proof is in
Morphisms.Proper. No unstated independent prerequisite is needed to type the statement.

Edge cases checked before writing:

- Empty schemes and empty closed subschemes are allowed; no nonemptiness assumption.
- The identity closed immersion and identity separated morphism remain included.
- The zero coefficient ring and the zero complex are allowed; no Nontrivial assumption.
- Tor intervals are existential, with no artificially imposed positive length.
  In particular zero complexes and an empty interval are not excluded.
- Every integer m is allowed, including zero and negative m. Both orders of the
  m,-m inverse pair are supplied; the shift is the signed integer `2 * m`.
- No characteristic or invertible-exponent assumption is added. The node is a
  formal assertion for supplied invertible twist objects, not a geometric purity theorem.
- K and L alone have the stated finiteness hypotheses; the inverse object of L,
  Ri!K, pulled-back B, and the intermediate diagonal tensors are not required to be
  bounded constructible. This matches the repaired ambient proof in the DAG.
- The diagonal is the actual self-pullback diagonal and is closed by separation,
  rather than an arbitrary morphism accompanied by an unrelated compactification.

Searches for existing declarations:

1. `msearch.py ... leanfinder "co-projection for a closed immersion and an invertible
   derived tensor factor on small etale sheaves"`: eight hits, including
   Algebra.FormallyUnramified.isOpenImmersion_SpecMap_lmul and unrelated etale
   morphism statements; no co-projection theorem.
2. `msearch.py ... loogle "rightDerivedUpperShriek, derivedTensor"`: zero hits,
   unknown identifier rightDerivedUpperShriek in Mathlib.
3. `msearch.py ... grep "rightDerivedUpperShriek|coprojection" CategoryTheory`:
   15 ordinary coproduct-coprojection hits; no exceptional inverse image formula.
4. `msearch.py ... leansearch "right adjoint commutes with tensor by an invertible
   object projection formula"`: eight hits, including Module.Invertible.rTensorEquiv
   and CategoryTheory.tensorRightAdjunction; no small-etale co-projection theorem.
5. `rg` for the item id and `nonempty_iso_rightDerivedUpperShriek` in upstream
   WeilConjectures locates EtaleCohomology/Purity/Smooth/Coprojection.lean and its
   consumers. Read its entire declarations, docstrings and formal vocabulary,
   including the current live source through `scompile.py --source`.
6. `rg` for coprojection/Coprojection/rightAdjoint-derivedTensor in `lean/Sheaf`
   finds ordinary coproduct coprojections and no matching theorem. Also searched
   `dag/lean_names_upstream.json`; no usable binding of this node was present.
7. Fresh-name grep for `closedImmersion_coprojection` in upstream and side sources
   returns no existing declaration.

Why the previous ATTACH candidates are not exact matches:

The upstream main theorem uses
`DerivedCategory.boundedConstructibleFiniteTor`, whose constructibility component
is the upstream `boundedConstructible`, defined using `Scheme.IsConstructibleSheaf`.
The recorded dependency deliberately uses `isBoundedConstructible`, defined using
`Scheme.IsConstructibleEtaleModuleSheaf`; its docstring explicitly says not to reuse
the upstream predicate. No unproved identification is assumed here. In addition,
the upstream formulas use the compactification-based right adjoint of Ri_!, whereas
the present node explicitly fixes the right adjoint of closed direct image. Finally,
the live upstream twist theorem requires `[HasInvertibleExponent Λ X]` and the
analogous hypothesis on Z. Its live HasTateTwist only guarantees inverse and pullback
identifications under those hypotheses. Attaching those declarations would silently
change either the hypotheses or the vocabulary of this node. This delivery instead
uses the exact recorded predicates, direct-image adjoint and explicit formal datum.

No statement correction, disputed statement, new node or dependency repair is needed.
Only the item's `lean` field changes. The public statement was compiled through the
prescribed scompile.py wrapper: sandbox 5.9 seconds, final library module 7.5 seconds,
no errors or warnings. No global build or direct live-source edit was performed.

## Second reading by Q118

I reread `dag/nodes/sec-smooth-purity/sk-lem-coprojection.json`, its source place
(`literature/blueprint/main-20261015/blueprint/sec-smooth-purity/sk-lem-coprojection/_section.md`),
the nine-step proof file, and the upstream ordinary-etale Coprojection source. The node's
objects, hypotheses, and conclusion clauses match the Lean signature as follows.

1. The coefficient object is a finite commutative ring: Lean has
   `(Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]`. The Tate datum consists of objects
   `twist T m` for every `Scheme.{u}` and `m : ℤ`, two inverse-pair `Nonempty` isomorphisms
   for `m` and `-m`, and pullback isomorphisms for every scheme morphism and integer. This is
   exactly the node's stated formal datum; no characteristic, exponent, normalization, or
   Kummer hypothesis is added.
2. The ambient categories are the ordinary unbounded small-etale derived module categories:
   `DerivedCategoryModule Λ T`, with `ModuleCat.{u + 1} Λ` and `Scheme.{u}`. This renders the
   node's size convention without introducing a bounded ambient category or a smaller universe.
3. In the first conjunct, Lean introduces `Z X`, `i : Z ⟶ X`, `[IsClosedImmersion i]`,
   `K L : DerivedCategoryModule Λ X`, and hypotheses
   `isBoundedConstructible K`, existential finite `hasTorAmplitudeIn K`, the corresponding
   two hypotheses for `L`, and `isInvertible L`. Its `Nonempty` isomorphism is exactly
   `Ri! (K ⊗ᴸ L) ≅ Ri! K ⊗ᴸ Li* L`, rendered by the right adjoint of
   `R(lowerStar ... i)` and `derivedTensor`/`L(upperStar ...)`.
4. The second conjunct introduces arbitrary `f : X ⟶ Y`, `B` on `Y`, with `B` invertible,
   and keeps the node's `K` finiteness hypotheses. Its right side uses `i ≫ f` exactly for
   `f' = f ∘ i`, giving the stated base-pullback formula.
5. The third conjunct introduces every `m : ℤ`, retains precisely the node's `K` finiteness
   hypotheses, and states the shift by the signed integer `2 * m` on both sides, with
   `twist X m` and `twist Z m`.
6. The fourth conjunct introduces `f : X ⟶ Y` with `[IsSeparated f]`, takes the actual
   `W = pullback f f`, actual `pullback.diagonal f`, `pullback.fst f f`, and
   `pullback.snd f f`, and an invertible `omega` on `X`. The displayed Lean isomorphism is
   the node's left-associated iterated formula, including `RΔ! constantComplex` and both
   pulled-back factors. Separation supplies exactly the closed-diagonal hypothesis needed by
   the right-adjoint construction.

The edge cases remain covered: empty schemes and closed subschemes, identity immersions and
identity separated morphisms, the zero coefficient ring and zero complexes, arbitrary integer
`m` including `0` and negative values, zero-length or unconstrained existential Tor intervals,
and no characteristic or exponent restriction. The fourth clause does not impose finiteness on
`omega` beyond invertibility, matching the node.

I searched Mathlib, the project source, and the DAG with LeanFinder/LeanSearch/Loogle/grep,
including fresh-name searches for `closedImmersion_coprojection` and searches for exceptional
inverse-image projection formulas. The upstream declaration
`AlgebraicGeometry.Etale.nonempty_iso_rightDerivedUpperShriek_derivedTensor_of_isInvertible`
is not an exact existing match: it uses `boundedConstructibleFiniteTor` (with the upstream
constructibility predicate), a compactification-based `rightDerivedUpperShriek`, and extra
compactification hypotheses. The upstream consequence declarations have the same mismatch.
No Mathlib or current project declaration states this node with its recorded predicates and
right adjoint, so `existing: false` and the delivered module are correct.

No mismatch was found. I changed no Lean declaration, node statement, dependency, or import;
there is no statement correction, new node, dependency repair, or disputed statement. The
module and its exact signature compiled with
`python3 /home/ubuntu/weil-launcher-nt/scompile.py Q118 sk-lem-coprojection
lean/Sheaf/AlgebraicGeometry/EtaleClosedCoprojection.lean` with no errors or warnings.
