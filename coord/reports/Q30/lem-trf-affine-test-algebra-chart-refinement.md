## Worker report

The new module `Sheaf.AlgebraicGeometry.AffineTestAlgebraChartRefinement` states
`AlgebraicGeometry.affine_test_algebra_chart_refinement`, with `sorry` as its only proof.
It defines no new notion. The node is unchanged except for its `lean` record.

I read Stacks `morphisms.tex`, `lemma-J` (Tag 07R4), lines 3310–3361: the first
paragraph gives local finite type for open inclusions and compositions, the second
uses a finite type algebra over an affine open, and the last chooses affine source
charts over prescribed affine target charts and asserts finite type of section maps.
The present node isolates that geometric preparation; it assumes neither J-2 nor a
regular-locus conclusion. Its six proof steps are reproduced in the theorem docstring.

Hypotheses and clauses, in the order of the node:

- The locally Noetherian scheme is `(X : Scheme.{u}) [IsLocallyNoetherian X]`.
- Its prescribed affine open cover is `{I : Type v} (U : I → X.affineOpens)` and
  `(hcover : (⨆ a, (U a).1) = ⊤)`. The subtype bundles exactly affineness of each
  open; the supremum equality is the covering condition. There is no `Finite I`.
- The affine open `V` is `(V : X.affineOpens)`; the ring `R` is literally
  `Γ(X, V.1)`, rather than an independently supplied ring with an arbitrary map.
- The commutative ring and the finite type homomorphism are `(B : Type u)
  [CommRing B] (φ : Γ(X, V.1) →+* B) (hφ : φ.FiniteType)`.
- The spectrum `Y` is literally `Spec (CommRingCat.of B)`.
- The morphism `h : Y → V` is
  `Spec.map (CommRingCat.ofHom φ) ≫ V.2.isoSpec.inv`.
  Mathlib's `IsAffineOpen.isoSpec` has the precise target `Spec Γ(X,V)`, so this
  uses the canonical identification in the node without any extra identification
  hypothesis or choice. Its composite `f : Y → X` is written
  `Spec.map (CommRingCat.ofHom φ) ≫ V.2.fromSpec`;
  `IsAffineOpen.fromSpec` is defined as `V.2.isoSpec.inv ≫ V.1.ι`.
- The first conjunct is the asserted `IsNoetherianRing Γ(X, V.1)`.
- The second and third conjuncts are `LocallyOfFiniteType` of precisely `h` and `f`.
- The fourth conjunct is `IsLocallyNoetherian (Spec (CommRingCat.of B))`.
- The existential `i : Spec (CommRingCat.of B) → I` chooses an index for every
  point, and `W : Spec (CommRingCat.of B) → (Spec (CommRingCat.of B)).affineOpens`
  chooses an affine open for each point.
- `(∀ y, y ∈ (W y).1)` renders the neighbourhood condition.
- `(⨆ y, (W y).1) = ⊤` renders the union of all these neighbourhoods being `Y`.
- The existential proof family `e : ∀ y, (W y).1 ≤ f ⁻¹ᵁ (U (i y)).1`
  renders the containment in the inverse image. It is bound explicitly because
  the canonical section-map API consumes this proof.
- Finally `∀ y, (f.appLE (U (i y)).1 (W y).1 (e y)).hom.FiniteType` says that
  every induced map from `O_X(U_i(y))` to `O_Y(W_y)` is of finite type. The map is
  Mathlib's canonical `Scheme.Hom.appLE`, not an arbitrary finite type map.

Dependency declarations, with signatures and docstrings read in the local Mathlib:

- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`, `AlgebraicGeometry.Scheme`
  and its scheme morphisms.
- `pqf-def-locnoeth`: `Mathlib.AlgebraicGeometry.Noetherian`,
  `AlgebraicGeometry.IsLocallyNoetherian`; its every-affine-open presentation
  agrees with the node's covering presentation by the recorded cover theorem.
- `def-weil-pbc-finite-type-algebra`: `Mathlib.RingTheory.FiniteType`,
  `RingHom.FiniteType`, defined using `φ.toAlgebra`, exactly the supplied ring map.
- `def-weil-affine-spectrum`: `Mathlib.AlgebraicGeometry.Scheme`,
  `AlgebraicGeometry.Spec` and `AlgebraicGeometry.Spec.map`.
- `def-weil-pbc-noetherian-ring`: `Mathlib.RingTheory.Noetherian.Defs`,
  `IsNoetherianRing`, meaning finite generation of all ideals.
- `def-weil-finite-type-morphism`:
  `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`,
  `AlgebraicGeometry.LocallyOfFiniteType` and its induced `finiteType_appLE`.
- The canonical affine identification and open immersion are
  `IsAffineOpen.isoSpec` and `IsAffineOpen.fromSpec` in
  `Mathlib.AlgebraicGeometry.AffineScheme` (lines 388 and 427).

All six statement-dependency modules are public imports. The proof dependencies
have Mathlib matches, rather than separately landed project modules. Their relevant
interfaces (`IsLocallyNoetherian.component_noetherian`,
`Algebra.FiniteType.isNoetherianRing`, `HasRingHomProperty.iff_exists_appLE`,
`IsImmersion`'s locally finite type instance, `locallyOfFiniteType_comp`,
`Scheme.isBasis_affineOpens`, and `locallyOfFiniteType_iff`) are available through
these imports. No extra dependency interface or duplicate notion is needed.

Edge cases checked mathematically against both node and signature:

- If `B` is the zero ring, `Y` is empty. Its point-indexed functions and affine
  family are empty, the supremum of the empty family is top in the empty space,
  and all membership, containment and finite type clauses are vacuous.
- An empty `I` forces `X` empty by `hcover`; hence `V` and `Y` are empty as well.
  A unital map from the zero section ring forces `B` to be the zero ring.
  No impossible nonempty choice of chart is required.
- An arbitrary infinite `I` is permitted. No finite subcover or quasi-compactness
  hypothesis has been inserted.
- For `X = Spec k`, `V = X`, `B = k[t]`, the formula is the usual spectrum map
  and affine chart refinement. No extra finiteness on `B` as a module is assumed.
- The cover index universe `v` is independent of the ambient scheme universe `u`.
  Rings, spectra, points and section maps share the ambient Mathlib scheme
  universe; there is no quantification over a smaller universe of test rings.

Searches actually run on 2026-10-24:

1. `msearch.py ... leanfinder` with query
   "A finite type algebra over an affine open of a locally Noetherian scheme admits
   affine charts refining a prescribed affine open cover": eight hits, including
   `Scheme.OpenCover.affineRefinement`, cover criteria for local Noetherianity and
   finite-cover Noetherianity. None states the combined point-indexed result or
   the canonical algebra input and its two locally finite type morphisms.
2. `msearch.py ... loogle` with query
   `AlgebraicGeometry.LocallyOfFiniteType, RingHom.FiniteType`: five hits,
   including `LocallyOfFiniteType.finiteType_appLE`, its constructor and
   `locallyOfFiniteType_iff`. These give the exact ring-map interface, not the item.
3. `msearch.py ... grep` with query
   `affine.*refin|refin.*affine|finiteType.*app` in `AlgebraicGeometry`: 25 hits,
   including the general `OpenCover.affineRefinement` and usages of
   `finiteType_appLE`. No exact statement.
4. `rg` over `lean/WeilConjectures` and `lean/Sheaf` for affine refinements and
   the candidate declaration names: general affine/fppf refinement material and
   unrelated affine-line proofs, but no statement of the item. A precise search
   for `affineTestAlgebra`, `affine_test_algebra`, `affineChartRefinement`,
   `affine_chart_refinement` and the final module/declaration names in those
   roots and `dag/lean_names_upstream.json` returned no exact declaration.
5. `grep -rn` for the node id in `lean/WeilConjectures` returned no match.

Validation: the prescribed `scompile.py Q30
lem-trf-affine-test-algebra-chart-refinement <module>` compiled the module as both
sandbox and library source on the server, with no errors or warnings. Both
reported 1.4 seconds. The maximum Lean source line length is 93 characters.
There are no new nodes, dependency modules, statement corrections or disputes.

## Second reading by Q30

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
