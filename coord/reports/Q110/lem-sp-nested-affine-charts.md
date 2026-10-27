## Worker report

The module `Sheaf.AlgebraicGeometry.NestedAdmissibleAffineCharts` states
`AlgebraicGeometry.SmoothOfRelativeDimension.exists_nested_admissible_affine_charts`.
Its only theorem has proof `sorry`. There are no new definitions, helper axioms,
new nodes, dependency repairs, or statement corrections. Only the item's `lean`
record changes. All data in the statement are existing Mathlib/project objects.

Source read: current blueprint `literature/blueprint/latest/blueprint/sec-smooth-purity/
sk-prop-sp-composition/sk-prop-sp-composition-factors.proof.md`, proof (1), first
sentence. It chooses coordinates for g and then coordinates for f over that chart,
with f coordinates integrated first. Also read Stacks morphisms.tex Tag 054L,
`lemma-smooth-etale-over-affine-space`, and constructions.tex Tag 01M0,
`definition-affine-n-space` and its polynomial description/base-change discussion.
The imported node's nine proof steps are carried into the theorem docstring with
their dependency ids. No change to the accepted stage-1 proof is made.

Hypotheses and clauses, checked against the full node statement:

- The fixed algebraic closure of a finite field, p, q, and the positive exponent
  are `D : WeilConjectures.FiniteFieldDatum.{u}`. Its fields `D.k`, `D.k₀`,
  `D.prime`, `D.card_base`, `D.cardinality_eq`, `D.exponent_pos`, and
  `D.isAlgClosure` give exactly the global datum. The prime ell distinct from p
  is `(ell : ℕ) (_hell : ell.Prime) (_hne : ell ≠ D.p)`. It is retained even
  though the geometric assertion is independent of the coefficient prime.
- X, Y, Z are `Scheme.{u}`, each `Over (Spec (.of D.k))`. Each structure map
  has `IsSeparated`, `LocallyOfFiniteType`, and `QuasiCompact`: precisely
  separated finite type over k, not absolute separation over Spec Z.
- f and g are morphisms with `IsOver (Spec (.of D.k))` and `IsSeparated`.
  Pure relative dimensions are `(d e : ℕ)`, `SmoothOfRelativeDimension d f`
  and `SmoothOfRelativeDimension e g`. The composite h is written `f ≫ g`.
- For every scheme point (`∀ x : X`), the existential S, V, U are opens of
  Z, Y, X respectively; `IsAffineOpen` asserts affineness, and the three
  membership clauses say they contain gf(x), f(x), x. `hVS` and `hUV` are
  exactly V ≤ g⁻¹S and U ≤ f⁻¹V.
- The two chart maps v and u have targets `AffineSpace (ULift (Fin e)) S.toScheme`
  and `AffineSpace (ULift (Fin d)) V.toScheme`. `Etale v` and `Etale u` give
  étaleness. The two equalities with `g.resLE S V hVS` and `f.resLE V U hUV`
  give exactly the restricted structural morphism factorizations.
- The base change b is the existing canonical `AffineSpace.map (ULift (Fin d)) v`.
  Mathlib's `AffineSpace.isPullback_map` identifies its square with the base
  change square. No unconstrained morphism is used in place of b.
  Both `Etale b` and `Etale (u ≫ b)` are asserted.
- The isomorphism c has exactly the iterated affine-space source and summed
  affine-space target. Its equations on all standard coordinates specify that
  `Fin.castAdd e` positions are the f coordinates and `Fin.natAdd d` positions
  are pullbacks of the g coordinates. The equation on the projection fixes
  the base map. These equations uniquely characterize the ordered canonical
  isomorphism by `AffineSpace.hom_ext`; thus c is not an arbitrary coordinate
  isomorphism. This is a characterization of the identification already in
  the statement, not a new notion or a stronger chart condition.
- The displayed equality `U.ι ≫ f ≫ g = u ≫ b ≫ c.hom ≫ p ≫ S.ι` is precisely
  the equation h|U = p_(d+e,S) c b u, compared in the original Z. Inclusion S.ι
  is needed because the left hand side lands in Z and the right initially in S.
- The list of seven `Over.mk` objects is S, V, U, A^e_S, A^d_V,
  A^d_(A^e_S), and A^(d+e)_S, each with its indicated structural map to k.
  For every member, `IsNoetherian W.left`, `IsSeparated W.hom`,
  `LocallyOfFiniteType W.hom`, `QuasiCompact W.hom` give the exact final
  geometric properties. Using bundled objects in a finite list avoids
  introducing any private admissibility predicate.
- The finite list of `Arrow.mk` entries contains v, u, b, bu, cbu, c and
  its inverse, the four affine-space projections, g|V, f|U, the composite
  map U → S, and the inclusions U → X, V → Y, S → Z. Each has
  `IsSeparated`, `LocallyOfFinitePresentation`, `QuasiCompact`,
  `QuasiSeparated`. The final three together are finite presentation in
  Stacks Tag 01TP, as prescribed by def-weil-pbc-scheme-conventions.
- The pointwise existence statement says these opens cover X: take the family
  of all witnesses (or all such chart data). If X is empty this family is empty
  and no chart is requested. No nonempty or surjectivity assumption occurs.

Dependency declarations and source interfaces read:

- def-weil-finite-field-fiber: `Sheaf.Paper.FiniteFieldFiber`,
  `WeilConjectures.FiniteFieldDatum`, full structure and instance attributes.
- def-weil-finite-type-morphism: Mathlib Morphisms.FiniteType and QuasiCompact,
  `AlgebraicGeometry.LocallyOfFiniteType` and `AlgebraicGeometry.QuasiCompact`.
- def-weil-proper-morphism: Mathlib Morphisms.Proper/Separated,
  `IsProper`, `IsSeparated`; separation is the diagonal condition.
- def-sbc-smooth-morphisms: Mathlib Morphisms.Smooth, `Smooth` and
  `SmoothOfRelativeDimension`; the latter is the recorded standard-smooth
  local form equivalent to constant pure fibre dimension.
- def-weil-etale-morphism: Mathlib Morphisms.Etale, `Etale`.
- def-sbc-affine-space: its mathlib_match is used directly:
  Mathlib.AlgebraicGeometry.AffineSpace, `AffineSpace`, `AffineSpace.over`,
  `AffineSpace.map`, `AffineSpace.coord`, `AffineSpace.isPullback_map`.
  `ULift.{u} (Fin n)` is exactly the recorded coordinate convention.
- def-weil-open-immersion: Mathlib.AlgebraicGeometry.OpenImmersion,
  `IsOpenImmersion`; open subschemes, inclusions and restrictions reuse
  `Scheme.Opens.toScheme`, `.ι`, and `Scheme.Hom.resLE`.
- def-pc-fibre-product: Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback,
  `pullback`, `pullback.fst`, `pullback.snd`, used by the existing affine space.
- def-sbc-locally-finite-presentation: Mathlib Morphisms.FinitePresentation,
  `LocallyOfFinitePresentation`.
- pqf-def-locnoeth: Mathlib.AlgebraicGeometry.Noetherian,
  `IsLocallyNoetherian`; `IsNoetherian` adds compactness as the node requires.
- def-weil-pbc-scheme-conventions explicitly declares it adds no own notion;
  its existing convention record is used, particularly for finite type and
  finite presentation as the conjunctions stated above.

Proof imports: `Sheaf.AlgebraicGeometry.SmoothAdmissibleCoordinateCover` supplies
`SmoothOfRelativeDimension.exists_finite_admissible_coordinate_cover`, whose
full signature and docstring were read. All other recorded proof dependencies
are Mathlib leaves; the relevant modules for separation, finite type, finite
presentation, Noetherian schemes, fibre products, étale morphisms, finite and
closed/ordinary immersions are imported. No unstated dependency is needed to
form the statement.

Searches actually run:

- msearch.py leanfinder: "Two composable smooth morphisms admit nested affine
  etale coordinate charts with ordered coordinates of summed relative dimension".
  Eight hits, including smooth relative-dimension composition and standard-smooth
  étale polynomial charts; none states the nested affine/admissibility assertion.
- msearch.py loogle: "AlgebraicGeometry.AffineSpace,
  AlgebraicGeometry.SmoothOfRelativeDimension". Three hits, the smoothness
  of affine-space projections, not the requested chart existence theorem.
- msearch.py grep: "nested.*chart|chart.*nested|AffineSpace.*(sum|Sum)|(sum|Sum).*AffineSpace"
  in AlgebraicGeometry: zero hits.
- rg on lean/WeilConjectures and lean/Sheaf for the node id, nested affine
  names, and affine spaces indexed by sums. No exact theorem. The smooth-pair
  coordinates module treats a closed immersion of two smooth schemes, not two
  composable smooth morphisms. The existing finite admissible coordinate cover
  handles one morphism only. The upstream `AffineSpace.sumIso`, `reindexIso`,
  `sumHom`, `sumInv` were also read: they give the coordinate construction,
  not the nested-chart theorem. No duplicate definition was introduced.
- rg on dag/lean_names_upstream.json and lean/WeilConjectures for
  lem-sp-nested-affine-charts: no hits.

Edge cases: d=0 and e=0 are allowed; the corresponding universally quantified
coordinate equations range over Fin 0 and are empty, while the projection
condition still fixes the base map. With both zero the ordered isomorphism is
that between zero-variable affine spaces and their base. The empty scheme X
makes the pointwise conclusion vacuous and admits the empty covering. Empty Y
or Z forces the source empty when a map to it exists. Disconnected schemes and
non-surjective smooth maps are allowed; the statement only fixes the relative
dimension on their nonempty fibres. No extra dimension, nonzero, field-size,
or nonemptiness restriction is introduced. The common scheme/coefficient
universe u and `ULift.{u} (Fin n)` do not bound the number of scheme points or
exclude arbitrary schemes in the stipulated universe.

Validation: scompile.py on the server compiled the module cleanly. Expected
sorry-only proof, all variables explicitly bound (`autoImplicit false`). The
final version is checked again by deliver2.py, including the added summed chart
arrow in the admissibility list. No STATEMENT-DISPUTED issue was found.

The dispatcher instructs this worker to deliver directly and forbids starting
other agents; the maintainer supplies the independent review. No second reading
by a separate worker is claimed here.

## Second reading by Q110

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
