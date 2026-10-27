## Worker report

The module `Sheaf.AlgebraicGeometry.MonoschemeSmoothLocalCharts` states all clauses of
`lem-trf-monoscheme-smooth-local-charts` in five named theorems. All proofs are `sorry`;
there are no new definitions, new nodes, dependency repairs, or statement changes.
Read ILO VIII printed pp.98--104, especially Remarks 3.1.4(iii), 3.1.10(ii),
3.1.16(i) and Lemma 3.2.12(i). The latter imposes no torsion-free assumption in (i).

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- A fine monoscheme is the recorded `Monoscheme.Fine.{u}`; its definition already
  includes the finite affine cover convention of the dependency. Points are `x : M.space`.
  `exists_smallest_affine_neighborhood` gives `U : AffineOpens M`, so the open is affine
  with a fine coordinate monoid. The witness `hx` asserts that it contains x, the universal
  inequality over `V : Opens M.space` says it is smallest, and
  `z ∈ U.1 ↔ Specializes z x` says that it consists exactly of generalizations.
  `Function.Bijective (FineFan.germ ... U.1 x hx)` identifies its sections with the actual
  stalk through the canonical homomorphism, rather than an arbitrary monoid isomorphism.
- For the explicit affine formula, `P : Type u`, `[CommMonoid P]`, `FineFan.IsFine P`,
  and `Submonoid.closure (Set.range e) = ⊤` express a fine monoid with a finite tuple of
  generators `e : Fin n → P`. A finite generating set is enumerated by such a tuple;
  repetitions cause no change to the principal open or localization. `p` is the prime.
  The equation defining `a` multiplies exactly the generators outside p: the factors
  inside p are replaced by 1. This is the node's additive sum with empty sum 0, since
  the dependency uses multiplicative notation. The theorem says D(a) is the smallest
  neighborhood and equates `Algebra.faceLocalization P (Submonoid.powers a)` with
  localization along `Submonoid.closure {q | q ∉ p.carrier}`, as actual submonoids of
  the group completion. Its final `E` identifies sections of the ordinary monoid sheaf
  on D(a) with this localization and fixes every numerator. These are the claimed
  `Γ(M_x) = P_p` and `P_a = P-(P\p)` identifications. In an arbitrary affine neighborhood
  of M, transport this formula by its chart isomorphism; uniqueness of the smallest
  open in the first theorem identifies it with M_x.
- `restrict_smallest_neighborhoods` uses the recorded `f : Hom N M`, any point y, and
  affine neighborhoods U,V containing y and f(y). `_hU` and `_hV` say exactly that
  these are N_y and M_f(y); these binders describe the objects already constructed,
  not additional geometric assumptions. The witness `h` is the required image inclusion.
  The displayed `g` and its square with `ofRestrict` give the actual restricted map.
  The equality on every section says precisely that `Hom.sectionMap` becomes the
  recorded `FineFan.stalkMap f.map y` under the two canonical germ identifications.
  The implication with hypothesis `f.IsSmooth` gives finite `r t : ℕ`, the isomorphism
  `Γ(V) × Multiplicative (Fin r → ℕ) × Multiplicative (Fin t → ℤ) ≃* Γ(U)`, and its
  equation `e (p,1,1) = f.sectionMap ... p`. Thus it identifies the given affine morphism
  with the first-factor product inclusion. Here Γ(V) is canonically the P of the node
  by the first theorem; no arbitrary replacement of the stalk map is made.
- `realized_smallest_product_chart` applies to precisely this product chart and its
  commuting section-map equation, with `k : Type u` and `[Field k]`. The codomain of
  `E` is `AddMonoidAlgebra (MvPolynomial (Fin r) (MonoidAlgebra k Γ(V))) (Fin t → ℤ)`:
  finite sums with integer Laurent exponents and polynomial coefficients, exactly
  `k[P][x_1,...,x_r,y_1^{±1},...,y_t^{±1}]`. It uses Mathlib's existing monoid and
  polynomial algebras. The first formula sends `e^(p,α,β)` with coefficient a to
  `e^p x^α y^β`, using `Finsupp.equivFunOnFinite.symm` for the finite natural exponent
  vector. The second formula sends every element of `k[P]` to its constant Laurent
  polynomial with constant polynomial coefficient; it identifies the entire realized
  ring map, not just its values on generators. The conjunct `Smooth (Spec.map ... )`
  asserts smoothness of the exact map induced by the recorded `monoidAlgebra` functor.
  The library uses one common ambient universe for the monoscheme and coefficient
  field; no separate universes are equated by an extra hypothesis.
- `smallest_neighborhood_realizations_cover` quantifies over any family of smallest
  neighborhoods, with membership and minimality as above. Every `z : realization k N`
  is the image of some point q in the corresponding actual affine realization diagram
  object, under `realizationι`. This is exactly covering k[N] by the source realizations.
  None of the five signatures assumes torsion-freeness of M, N, or their stalks.

Dependency declarations read and used:

- `Sheaf.AlgebraicGeometry.FineFanBlowup`: `FineFan.IsFine`, `MonoidPrime`, `basicOpen`,
  the spectrum sheaf, `germ`, and `stalkMap` (including their full signatures/docstrings).
  Its `Algebra.faceLocalization` comes from `Sheaf.TraceFormula.FaceLocalizationFs`:
  the concrete subgroup-completion fractions `of q * (of f)⁻¹`.
- `Sheaf.AlgebraicGeometry.MonoschemeToricRealization`: `affine`, `Fine`, `Hom`,
  `Hom.IsSmooth`, `AffineOpens`, `affineSection`, `Hom.sectionMap`, `monoidAlgebra`,
  `realizationDiagram`, `realization`, and `realizationι`. These are used without copies.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: the recorded `Smooth` class,
  `smooth_comp`, and the open-immersion smoothness instance. Read the exact Smooth
  signature and affine-local docstring, not the search service's older `IsSmooth` name.
- Available proof imports: `Mathlib.AlgebraicGeometry.AffineSpace`,
  `Mathlib.AlgebraicGeometry.OpenImmersion`, and
  `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth` (whose
  `AffineSpace.smoothOfRelativeDimension_over` signature and docstring were read).
  `FineFanBlowup` and `MonoschemeToricRealization` are public statement imports.
  `lem-trf-monoid-prime-minimal-neighborhood` has no recorded Lean module to import.
  The recorded proof-only `Sheaf.AlgebraicGeometry.FineMonoidLocalSmoothCharts` is absent
  locally and `scompile.py --source Sheaf.AlgebraicGeometry.FineMonoidLocalSmoothCharts`
  reports `Module source unavailable`. It is therefore omitted as a proof import;
  none of its declarations is needed to type these statements. Its mathematical role
  remains explicit in the theorem docstrings and the unchanged DAG proof.

Edge cases checked against the source and signatures: empty monoscheme and cover;
the zero additive monoid (one multiplicative element) and empty generating tuple;
empty prime, maximal prime, generic and closed points; all generators in the prime;
monoids that are finite groups, including torsion; identity morphisms; r=0, t=0,
and r=t=0; arbitrary field characteristic. Empty selected products equal 1, localizations
at 1 are unchanged, and the Laurent exponent group at t=0 is trivial. No field
characteristic or torsion-freeness condition is introduced. The covering argument uses
the maximal monoid prime, whose smallest neighborhood is the whole original chart,
so it covers all scheme points of the realization, not only distinguished monomial points.

Searches actually run:

- `msearch.py leanfinder`: "Smallest affine neighborhoods of fine monoschemes and smooth
  product charts with polynomial Laurent monoid algebra realization". Eight hits,
  headed by ordinary scheme standard-smooth charts and affine-neighborhood lemmas;
  none states this monoscheme theorem.
- `msearch.py leansearch`: "Fine monoscheme smallest affine neighborhood and smooth
  polynomial Laurent charts". Eight hits: ordinary scheme affine neighborhoods and
  smooth classes; no monoscheme statement.
- `msearch.py loogle`: "MonoidAlgebra, Smooth". Zero hits, with the service note
  "unknown identifier 'Smooth'"; this query did not establish absence by itself.
  A second query `MonoidAlgebra.curryAlgEquiv` found the existing product algebra
  equivalence and its monomial formulas; its full source was read. This is a component
  of the algebra calculation, not the combined node statement.
- `msearch.py grep`: `Monoscheme|monoscheme` in Mathlib: zero hits.
- `rg` in project `lean/WeilConjectures` for monoscheme and smallest/smooth-chart names,
  and for the item id: no matching existing declaration. `rg` in `lean/Sheaf` found
  the recorded fine-monoscheme and realization interfaces, which are reused, but no
  declaration tagged with this item and no exact existing theorem for all its clauses.
  Also checked `dag/lean_names_upstream.json`; no monoscheme entry.
- Read Mathlib's `MonoidAlgebra.curryAlgEquiv`, `domCongr`, finite polynomial exponent
  conventions and `MonoidHom.inl` while checking that no extra ring notion was needed.

Validation: the initial complete module passed `scompile.py` in both sandbox and library
modes with no errors or unexpected warnings. The final packet is checked again by the
required delivery dry run. No `STATEMENT-DISPUTED` flag or mathematical node fault.

## Second reading by Q60

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
