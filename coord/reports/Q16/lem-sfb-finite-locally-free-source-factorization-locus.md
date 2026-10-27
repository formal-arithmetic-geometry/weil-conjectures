## Worker report

The module `Sheaf.AlgebraicGeometry.FiniteLocallyFreeSourceFactorizationLocus` states
`AlgebraicGeometry.exists_finiteLocallyFreeSource_closedFactorizationLocus`. Its sole
proof is `sorry`, as required for stage 2. It introduces no definitions, helper axioms,
new nodes, dependency replacements, or statement corrections. The node copy changes
only `lean`.

Source read: Conrad, *Reductive Group Schemes*, Lemma 2.1.3 and its proof,
printed pp.58–59, and the last part of the proof of Proposition 2.1.2, printed p.60:
https://math.stanford.edu/~conrad/papers/luminysga3smf.pdf . The former constructs the
Hom scheme using coefficients in a finite free basis; the latter imposes coefficient
conditions from the ideal of the target closed subscheme. The node's ten-step proof
makes finite generation, gluing, and arbitrary parameter base change explicit. All ten
steps, including their cited inputs and the rank-zero case, are in the theorem docstring.

Hypothesis-by-hypothesis and clause-by-clause comparison:

- The base, source, target, closed subscheme, and parameter are the explicitly bound
  `{S D X Z P : Scheme.{u}}`, for arbitrary universe `u`.
- The finite locally free morphism is `(q : D ⟶ S) [q.IsFiniteLocallyFree]`, using
  the recorded upstream class, which extends `IsFinite`, `Flat`, and
  `LocallyOfFinitePresentation`. No constant rank or nonempty source is required.
- The affine finitely presented target is `(x : X ⟶ S) [IsAffineHom x]
  [LocallyOfFinitePresentation x]`. Affine morphisms are quasi-compact and
  quasi-separated, so this is exactly finite presentation, with no extra condition.
- The finitely presented closed immersion is `(i : Z ⟶ X) [IsClosedImmersion i]
  [LocallyOfFinitePresentation i]`. Closed immersions are affine and therefore
  quasi-compact and quasi-separated; local finite presentation is exactly the
  remaining requirement for finite presentation. `Z` has its induced map `i ≫ x` to S.
- The S-scheme parameter is `(p : P ⟶ S)`. The family is
  `(F : pullback q p ⟶ X)`, and
  `hF : F ≫ x = pullback.snd q p ≫ p` asserts that it is an S-morphism.
- The conclusion `∃ (L : Scheme.{u}) (l : L ⟶ P), IsClosedImmersion l ∧
  LocallyOfFinitePresentation l ∧ ...` is the required finitely presented closed
  immersion. Again quasi-compactness and quasi-separatedness follow from closedness.
- The first `∀ (T : Scheme.{u}) (t : T ⟶ P)` covers every S-scheme T and every
  S-morphism to P: the displayed arrow equips T with `t ≫ p`, and any separately
  specified structure map of an S-morphism is equal to this one. Thus neither the
  objects nor the morphisms of the test category are restricted.
- Factorization through L is `∃! a : T ⟶ L, a ≫ l = t`.
- The canonical `1_D × t` is
  `pullback.map q (t ≫ p) q p (𝟙 D) t (𝟙 S) (by simp) (by simp)`.
  The right side is `∃! b : pullback q (t ≫ p) ⟶ Z, b ≫ i = ... ≫ F`.
  The `↔` asserts exactly the factorization criterion; `∃!` on both sides records
  uniqueness. Since i and l are monomorphisms, unique existence is equivalent to
  existence on each side independently. The equations also force all lifts to be
  S-morphisms; no arbitrary replacement of the canonical map is used.
- The final `∀ (P' : Scheme.{u}) (g : P' ⟶ P)` allows every parameter base change,
  without a flatness, finiteness, or affineness restriction on g or P'.
- Its given immersion is literally `pullback.snd l g : pullback l g ⟶ P'`, and
  it is asserted to be closed and locally of finite presentation. This identifies
  the base-changed locus as L times_P P', rather than choosing some new locus.
- The final test clause is the same unique-lift criterion for this projection,
  with arbitrary `T` and `t : T ⟶ P'`. The right-hand map is explicitly the composite
  of `1_D × t : D ×_S T ⟶ D ×_S P'`, `1_D × g`, and F. Its source uses
  `((t ≫ g) ≫ p)`, and the intervening pullback uses `g ≫ p`, so it is exactly the
  induced family on D times_S P'. Associativity proof terms identify the two
  expressions for the induced S-structure and add no hypothesis.
- The statement imposes no smoothness, connectedness, reducedness, Noetherian,
  separatedness, or nonemptiness condition on D, P, Z, or any test scheme.

Dependency declarations used, with their full definitions/signatures and docstrings read:

| Node | Module | Declaration |
| --- | --- | --- |
| def-pc-scheme | Mathlib.AlgebraicGeometry.Scheme | AlgebraicGeometry.Scheme; AlgebraicGeometry.Scheme.Hom |
| def-pc-finite-locally-free | WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree | AlgebraicGeometry.Scheme.Hom.IsFiniteLocallyFree |
| def-sbc-locally-finite-presentation | Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation | AlgebraicGeometry.LocallyOfFinitePresentation |
| def-weil-closed-immersion | Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion | AlgebraicGeometry.IsClosedImmersion |
| def-pc-fibre-product | Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback | CategoryTheory.Limits.pullback; pullback.fst; pullback.snd; pullback.map |

Affineness uses Mathlib's `AlgebraicGeometry.IsAffineHom` from
`Mathlib.AlgebraicGeometry.Morphisms.Affine` (the existing proof-dependency node
`pqf-def-affine-morphism` records it). `Mathlib.AlgebraicGeometry.Pullbacks`
supplies existence of scheme pullbacks. These and the statement-dependency modules
are public imports. No dependency interface required repair.

Plain proof imports retain the recorded modules for:
`lem-sc-finite-pushforward-locally-free`, `def-weil-finite-integral-morphism`,
`lem-weil-pbc-affine-opens-basis`, `lem-weil-pbc-open-fibre-product`,
`lem-weil-pbc-fibre-product-affine-spectra`, `lem-weil-pbc-free-module-base-change-free`,
`lem-weil-pbc-morphism-into-affine-scheme`, `def-sbc-closed-immersion-ideal-sheaf`,
`lem-weil-pbc-affine-finite-type-generating-sections`, `def-weil-pbc-projective-module`,
`lem-pc-affine-containment-ideal`, `lem-pc-proper-monomorphism-closed`,
`lem-weil-pbc-scheme-morphism-gluing`, `lem-weil-pbc-closed-immersion-base-change`,
`lem-weil-pbc-glue-schemes`, `lem-weil-pbc-closed-immersion-affine-cover-criterion`,
`lem-weil-pbc-quasi-coherent-finite-type-affine`, and
`lem-pc-closed-subscheme-base-change-ideal-image`. Modules also needed publicly by the
signature are imported publicly once. The proof dependency
`lem-trf-closed-immersion-finite-presentation-ideal` has no recorded Lean module or
Mathlib match and is therefore not imported; it is a proof input, not a missing
notion needed to state this item.

Edge cases checked before writing:

- Empty D, including rank-zero components: all source maps factor uniquely through
  Z and the locus is P, with its identity closed immersion.
- Varying rank: `IsFiniteLocallyFree` allows it; no degree parameter occurs.
- Z = X: the locus is P; an empty P or empty test T is allowed.
- Empty Z: factorization holds precisely when the pulled-back source is empty;
  the rank-zero part is preserved, so there is no incorrect claim that the locus
  must be empty when D has some empty fibres.
- A nonreduced finite locally free source, for example dual numbers, still tests
  all coefficients; the criterion is scheme-theoretic and includes nonreduced tests.
- Arbitrary nonflat g and arbitrary non-affine tests are explicitly quantified;
  the argument uses no tensor injectivity or affine restriction on these tests.
- A non-quasi-compact parameter is allowed: finite presentation is a property of
  the closed immersion, not a quasi-compactness assumption on the parameter scheme.

Searches made for an existing statement:

- `msearch.py leanfinder`: “A family of maps from a finite locally free scheme
  factors through a finitely presented closed subscheme on a finitely presented
  closed parameter locus”. Eight hits, including `LocallyOfFinitePresentation`,
  affine-transition-limit factorization statements, and `specTargetImageFactorization`;
  none gives this universal parameter locus.
- `msearch.py loogle`: `"WeilRestriction", "IsFiniteLocallyFree"`: no hits.
- `msearch.py grep`: `WeilRestriction|factorization.?locus|containment.?locus`,
  in Mathlib/AlgebraicGeometry: no hits.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for factorization/containment loci,
  finite-locally-free factorizations, and the proposed declaration/module names;
  `grep -rn` of the exact node id in WeilConjectures; and the upstream name index:
  no exact statement or name collision.
- Read `Sheaf.AlgebraicGeometry.ConstantSourceClosedFactorizationLocus`:
  its `existsUnique_constantSource_closedFactorizationLocus` requires a field and
  finite type separated schemes and says nothing about finite presentation of the
  locus. It is not this relative finite locally free statement.
- Read `WeilConjectures.AlgebraicGeometry.Hilbert.ClosedImmersion`,
  `exists_idealSheafData_le_ker_iff_comap_le`: it concerns a Hilbert subscheme of
  fixed degree in an ambient family and does not assert finite presentation of
  the locus. It is not an exact existing match either.

No node fault or disputed statement was found.

Validation: the prescribed `scompile.py Q16
lem-sfb-finite-locally-free-source-factorization-locus` compiled the file in both
sandbox mode and its library module path, with no error or unexpected warning.
All universes and variables are explicitly bound; `autoImplicit` is false.

## Second reading by Q16

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
