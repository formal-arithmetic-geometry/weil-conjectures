## Worker report

The module `Sheaf.AlgebraicGeometry.NormalizationImmersionFiniteStage` states
`AlgebraicGeometry.Scheme.Hom.exists_normalization_immersion_at_finite_stage` with `sorry`.
No definitions, new nodes, dependency modules, or statement corrections are needed.

Hypothesis and clause correspondence:

- Schemes `X,S` and `f : X → S`: `{X S : Scheme.{u}} (f : X ⟶ S)`.
- Separated: `[IsSeparated f]`.
- Finite type: `[LocallyOfFiniteType f] [QuasiCompact f]`, precisely the convention node.
- Everywhere quasi-finite: `_hf : f.IsLocallyQuasiFinite`, the dependency's Stacks
  predicate including finite type at every point, rather than Mathlib's weaker predicate.
- The base is quasi-compact and quasi-separated: `[CompactSpace S] [QuasiSeparatedSpace S]`.
- Relative normalization and its canonical maps: `f.normalization`, `f.fromNormalization`,
  and `f.toNormalization`, from Mathlib, as prescribed by the dependency's match.
  Their composition is `f` by `toNormalization_fromNormalization`.
- The canonical immersion is open: `[IsOpenImmersion f.toNormalization]`. Its required
  quasi-compactness is already a Mathlib instance from the finite-type hypothesis on `f`;
  a redundant quasi-compactness binder would convey no further assumption.
- The given finite-stage presentation is `F : f.fromNormalization.FiniteApproximation`.
  Read its whole structure: `I : Type u`, `SmallCategory`, `IsCofiltered`, `D`, structure
  maps `p`, their compatibility `map_p`, finiteness `isFinite_p`, cone `π`, limit proof
  `isLimit`, and compatibility `π_p`. Thus stages are finite S-schemes, projections are
  `F.π.app λ`, and transition maps are affine by `FiniteApproximation.isAffineHom_map`.
  The category encoding includes directed inverse systems and their cofiltered form;
  it does not impose an ordering beyond the filtered-limit hypothesis.
- Existence of an index, intermediate scheme, and two arrows: `∃ l₀ T j i`.
- `j` quasi-compact open: `IsOpenImmersion j ∧ QuasiCompact j`.
- `i` closed: `IsClosedImmersion i`.
- Factorization of the original canonical projection: `j ≫ i = f.toNormalization ≫ F.π.app l₀`.
- The same index has the locally Noetherian refinement:
  `IsLocallyNoetherian S → LocallyOfFinitePresentation (F.p l₀)`.
  `F.isFinite_p l₀` already ensures finiteness, quasi-compactness and quasi-separatedness,
  so local finite presentation is exactly the remaining component of finite presentation.
  The parenthetical case of locally finitely presented `f` over locally Noetherian `S`
  is covered by this implication without an extra hypothesis or separate clause.

Dependency declarations read and used:

- `Sheaf.AlgebraicGeometry.QuasiFiniteMorphism`:
  `AlgebraicGeometry.Scheme.Hom.IsLocallyQuasiFinite` and `IsQuasiFiniteAtPoint` (full
  definitions read, including the finite-type witness and recorded ring predicate).
- `Mathlib.AlgebraicGeometry.Normalization`: `Scheme.Hom.normalization`,
  `toNormalization`, `fromNormalization`, `toNormalization_fromNormalization`, the
  integral, dominant and quasi-compact instances, `normalizationObjIso`,
  `fromNormalization_app`, `normalizationObjIso_hom_val`, and the integral-scheme instance.
- `Mathlib.AlgebraicGeometry.ZariskisMainTheorem`: the open-immersion instance for
  `f.toNormalization`, read with its separated, locally finite-type, quasi-compact,
  locally quasi-finite hypotheses. The recorded dependency notes Mathlib's weaker
  quasi-finiteness encoding; this item instead uses the exact recorded project predicate.
- `Mathlib.AlgebraicGeometry.Noetherian`: `IsLocallyNoetherian`, the recorded class.
- `WeilConjectures.Mathlib.AlgebraicGeometry.ZariskisMainTheorem`:
  `Scheme.Hom.exists_finiteApproximation_of_isIntegralHom`, its `FiniteApproximation`
  result structure, and `FiniteApproximation.isAffineHom_map`.
- The scheme-conventions dependency introduces no declaration; the existing Mathlib
  properties above render its finite-type and finite-presentation conventions.

Existing theorem inspection: the upstream
`Scheme.Hom.FiniteApproximation.exists_isOpenImmersion_isClosedImmersion` was found and
its full signature, docstring and proof were read. It has arbitrary `ν : N ⟶ S` and an
arbitrary open immersion into `N`; it does not state the node's canonical relative
normalization or the separated, finite-type, everywhere-quasi-finite hypotheses on `f`.
It supplies the general result from which this exact specialized statement follows.
No second notion or alternate finite-approximation structure has been introduced.

Edge cases: the empty source is allowed, and no nonempty scheme is assumed. The empty
base likewise causes no excluded case. `IsCofiltered F.I` gives a nonempty index category,
so the existential index is not incorrectly demanded of an empty presentation. Index,
stages and schemes share universe `u`; there is no independent undersized test universe.
There are no field, characteristic, reducedness, or integrality assumptions on `X` or `S`.
The final refinement uses the same index and arrows, including when `S` is locally
Noetherian and when it is not. No statement dispute or node fault was found.

Searches:

- `msearch.py ... leanfinder "A quasi-compact open immersion into relative normalization
  descends to an open immersion followed by a closed immersion at a finite stage"`:
  eight component hits (normalization, its maps and instances), no full target theorem.
- `msearch.py ... loogle "FiniteApproximation, IsOpenImmersion, IsClosedImmersion"`:
  zero hits, unknown identifier `FiniteApproximation`.
- `msearch.py ... grep "exists_isOpenImmersion_isClosedImmersion|FiniteApproximation"
  AlgebraicGeometry`: zero Mathlib hits.
- `rg` of `WeilConjectures/` and `lean/Sheaf` for finite approximation, immersion descent,
  and quasi-finite names: found the general upstream theorem above and the existing
  project quasi-finite predicates; no specialized theorem with this signature.
- `grep -rn "thm-pqf-immersion-descent" WeilConjectures/`: the general theorem's docstring
  and a component limit-immersion lemma carry the tag; neither states the full specialized
  node signature. `dag/lean_names_upstream.json`, Mathlib, project and upstream source
  name searches found no collision with `exists_normalization_immersion_at_finite_stage`.

Validation: server single-file compilation and the delivery dry run are run before READY.
The independent second reading is reserved for the dispatcher’s second reader.

## Second reading by U1

The node introduces the following data and clauses, matched against the Lean declaration
`AlgebraicGeometry.Scheme.Hom.exists_normalization_immersion_at_finite_stage` in
`Sheaf.AlgebraicGeometry.NormalizationImmersionFiniteStage`:

- `X S : Scheme.{u}` and `f : X ⟶ S` render the source schemes and morphism exactly.
- `[IsSeparated f]`, `[LocallyOfFiniteType f]`, and `[QuasiCompact f]` render separated and
  finite type (the latter is locally finite type plus quasi-compact), with no extra finiteness.
- `_hf : f.IsLocallyQuasiFinite` is the recorded Stacks everywhere-quasi-finite predicate,
  including its local finite-type witness.
- `[CompactSpace S] [QuasiSeparatedSpace S]` render the qcqs base assumptions.
- `f.normalization`, `f.fromNormalization`, `f.toNormalization`, and
  `F : f.fromNormalization.FiniteApproximation` render the relative normalization, its
  canonical maps, and the cofiltered finite-stage presentation. `F.π.app l₀` is the stage
  projection and `F.p l₀` its structure map; transition maps are affine by the dependency
  declaration.
- `∃ (l₀ : F.I) (T : Scheme) (j : X ⟶ T) (i : T ⟶ F.D.obj l₀)` renders the existential
  index, intermediate scheme, and two arrows.
- `IsOpenImmersion j ∧ QuasiCompact j ∧ IsClosedImmersion i` renders the two requested
  factor properties.
- `j ≫ i = f.toNormalization ≫ F.π.app l₀` is the required factorization equation.
- `(IsLocallyNoetherian S → LocallyOfFinitePresentation (F.p l₀))` renders the same-index
  locally Noetherian finite-presentation refinement; finiteness, quasi-compactness, and
  quasi-separatedness of every stage come from `FiniteApproximation.isFinite_p` and its
  instances.

The prior worker had added `[IsOpenImmersion f.toNormalization]` to the theorem binders. That
is an extra hypothesis: the node lists the canonical immersion as a consequence of the
normalization-open dependency under the stated separated finite-type everywhere-quasi-finite
assumptions. I removed that binder from the Lean signature and made the node's `lean.statement`
verbatim match the corrected signature. No other mismatch was found. The node's statement
itself was not changed.

Edge cases checked: empty source and empty base schemes remain admissible; no nonemptiness of
`X` or `S` is assumed. `F.I : Type u` has the scheme universe and carries `IsCofiltered`, so the
presentation supplies an index and does not introduce an empty-index loophole. Zero or empty
stages are not excluded beyond the stated finite-stage structure. No field, characteristic,
reducedness, integrality, or independent test universe is introduced; `n = 0` is irrelevant to
this statement.

Searches were reread from the worker packet and checked with `rg` over Mathlib, the source
repository, and `lean/Sheaf`, plus the recorded LeanFinder/Loogle/grep searches. The general
upstream `FiniteApproximation.exists_isOpenImmersion_isClosedImmersion` theorem is not the exact
canonical-normalization statement, and no duplicate specialized theorem exists.
