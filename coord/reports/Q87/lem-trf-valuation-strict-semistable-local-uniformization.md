## Worker report

This delivery repairs the inherited statement in
`Sheaf.TraceFormula.ValuationStrictSemistableLocalUniformization` and states
`AlgebraicGeometry.valuation_strict_semistable_local_uniformization`. The theorem's entire
proof is `sorry`. No theorem is proved and no definition is introduced. The inherited
canonical generic-point residue-field condition is retained. The new changes implement
full finite presentation, reuse the landed relative strict-semistability predicate, and
characterize the induced generic-fibre map by BOTH pullback projection equations.

Source read: Temkin, *Stable Modification of Relative Curves*, arXiv:0707.3953v3, §1.2
(relative curves), opening conventions of §4 (finite-height valuation ring and separably
closed fraction field), §4.3 (relative strict charts), and Proposition 4.3.3, printed
pp. 29–30. A PDF and its text extraction are retained in the sandbox scratch directory.
No repair-note file exists for this item. The previous node's `statement_change` is
preserved whole under `statement_change.previous`.

Hypotheses, one by one:

- `{V K : Type u}` supplies the valuation domain and its fraction field in the scheme
  universe; `[CommRing V] [IsDomain V] [Field K] [Algebra V K] [IsFractionRing V K]`
  is the injective presentation of the given inclusion with fraction field K.
- `[ValuationRing V]` is the valuation-ring condition, not discreteness or rank one.
  `[IsSepClosed K]` is separable closedness. `hchain` explicitly retains comparability of
  primes and `hfinite : Finite (PrimeSpectrum V)` retains finite height. No excellence,
  Noetherianity, characteristic or properness condition is added.
- `X : Scheme.{u}` and `c : X ⟶ Spec (CommRingCat.of V)` are the given relative curve.
  `[Flat c]` expresses flatness. `[LocallyOfFinitePresentation c] [QuasiCompact c]
  `[QuasiSeparated c]` together express FINITE presentation as required by §1.2; the
  last two were missing from the inherited Lean translation.
- `hcurve` quantifies every `s : Spec V` and every `Z ∈ irreducibleComponents (c.fiber s)`
  and sets `topologicalKrullDim Z = 1`. This is the recorded pure relative dimension
  condition, and permits empty fibres.
- `[Smooth (pullback.snd c (Spec.map ... (algebraMap V K)))]` is smoothness of the actual
  generic-fibre structure map to Spec K. No geometric-connectedness hypothesis is added.

Conclusions, clause by clause:

- `∃ (n : ℕ) (Y : Fin n → Scheme.{u}) (y : ∀ i, Y i ⟶ X)` gives a finite list of models
  with the specified maps. `n = 0` is permitted.
- `∀ i, IsIntegral (Y i)` requires integrality, including nonemptiness of each member.
- `∀ i, IsStrictlySemistableCurve (y i ≫ c)` uses the exact existing predicate in
  `Sheaf.AlgebraicGeometry.StrictlySemistableCurve`. Its first four conjuncts are
  flatness, local finite presentation, quasi-compactness and quasi-separatedness; its
  next clause gives pure dimension one in every fibre. Its final clause gives Zariski
  neighbourhoods and étale affine-line/nodal charts, with the coefficient structural map
  equalling `U.ι ≫ y i ≫ c`. Thus these are charts OVER the given base. The nodal
  chart is the existing universal nodal chart pulled back by its parameter, canonically
  Spec A[u,v]/(uv-a); the affine-line chart is Spec (Polynomial A). Restricting such
  neighbourhoods to affine ones recovers the node's affine-source presentation.
- `∀ i, IsSeparated (y i) ∧ LocallyOfFiniteType (y i) ∧ QuasiCompact (y i)` supplies
  separated finite type for the quasi-modification; it imposes no separation of `c`.
- The next conjunct supplies a component `C`, its generic point `ξ`, every image point
  of `Y i` in `C`, and `ηᵢ` generic in `Y i`, with `(y i).base ηᵢ = ξ` and
  `Function.Bijective ((y i).residueFieldMap ηᵢ).hom`. This is birationality through
  the CANONICAL residue-field map of the displayed morphism. It is not an unrelated
  field isomorphism or an unreduced generic stalk.
- The next conjunct supplies `j` between the ACTUAL two generic pullbacks. Its first
  equation is `j ≫ pullback.fst c η = pullback.fst (y i ≫ c) η ≫ y i`; its second is
  `j ≫ pullback.snd c η = pullback.snd (y i ≫ c) η`. These determine the canonical
  base change of `y i` by pullback uniqueness. `IsOpenImmersion j` therefore asserts
  that the given generic map identifies its source with an open subscheme. The inherited
  statement had only the second equation, permitting a map unrelated to `y i`.
- The last conjunct quantifies EVERY component `C`, generic point `ξ`, valuation
  subring `W : ValuationSubring (X.residueField ξ)`, and morphism `z : Spec W ⟶ X`.
  The equality `z.base (⊥ : PrimeSpectrum W) = ξ` is exactly its stipulated centre
  condition. The conclusion `∃ i, ∃ l : Spec W ⟶ Y i, l ≫ y i = z` is the required
  factorization through a member of the same finite list.

Dependency declarations read in their source modules and used:

- `Mathlib.FieldTheory.IsSepClosed`: `IsSepClosed`, with the dependency's companion
  `IsSepClosure` also inspected. Only separable closedness is needed here.
- `Mathlib.Topology.KrullDimension`: `topologicalKrullDim`.
- `Mathlib.AlgebraicGeometry.Properties`: `IsIntegral` and `IsReduced`; the former is
  explicit, while the component fields use residues, valid for reduced components.
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`:
  `LocallyOfFinitePresentation`, with finite presentation completed by the recorded
  `QuasiCompact` and `QuasiSeparated` notions.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `Smooth`; its
  `SmoothOfRelativeDimension` interface was inspected as well.
- `Mathlib.AlgebraicGeometry.Scheme`: `Spec`, `Spec.map`.
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `Etale`, used by the shared chart predicate.
- `Mathlib.Algebra.Field.Defs`: `Field` (the field dependency has status mathlib and
  its `mathlib_match` is used; no new Lean record is required).
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType` and `.QuasiCompact`:
  `LocallyOfFiniteType` and `QuasiCompact`.
- `Mathlib.AlgebraicGeometry.Morphisms.Flat`: `Flat`, the same stalkwise notion.
- `Mathlib.Topology.Irreducible`: `irreducibleComponents` (the dependency's mathlib match).
- `Mathlib.Algebra.Polynomial.Basic`: `Polynomial`, used through the shared chart predicate.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper` and `.Separated`: `IsSeparated`, the
  separatedness portion of the recorded proper-morphism dependency.
- `Mathlib.AlgebraicGeometry.ResidueField`: `Scheme.Hom.residueFieldMap` and
  `Scheme.residueField`, canonical generic component fields.
- `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`: `QuasiSeparated`, the new
  direct dependency needed to spell out the source's finite presentation.
- `Sheaf.AlgebraicGeometry.StrictlySemistableCurve`: `IsStrictlySemistableCurve`,
  read both in the local source and through `scompile.py --source`. This is a newly
  CITED landed node, not a new definition or a dependency repair. Its pure-fibre
  predicate is the recorded `Scheme.IsPureDimension` in
  `Sheaf.AlgebraicGeometry.PureDimension`, definitionally the componentwise condition.

The declaration docstring reproduces all TWELVE existing DAG proof steps, including
all named citations: affine horizontal reduction; valued étale parameter; Riemann–Zariski
approximation; étale algebra descent; finite-presentation factorization; strict cofinality;
base change and flat finite presentation; fibre dimension; relative chart composition and
quasi-modification; generic quasi-finiteness/Zariski main; finite birational normal image;
and finite valuation-cover extraction, including empty X. `citations.json` retains a
verbatim quote for every cited node of every step. No proof or proof dependency was changed.

Edge cases checked before finalizing:

- Empty X permits `n = 0`; no integral empty member is demanded. Empty fibres satisfy
  the pure-dimension clauses vacuously, as in the recorded definition.
- Disconnected generic fibres are handled by separate component witnesses; no common
  function field or connectedness premise is introduced.
- The trivial valuation `V = K`, height zero, and the valuation `W = X.residueField ξ`
  remain allowed. There is no rank-one or nontrivial-valuation assumption.
- Without full finite presentation an infinite disjoint union of affine lines over a
  separably closed field satisfies flatness/local finite presentation/pure dimension one
  but cannot be covered by finitely many integral models. The corrected inputs exclude
  precisely this non-quasi-compact impostor, as the source does.
- An unrelated affine-line chart on a flat finite map such as `t ↦ t²` does not establish
  relative smoothness or semistability. The imported predicate's base-map equations
  prevent this error. Both nodal and smooth chart branches, including `a = 0`, remain.
- An open immersion between two abstract generic fibres alone does not assert the
  displayed map is open: the two projection equations now specify the actual induced
  map. Identity generic maps and arbitrary permitted component maps are retained.
- All universes and variables are explicitly bound, with both auto-implicit options off.
  No field extension test, valuation or component is silently replaced by an unrelated
  type or an arbitrary chosen map.

Searches actually run with `msearch.py Q87` (full machine results in `searches.jsonl`):

- LeanFinder: “Finite strictly semistable local uniformization of a curve over a valuation
  ring covering centred valuations”: 8 results, all Weierstrass valuation/minimal/good
  reduction or valuation-uniformizer results; no matching local-uniformization theorem.
- LeanSearch: “Strictly semistable local uniformization covering valuations of a relative
  curve over a valuation ring”: 8 uniformizer or valuation-local-ring results; no match.
- Loogle: `AlgebraicGeometry.IsStrictlySemistableCurve`: unknown identifier in its Mathlib
  index, so unavailable for the project predicate; it is not evidence that the predicate
  is missing from this project.
- Loogle, `"semistable"`: zero hits.
- Mathlib grep: `semistable|uniformization|quasi.modification` in AlgebraicGeometry:
  zero hits. Direct `rg` of upstream WeilConjectures for these expressions and for this
  item id returned no matches.
- Direct `rg` in `lean/Sheaf` found the inherited theorem in its owning module and the
  existing `IsStrictlySemistableCurve` predicate. The inherited theorem is NOT an exact
  existing match, for the three defects detailed above, so it is repaired in place in
  its sandbox module rather than recorded as `existing: true` or duplicated elsewhere.

No new definition nodes, no dependency modules, no theorem proofs and no unresolved
mathematical dispute are introduced. The packet needs the independent maintainer review;
the final validation evidence is appended after the prescribed wrappers return.

## Statement corrected

The natural-language clarification follows exactly the source places listed above:
finite presentation means local finite presentation plus quasi-compactness and
quasi-separatedness; a relative strict-semistable chart commutes with the base map;
and the generic map is the one induced by the specified `y i`. The prior Lean
translation missed these. The node now cites the already landed
`def-trf-strictly-semistable-curve` and `def-weil-quasi-separated-morphism`. The proof,
proof dependencies and all other mathematical objects are retained. The previous
canonical residue-field correction is retained under `statement_change.previous`.

The old statement, verbatim:

Let $K$ be a separably closed [def-kun-separably-closed] field [def-weil-field] and $V\subset K$ a valuation ring with fraction field $K$: for every $a\in K^\times$, either $a$ or $a^{-1}$ lies in $V$. Assume that the prime ideals of $V$ form a finite chain, and put $T=\operatorname{Spec}V$ [def-weil-affine-spectrum], with generic point $\eta=\operatorname{Spec}K$. Let $X$ be a $T$-curve with smooth generic fibre [def-sbc-smooth-morphisms]. There are finitely many integral strictly semistable $T$-curves $Y_i$ and birational quasi-modifications $Y_i\to X$ such that every centred valuation of every irreducible component [def-weil-irreducible-components] of $X$ lifts to some $Y_i$. Each generic map $(Y_i)_\eta\to X_\eta$ identifies $(Y_i)_\eta$ with an open subscheme. A $T$-curve means a flat [def-weil-flat-morphism] finitely presented [def-sbc-locally-finite-presentation] $T$-scheme of pure relative dimension one, without a separatedness or properness assumption. Dimension is topological Krull dimension [def-kun-topological-krull-dimension]. A $T$-curve is strictly semistable if, locally on it and on $T$, it admits an etale morphism [def-weil-etale-morphism] to $\operatorname{Spec}A[t]$ or $\operatorname{Spec}(A[u,v]/(uv-a))$, where $\operatorname{Spec}A$ is an open of $T$ and $a\in A$; polynomial rings use [def-weil-polynomial-ring]. For an integral scheme $Y$ [def-pc-integral-scheme], its function field is the local ring at its generic point. A birational quasi-modification $Y\to Z$ is a separated finite-type morphism [def-weil-finite-type-morphism] identifying the function field of $Y$ with the function field of the reduced irreducible component of $Z$ represented by $C$; equivalently, for a generic point $\eta_Y$ of $Y$ mapping to a generic point $\xi$ of $C$, the canonical residue-field map $\kappa_X(\xi)\to\kappa_Y(\eta_Y)$ induced by $Y\to Z$ is an isomorphism. A centred valuation of that component means a valuation subring $W\subset\kappa_X(\xi)$, together with a morphism $\operatorname{Spec}W\to Z$ whose generic point is $\xi$. It lifts to $Y$ when this morphism factors through $Y$.

The complete actual citer audit (dependency-list membership, not incidental text):

- `lem-trf-valuation-common-strict-semistable-refinement`: holds=true. Its multipointed input is finitely presented, and the strict models and generic maps are relative to the specified base; the clarified clauses supply exactly its existing use.
- `lem-trf-valuation-stable-reduction`: holds=true. Its multipointed input is finitely presented, and the strict models and generic maps are relative to the specified base; the clarified clauses supply exactly its existing use.

No citer is edited. The refinement uses a multipointed finitely presented relative curve R;
the stable-reduction proof uses the finitely presented multipointed target X. Their uses
therefore satisfy full finite presentation and use precisely the relative charts and actual
generic maps delivered here.

## Second reading by Q87

This is a second pass by the delivering worker, not a claim of an independent agent review.
The maintainer performs the independent review. I reopened the corrected node, shared
strict-semistability definition, source §1.2/§4.3, and the full final Lean signature.

The corrected inputs match field, valuation-ring inclusion, finite prime chain, the actual
base Spec V, flat FULLY finitely presented relative curve, every fibre's component dimension,
and smoothness of the generic structure map. The finite family has integral members; the
shared strict-semistability predicate retains flatness, all three finite-presentation clauses,
pure fibre dimension and both relative étale-chart branches; the quasi-modification has
separated finite type; its generic point maps to the chosen component generic point with
bijective CANONICAL residue-field map. Both generic pullback projection equations are now
present, so the open immersion belongs to y itself. The final quantifier includes every
component, every generic point, every valuation subring of its canonical field, and every
stated centred map, with the exact factorization equality. Empty families/fibres and height
zero are included. The three inherited translation mismatches were fixed as listed; no
further mismatch was found in this second pass.

Proof-import audit: available stated proof dependencies are imported without `public`.

- `lem-trf-birational-riemann-zariski-neighbourhoods`: not yet stated: no Lean record or Mathlib match.

- `lem-trf-valued-curve-etale-parameter`: not yet stated: no Lean record or Mathlib match.

Validation: `scompile.py Q87 lem-trf-valuation-strict-semistable-local-uniformization`
compiled the repaired declaration, then the version with its available proof imports,
with exit code 0 and no Lean warnings or errors. The final prescribed
`deliver2.py Q87 lem-trf-valuation-strict-semistable-local-uniformization --no-push`
returned exit code 0 and printed `OK (dry run): commit a24724b975 passes the preflight
and compiles; nothing pushed`. It checked the final signature, both added landed
statement dependencies, correction history and complete two-citer record. A direct
JSON comparison confirms that only `lean`, `statement`, `stmt_deps`, and
`statement_change` differ from the base node; `proof` and `proof_deps` are unchanged.
All Lean lines are at most 100 characters, and the recorded signature is the exact
keyword-to-`:=` text from the module.
