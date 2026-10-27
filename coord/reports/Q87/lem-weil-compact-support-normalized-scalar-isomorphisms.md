## Worker report

The module `Sheaf.Paper.CompactSupportNormalizedScalarIsomorphisms` states
`WeilConjectures.sfCompactSupportNormalizedScalarIsomorphisms`, with a single `sorry`.
It also constructs the actual whole-system scalar map (a composite of existing
canonical maps) and the base-field-to-residue-field transport of the given unit.
Neither helper has postponed data or an additional theorem. The node is unchanged
outside `lean`; no definition nodes or dependency repairs are needed.

Sources read: main-20261015 `lem-weil-compact-support-finite-field-independence.proof.md`,
first sentence, and `lem-fix-operation-reduction.proof.md`, compact-support and final
paragraphs. The six-step proof docstring follows the current accepted split, including
the Roos-leg adjunct argument and the etale scalar-extension boundedness argument.
The example `CategoryTheory/CompactObject.lean` is withdrawn in the current source;
the file follows the current module-mode header convention and the live dependency
modules instead.

Hypotheses and objects, matched individually:

- A field K₀: `(K₀ : Type u) [Field K₀]`.
- Schemes X and Y over K₀: `{X Y : Scheme.{u}}`, each with
  `[W.Over (Spec (.of K₀))]`.
- Finite type of X and Y over K₀: `LocallyOfFiniteType` and `QuasiCompact` of
  each structure morphism. The convention node fixes finite type to these properties.
- The K₀-morphism f: `{f : X ⟶ Y}` and `[f.IsOver (Spec (.of K₀))]`.
- Separated finite type f: `[IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]`.
  No separatedness of either structure morphism is assumed.
- Prime ℓ and its invertibility: `(l : ℕ) [Fact l.Prime] (hl : IsUnit (l : K₀))`.
- Algebraic closure Ω: `(Ω : Type v) [Field Ω] [Algebra (Padic l) Ω]`
  and `[IsAlgClosure (Padic l) Ω]`. Its universe v is independent of the scheme
  universe u.
- The same compactification at all levels: `(c : Compactification f)`.
- Individual finite subextensions and inclusion: `(E L : Padic.FiniteCoefficientFields
  l Ω) (h : E ≤ L)`. `AlgebraicallyClosedCoefficients.Coefficient.{u}` and
  `coefficientInclusion` are the existing canonical Shrink models, so finite
  subextensions are not required to have the scheme's original universe.
- Categorical objects: the existing `sfIntegralConstructibleCategory` is exactly the
  derived-complete bounded constructible category, and `sfRationalConstructibleCategory`
  is its raw tensor-Hom localization, with unchanged objects and no Karoubi completion.
- Fixed actions F and G: `sfCompactSupportFiniteIntegralFunctor` and
  `sfCompactSupportFiniteFunctor`, with no arbitrary replacement functor. Their recorded
  definitions fix the compact-support values, strict tower and projections, and give
  the pure-tensor morphism formula `a ⊗ v ↦ a ⊗ F(v)`.
- Completed integral transitions and their rationalizations: `integralTransition`
  and `transition`, the published intrinsic scalar-extension functors specialized to
  the canonical coefficient inclusion. The redundant characteristic parameter is 0
  with the proof that the prime is nonzero, exactly as in the recorded stage interface;
  it imposes no characteristic-zero assumption on K₀.

Conclusion clauses, matched individually:

- `∃ b : F_E ⋙ integralTransition ... Y ≅ integralTransition ... X ⋙ F_L`
  is the integral natural isomorphism. Lean functor composition is diagrammatic,
  so these endpoints are respectively T_Y F_E and F_L T_X.
- The first conjunct is the dependency's exact
  `SfCompactSupportIntegralBetaSpec ... b`, not a new approximation to it.
  Unfolding that predicate gives, for every integral K and `n : ℕ`, the coefficient
  rings `Padic.coefficientExtensionRing l E (n+1)` and the inclusion-induced
  `integralScalarQuotientMap`. No flatness or injectivity is imposed on this map.
- Its A, M and N are the actual derived reductions appearing in the node. Its ηM is
  `sfMixedCompletedReductionUnit ... X n K.obj`; its ηN is the inverse fixed
  `sfCompactSupportFiniteReductionIso` followed by
  `sfMixedCompletedReductionUnit ... Y n (F_E.obj K).obj`, exactly as prescribed.
- The existential `hN` inside that existing predicate states `Function.Bijective`
  for `a ↦ ηN ≫ R.map a`, for EVERY target in `proEtaleDerivedCategory Y S_n`.
  Z is unrestricted: no boundedness, constructibility or completeness is imposed.
- The predicate's final equality identifies reduction of `b.hom.app K` followed
  by the fixed target reduction isomorphism with `sfCompactSupportFiniteMate`.
  That definition is the inverse of precisely the above bijection applied to
  compact support of ηM followed by `sfCompactSupportRestriction`. Thus it gives
  both the transpose equation and uniqueness of its solution.
- These are the recorded mixed units themselves. `sfMixedReductionUnit` has the
  sheafified-tensor formula s⊗x ↦ ι_n(s)⊗(1⊗x);
  `sfMixedReductionDerivedUnit` is fixed by the entire homotopy-category square
  with the universal reduction counits; `sfMixedCompletedReductionUnit` composes
  with `scalarCompletion`, the prescribed diagonal Roos map. The statement does
  not replace this normalization by cohomology equations.
- The middle conjunct asserts `(b.hom.app K).hom = sfCompactSupportScalarSystemMap ... K`
  on EVERY integral K. The helper is the following actual composite: completed
  scalar extension of `FrobeniusExchange.compactRealization.hom`, followed by
  `FrobeniusExchange.coefficientExchange` of `systemCompactScalar`, followed by
  the target `compactRealization.inv`. The system mate is the proper derived
  coefficient mate and proper image of the normalized open mate on whole ringed
  sequence systems. `coefficientExchange` uses the normalized source realization,
  its whole-system reduction counit, limit of this mate and inverse scalar-reduction
  counit. `compactRealization` is fixed by the exact Roos projections and both cone
  coordinates. This retains the statement's actual strict-system/derived-limit
  realization, beyond the finite-reduction clause.
- The final existential is a natural ISO β between the fixed rational functor
  composites. For every rational input K its hom component is `HEq` to the raw
  localization of `b.hom.app K.obj`. HEq only accommodates the recorded rational
  scalar transition's propositionally specified object equality; it does not
  forget any map. A natural isomorphism includes invertibility and naturality on
  all raw tensor Hom morphisms. Its inverse is consequently the localization
  of the integral inverse.
- E, L, h are inputs for one inclusion. There is no tower associator, coherence,
  common-stage independence, or global coefficient action in the conclusion.

Dependency declarations used, with their recorded module interfaces read:

- `def-weil-scheme-morphism-properties` is a convention node with no declaration.
  Its finite-type and separated variants are the existing Mathlib classes above.
- `Sheaf.Paper.SfRationalizationKaroubi`:
  `sfRationalConstructibleCategory`, `sfRationalConstructibleLocalization`,
  `sfRationalScalarExtension` (and its full unique tensor-Hom specification).
- `Sheaf.Paper.QcqsCompactSupportRealization`:
  publicly retained `sfIntegralCompactSupportValue`, `sfRationalCompactSupportValue`,
  and `sfQbarCompactSupportValue`, and its projection-normalized
  `sfQcqsCompactSupportRealization` interface. This public import is retained as
  the current recorded statement dependency.
- `Sheaf.Paper.CompactSupportFiniteAction`:
  `SfCompactSupportFiniteRealizationSpec`, `sfCompactSupportFiniteIntegralFunctor`,
  `sfCompactSupportFiniteFunctor`, `sfCompactSupportFiniteReductionIso`.
- `Sheaf.Paper.IntegralScalarExtensionUniverses`:
  `integralScalarExtensionOfUniverses` and its publicly retained
  `integralScalarExtension`; the two use the identical universal-localization witness
  at equal universes. The constructed helper uses these exact functors, as required
  by the published system API.
- `Sheaf.Paper.CompactSupportCoefficientAction`:
  `SfCompactSupportIntegralBetaSpec`, `sfCompactSupportFiniteMate`. Existence of
  `SfCompactSupportCoefficientAction` is NOT assumed.
- `Sheaf.Paper.MixedReductionUnit`:
  `sfMixedReductionUnit`, `sfMixedReductionDerivedUnit`,
  `sfMixedCompletedReductionUnit`, including their normalization docstrings and
  full homotopy square.
- `Sheaf.Paper.SystemOperationExchangeRealization` (already a proof dependency,
  public here since the helper's type/body refers to the actual system maps):
  `FrobeniusExchange.systemCompactScalar`, `coefficientExchange`, `compactRealization`.
- `Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients` (publicly inherited):
  `integralTransition`, `transition`, `Stage`, and the existing canonical coefficient
  models from `Sheaf.Paper.AlgebraicallyClosedCoefficients`.

Every stated proof-dependency module is imported. The Noetherian Mathlib leaf has
no `lean` record and is imported via `Mathlib.AlgebraicGeometry.Noetherian`, including
its quasi-compactness dependency. Nothing has been restated for that leaf.

Edge cases checked before writing and in the final signature:

- Identity inclusion E=L is allowed (`h` need not be strict); no unramifiedness is
  required. The actual quotient maps are used.
- `n=0` means the positive exponent 1 in the existing predicate. All natural n
  are quantified, including ramified extensions where the quotient map is neither
  flat nor injective. No proof uses such an assumption.
- K=0 is included and no nonzero or nonempty condition is introduced.
- Empty X and empty Y are not excluded; residue-field invertibility is transported
  pointwise and is vacuous when there are no points. No choice of a point is made.
- Z in the Hom bijection may be unbounded; the quantifier ranges over the entire
  finite-coefficient derived category.
- Arbitrary base characteristic with l invertible is retained. The initial compiler
  diagnostic concerned required residue-field `Invertible` data in the published
  realization API. The added helper constructs it by transporting the GIVEN K₀-unit
  through Γ(Spec K₀) → Γ(W) → κ(x). No additional theorem or hypothesis was added.
- Ω is allowed in an independent universe, using the existing finite-dimensional
  coefficient Shrink transport. The small pro-etale object/morphism universes are
  those of the existing categories, with no new equality imposed on them.

Searches actually run for this item:

- `msearch.py ... leanfinder "Normalized integral compact support scalar extension
  natural isomorphism with mixed derived tensor unit mate and raw rational localization"`:
  8 hits, including `ModuleCat.homEquiv_extendScalarsComp`, the tensor-unit and
  extension/restriction Hom-equivalence lemmas, and unrelated normalization lemmas.
  These give elementary scalar adjunctions, not the completed compact-support claim.
- `msearch.py ... loogle "NatIso, Functor.mapIso"`: returned
  `loogle: unknown identifier 'NatIso'` (unavailable query, not evidence of no match).
- `msearch.py ... grep "compactSupport.*[Ss]calar|[Ii]ntegralBeta|[Nn]ormalizedScalar"`:
  zero Mathlib hits.
- `msearch.py ... leansearch "Compact support direct image natural isomorphism under
  completed coefficient scalar extension"`: 8 hits, including
  `SheafOfModules.pushforwardCongr` and compactly supported continuous-function lemmas;
  none is this completed integral comparison with the fixed mixed-unit normalization.
- Direct `rg` of `lean/WeilConjectures`, `lean/Sheaf` and `dag/lean_names_upstream.json`
  for the item id and normalized scalar/beta names: no exact theorem; the project
  hits supply precisely the predicates and constructions reused here. A broader
  compactSupport/lowerShriek scalar search found the upstream finite-coefficient
  `lowerShriekWeilDatum_extendScalarsWeilDatum` and the existing compact-support
  scalar transport modules. Those concern finite coefficients, Frobenius compatibility,
  or separated/finite-Tor domains, not this normalized qcqs integral/rational statement.

Validation: the final file compiled via `scompile.py Q87
lem-weil-compact-support-normalized-scalar-isomorphisms` in both sandbox and actual
library-module modes, with no errors or warnings (50.6 s and 58.5 s).
All variables and universes are explicit and `autoImplicit` is false. The only
postponed theorem is the main theorem named above. No statement dispute or source
correction is needed.

## Second reading by Q87

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
