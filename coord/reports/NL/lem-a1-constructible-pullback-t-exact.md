## Worker report

The module `Sheaf.Paper.ConstructiblePullbackTExact` states every clause of
`lem-a1-constructible-pullback-t-exact`. All four theorems have `sorry` proofs;
the helpers have actual data or are transparent packages of the node's clauses.
There are no new DAG notions, dependency repairs, or statement corrections.

Hypotheses and objects:

- The global datum is `D : FiniteFieldDatum.{u}`. This carries p, a, q, both fields,
  the finite cardinality, and the fixed algebraic closure.
- The prime is `l : ℕ` with `[Fact l.Prime]`; `hl : l ≠ D.p` is retained.
- The closure is `Ω` with `[Field Ω] [Algebra (Padic l) Ω]
  [IsAlgClosure (Padic l) Ω]`. The t-exactness and pullback-scalar assertions
  use an independent closure universe v. The geometric-point fibre uses the
  same size convention as its recorded declaration `pointQbarFibre`.
- The finite coefficient field contained in Ω is `E : Index l Ω`. As in the
  recorded `Stage`, its coefficient carrier is `Coefficient.{u} l Ω E`, the
  canonical Shrink model of the actual finite subfield. This uses the recorded
  coefficient algebra equivalence and does not substitute a different category.
- `W` and `X` are schemes with their `Over (Spec (.of D.k))` structures.
  `LocallyOfFiniteType` and `QuasiCompact` on their structure morphisms state
  precisely finite type. The morphism `h : W ⟶ X` is arbitrary: no `IsOver`
  condition is imposed, and no smoothness, flatness or fibre bound is assumed.
- The point is exactly `x : Spec (.of D.k) ⟶ X`. The given datum makes D.k
  algebraically closed. The point is not required to preserve the k-structure.
- The residue-field `Invertible` instances needed by the recorded pullback API
  are constructed by `constructiblePullbackResidueUnits` from the existing
  `constructibleTruncations_exists`. They are not extra assumptions. This
  extraction is permitted data: each inverse is unique (`Invertible` is a
  subsingleton), so the unproved theorem determines the object completely.

Clause-by-clause rendering:

1. `constructible_pullback_t_exact` gives comparison data for both
   `rationalDerivedPullback` and `commonStageDerivedPullback`. In
   `ConstructiblePullbackComparison`, `tExact : F.IsTExact t s` reuses the
   existing upstream class. Its `isLE` and `isGE` fields say both standard
   halves are preserved for every n; n = 0 gives the two displayed inclusions,
   and the remaining cases are their shift forms.
   The t-structures are the recorded `sfRationalStandardTStructure` and
   `sfCommonStageStandardTStructure`, characterized by exactly the recorded
   standard classes, rather than alternative ambient rational sheaf categories.
2. `heart` is a functor between the actual full hearts, using
   `sfRationalHeartProperty` or `sfCommonStageHeartProperty`. `heart_fac`
   is equality after the full inclusions with the original pullback. Thus this
   is its restriction on objects AND maps. `heart_limits` and
   `heart_colimits` express exactness on these abelian hearts.
3. `truncLE`/`truncGE` are natural isomorphisms; `truncLE_counit` and
   `truncGE_unit` give the canonical equations with the given truncation maps.
   `cohomology j` is the natural isomorphism
   H^j(-) followed by pullback ≅ pullback followed by H^j(-).
   `cohomology_formula` fixes its components as the composite of these two
   truncation comparisons and the shift comparison, not a free isomorphism.
   `constructibleTruncationCohomology` is used unchanged from its owning node:
   τ≤j, then τ≥j, then shift j. All K and all integers j are quantified.
4. `constructible_pullback_scalar_compatibility` supplies the finite-stage
   families and their common-stage comparison. Its first clause is the
   cohomology square against the ACTUAL `rationalPullbackScalarComparison`
   for every E ≤ L. Its second clause compares finite-stage maps with the
   common-stage maps. The inclusion beta's component is fixed by the object
   equality in `commonStageDerivedPullback_existsUnique`; it is not arbitrary.
   `ConstructiblePullbackScalarSquare` spells out equality of the two routes
   T(F(H^j K)) → H^j(G(S K)). This is the finite-stage scalar-extension clause.
5. `constructible_pullback_point_fibre` states the point formula for both
   rational and common-stage coefficients. The realization functors are
   literally the recorded `pointRationalFibre` / `pointQbarFibre`, followed by
   their existing inclusions into D(E) / D(Ω). At Ω this realization is fully
   faithful; no information about isomorphisms is lost. The natural iso γ
   compares Fib(x*(H^j K)) and H^j(Fib(x*K)). Each γ component is specified as
   the fibre of the pullback cohomology comparison followed by the exact
   point-evaluation comparison. On D(E) and D(Ω), H^j is for Mathlib's usual
   standard t-structure: the ordinary cohomology module in degree zero.
6. The final clause of each point package quantifies every constructible heart
   object F and every j ≠ 0 and says its actual `DerivedCategory.homologyFunctor`
   vanishes on Fib(x*F). Thus the concentration assertion is not replaced by a
   condition merely on an arbitrary ambient object or a chosen representative.
7. `constructible_point_scalar_compatibility` states the scalar clause for
   point evaluation too. Its finite beta is `constructiblePointFiniteScalarBeta`,
   composed from the given `pointRationalFibreScalarIso`, the full-subcategory
   lift comparison and the recorded stage-transition identification. Its
   common-stage beta has every component fixed by the canonical field tensor
   tower and the object equality of `pointQbarFibre_existsUnique`.
   The scalar squares fix cohomology compatibility with these maps; the field
   extension shift is required to be the given exact-functor shift. Combining
   these fibre squares with the pullback squares gives the scalar compatibility
   of the displayed point formula. All finite E ≤ L, including E = L, occur.

The owning helper `ConstructiblePullbackComparison` is only a clause package:
it does not redefine a category, t-structure, heart, pullback, scalar extension,
cohomology or fibre functor. The two realized fibre abbreviations are composites
of the recorded functors. The map helpers are explicit composites of existing canonical maps:
`constructiblePointFiniteScalarBeta`, the typed coefficient-model map, the
recorded common-stage fibre object isomorphism, and its scalar-tower composite.
They use no choice of new maps and no postponed data. The complete eleven-step node proof is included in the main
theorem's docstring; the other three proof docstrings identify their steps and
canonical maps. All stated proof dependencies with modules are imported as
non-public proof-plan imports; the two still-unstated proof dependencies have
no module to import (integral/completed comparison and pullback composition).

Dependency declarations read and used:

- `def-weil-finite-field-fiber`: Sheaf.Paper.FiniteFieldFiber — `WeilConjectures.FiniteFieldDatum`.
- `def-weil-algebraically-closed-coefficients`: Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients — `WeilConjectures.generalAlgebraicallyClosedConstructibleCategory`.
- `def-weil-scheme-morphism-properties`: None — `None`.
- `def-weil-derived-pullback-tensor-hom`: Sheaf.Paper.DerivedPullbackTensorHom — `WeilConjectures.commonStageDerivedInternalHom_existsUnique`.
- `def-weil-constructible-standard-tstructure`: Sheaf.Paper.SfConstructibleHeart — `WeilConjectures.sfIntegralStandardClass`.
- `def-weil-constructible-heart`: Sheaf.Paper.SfConstructibleHeart — `WeilConjectures.sfRationalHeart`.
- `prop-constructible-truncations`: Sheaf.Paper.ConstructibleTruncations — `WeilConjectures.constructibleTruncations_exists`.
- `def-weil-geometric-point`: Mathlib.FieldTheory.IsAlgClosed.Basic — `IsAlgClosed`.
- `def-weil-finite-coefficient-point`: Sheaf.Paper.FiniteCoefficientPoint — `WeilConjectures.pointQbarFibre`.

For the derived-operations node the relevant recorded declarations are
`constructibleIntegralPullback`, `rationalDerivedPullback`,
`rationalPullbackScalarComparison`, `operationStageTransitionIso`,
`commonStageDerivedPullback`, and its defining object specification.
For the heart and standard-pair nodes the relevant declarations are
`sfRationalStandardClass`, `sfCommonStageStandardClass`, their heart predicates,
and their uniquely characterized standard t-structures.
For the fibre node they are `pointRationalFibre`, `pointQbarFibre`,
`pointRationalFibreScalarIso`, `pointQbarFibre_existsUnique`, and their existing
fully faithful full-subcategory/common-stage realizations.
`def-weil-scheme-morphism-properties` is explicitly a convention record with no
own declaration: its finite-type convention is the Mathlib classes just used.
The geometric-point node is likewise used inline as the specified scheme map.

Edge cases checked against the statements and source:

- Empty X or W; no point or nonemptiness hypothesis occurs in the pullback
  statements. Empty base-changed strata cause no condition in the proof plan.
- Zero complexes and heart objects, including an integral torsion module that
  becomes zero after rationalization. The standard rational class is its
  isomorphism closure; no bound is inferred from an arbitrary integral model.
- Every positive, negative and zero j; the point vanishing statement is exactly
  j ≠ 0, while the comparison itself includes j = 0.
- Non-surjective and non-flat h, and a geometric point twisted by a field
  automorphism. There is no hidden k-linearity or relative-dimension assumption.
- l = 2 when different from p, identity scalar inclusions, repeated extensions,
  and arbitrary later common stages. The quantified scalar comparisons include
  these cases and use the same canonical tensor and section maps.
- The scheme site still has object universe u+1 and morphism universe u;
  no equality between those universes has been imposed. The general pullback
  and its scalar-compatibility assertion allow independent closure universe v.

Searches:

- `msearch.py leanfinder`, query "Derived pullback of constructible l-adic
  complexes is t-exact and commutes with cohomology and geometric point fibres":
  eight general sheaf pullback/composition hits; none states the node.
- `msearch.py loogle`, query "Functor.IsTExact, DerivedCategory.homologyFunctor":
  no hits; service reported unknown identifier Functor.IsTExact. The upstream
  SpectralObject file was read directly for its actual definition, which is
  used as the package field `tExact` (no duplicate t-exactness predicate).
- `msearch.py grep`, query "IsTExact|mapDerivedCategoryHomologyFunctorIso|adic.*[Pp]ullback"
  in Mathlib CategoryTheory: two unrelated preradical colon hits.
- `msearch.py leansearch`, query "Pullback of constructible l-adic complexes
  preserves the standard t-structure": general sheaf inverse image and the
  ordinary derived-category standard t-structure; no completed rational or
  common-stage constructible result, point formula, or scalar package.
- `rg` of t-exact/constructible-pullback names and the item id in the upstream
  `WeilConjectures` and published `lean/Sheaf` found only unrelated short-exact
  sheaf statements. The upstream `Functor.IsTExact` definition is generic
  infrastructure, reused by the statement, not the concrete completed
  coefficient assertion here.
- Source checked directly: local Bhatt--Scholze PDF, Definition 6.8.10,
  Proposition 6.8.11(3), Proposition 6.8.14 and Remark 6.8.15; current blueprint
  `sec-deligne-laumon-a1/sk-thm-dl-a1-upper/lem-a1-finite-map-purity.proof.md`;
  recorded dependency signatures and docstrings, the compact-object example,
  and Mathlib standard t-structure/full-subcategory/shift/scalar definitions.

No STATEMENT-DISPUTED flag or node fault was found.

Validation: the full module compiled with no errors or warnings through
`scompile.py`, in both sandbox and library-path modes under the unchanged
60-second per-file limit. Both delivery dry runs passed server preflight
and compilation; the final interface check was commit c5f13309e4. That version
reuses the existing `Functor.IsTExact` class and makes the direct
statement-dependency imports public. The delivery wrapper repeats these checks
for the push, including the completed module-docstring statement index.

## Second reading by NL

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
