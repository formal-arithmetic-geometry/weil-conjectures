## Worker report

The module `Sheaf.AlgebraicGeometry.AlgebraicSpaceUniversalSurjectiveFlatOpen` states
`AlgebraicGeometry.AlgebraicSpace.exists_openSubspace_universal_surjective_flat`.
Its sole postponed theorem has proof `sorry`; the full seven-step DAG proof is in its
docstring. `baseChangeDiagramMap` is a helper belonging to this statement: it constructs
the canonical sheaf-pullback map using `Limits.pullback.map`. Its objects are bundled as
algebraic spaces with `fibreProduct_isAlgebraicSpace`. This chooses no unknown data and
adds no theorem obligation or stronger hypothesis. Both declarations are recorded.
Only the item's `lean` field changes. There are no new nodes or dependency repairs.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- The scheme S and the size convention: `{S : Scheme.{u}}`, with explicit universe u.
  The algebraic spaces and all test spaces use the dependency's category in that universe.
- The algebraic spaces A, C, B over S: `(A C B : AlgebraicSpace S)`.
- The three morphisms: `(p : A ⟶ B) (q : C ⟶ B) (f : A ⟶ C)`.
- Commutativity q composed with f equals p: `(w : f ≫ q = p)`.
- p flat: `hp_flat : MapIsFlat p`, the recorded chartwise definition.
- p locally of finite presentation: `hp_lfp : MapIsLocallyOfFinitePresentation p`.
- p closed: `hp_closed : IsClosedMap (mapPoint p.hom.hom)`.
- q locally of finite type: `hq_lft : MapIsLocally (@LocallyOfFiniteType) q`.
  This directly uses the recorded generic chart test with Mathlib's scheme property.
- q closed: `hq_closed : IsClosedMap (mapPoint q.hom.hom)`.
  Neither closedness hypothesis is strengthened to universal closedness.
- The existential open subspace of B: `∃ V : OpenSubspace B`.
- Every algebraic-space parameter and map: `∀ (T : AlgebraicSpace S) (h : T ⟶ B)`;
  no scheme, representability, reducedness or nonemptiness restriction is added.
- The map f_T is `baseChangeDiagramMap p q f w h`. Its source and target are literally
  the sheaf fibre products of p,h and q,h. `Limits.pullback.map` uses f on the first
  factor and identities on T and B; its two commutativity witnesses follow from w
  and the identity laws. There is no arbitrary map supplied in place of base change.
- Flatness of f_T: `MapIsFlat (baseChangeDiagramMap p q f w h)`.
- Surjectivity on the specified field-valued point classes:
  `Function.Surjective (mapPoint (baseChangeDiagramMap p q f w h).hom.hom)`.
  The representable-only `IsSurjective` predicate is deliberately not imposed on f_T.
- The conjunction of these properties is equivalent (`↔`) to factorization of h:
  `∃ l : T.obj.obj ⟶ V.val.toFunctor, l ≫ V.val.ι = h.hom.hom`.
  This is a natural transformation to the open subfunctor, with exactly the required
  equality after its inclusion. No choice of an algebraic-space structure on that
  subfunctor is needed to express factorization, as in the recorded open-factor theorem.
- Separatedness and universal closedness occur in the introductory list of property
  conventions, but the source's five assumptions do not require either for q or p.

Dependencies read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`, the
  full subcategory of fppf sheaves with representable diagonal and an etale atlas.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties`: `MapIsFlat`,
  `MapIsLocallyOfFinitePresentation`, `MapIsLocally` (all in AlgebraicSpace namespace).
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceOpenSubspace`: `OpenSubspace`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers`:
  `fibreProduct_isAlgebraicSpace` (closure of the actual sheaf fibre product).
- `Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology`: `pointTopologicalSpace`;
  `mapPoint` is defined in the transitively imported `ProperCurveModuli` module.
- `def-weil-size-convention` is recorded as metatheoretic: it has no declaration to import.

The stated proof dependencies are imported non-publicly: `SpaceInvariantOpenQuotient`
(`space_invariant_open_quotient`), `AlgebraicSpaceOpenFactorSchemeTests`
(`openSubspace_factor_schemeTests`), `AlgebraicSpacePointOpenCalculus`
(`point_open_calculus`), `AlgebraicSpaceFlatLfpUniversallyOpen`
(`universallyOpen_of_flat_of_locallyOfFinitePresentation`), and
`StackChartwiseSmoothEtaleCalculus` (`CategoryTheory.stack_chartwise_smooth_etale_calculus`).
The proof-dependency nodes `lem-sfb-space-relative-flat-locus-base-change` and
`lem-sfb-space-relative-lfp-permanence` have no recorded Lean module, so there is no module
to import for them. They are not needed to type this statement and are left unchanged.

Source and edge cases:

Read `literature/stacks-project/spaces-more-morphisms.tex`,
`lemma-where-surjective-flat` (Tag 05XC), including its five numbered assumptions and
proof. Its statement agrees with the node, including ordinary closedness and arbitrary
algebraic-space tests. No statement fault or STATEMENT-DISPUTED issue was found.
For empty T, both base changes are empty, flatness and surjectivity hold and the empty
map factors through every open; no excluded edge case. If A is empty, the condition is
exactly that the corresponding C-fibre be empty, as the complement of the closed q-image
predicts. If B is empty all objects over it are empty. If f is the identity with A=C
and p=q, every base change is flat and surjective and V=B works. Nonreduced tests remain
allowed; all morphisms and factorization are sheaf maps rather than point maps alone.

Searches made with the prescribed `msearch.py Q67 <item>` wrapper:

- leanfinder: `An open subspace represents base changes where a morphism of algebraic
  spaces is flat and surjective` — 8 hits, headed by `UniversallyOpen.of_flat`, all
  scheme openness or base-change stability; no matching algebraic-space locus theorem.
- loogle: `"AlgebraicGeometry", "Flat", "Surjective"` — 12 hits, scheme faithful
  flatness and descent statements; no match.
- grep: `whereSurjectiveFlat|where_surjective_flat|AlgebraicSpace`, subdirectory
  `AlgebraicGeometry` — 0 hits in Mathlib.
- leansearch: `The base changes where a map of algebraic spaces is flat and surjective
  are represented by an open subspace` — 8 hits, ring/module/scheme flat base-change
  stability and scheme openness; no matching statement.
- Local rg in `lean/WeilConjectures` for the item ID — no hit. Local rg in that tree,
  `lean/Sheaf`, and Mathlib AlgebraicGeometry for the statement and proposed declaration
  names found the scheme-only `UniversalSurjectiveFlatOpen` and the downstream
  `AlgebraicSpaceUniversalIsomorphismOpen`, but no existing algebraic-space theorem
  or canonical bundled helper. Read both modules: the former quantifies only over
  schemes, so cannot realize this node; the latter merely cites this unrecorded input.
- Checked `dag/lean_names_upstream.json` for the two new declaration names: no hit.

Validation uses only scompile.py, then deliver2.py --no-push, followed by deliver2.py.
The initial compile found bare `pullback` resolving to the algebraic-space etale module
pullback instead of categorical fibre products. Both object expressions and the helper's
map now explicitly use `Limits.pullback`. No mathematical change was required.

## Second reading by Q67

The dispatcher prohibits spawning another agent and assigns independent review to the
maintainer; this section records a second pass by the same worker, not a claimed
independent review. Reopened the node, source lemma and completed module together.
Checked the three spaces, three maps and commuting equation; all five assumptions
match individually as listed above. In particular both closedness hypotheses are ordinary
closedness and q is locally of finite type, not finite type. The conclusion has one open
subfunctor and quantifies over every algebraic space T. Its two properties concern the
actual canonical sheaf base change; point-surjectivity is not confused with representable
surjectivity. Factorization is an actual natural transformation with the inclusion
equation, not just image containment. The helper uses the recorded closure theorem for
both pullback objects, with no new axioms or existential choices. Explicit `universe u`
and `set_option autoImplicit false` rule out unintended auto-bound variables. The sole
postponed theorem has the node's seven-step proof. No remaining mismatch was found.

## Review fix

Maintainer review (2026-10-24): `mapPoint` is declared in `ProperCurveModuli` and owned by
def-sfb-proper-curve-moduli, which is not a statement dependency of this item. The two
closedness hypotheses now say that the image on point classes (computed on field-valued
representatives with `PointRepresentative.map`) of every closed subset is closed, and
surjectivity of f_T is `pointImage … = Set.univ`, all from def-a1-space-point-topology.
These are equivalent to the delivered `IsClosedMap (mapPoint …)` and
`Function.Surjective (mapPoint …)`. The statement field was updated verbatim; nothing else
changed. The fixed module compiles clean through nt_compile.py.
