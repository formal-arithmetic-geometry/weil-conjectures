## Worker report

Q138, stage 2, 2026-10-24. The module
`Sheaf.AlgebraicGeometry.ReducedClosedSubspaceSupport` states
`AlgebraicGeometry.AlgebraicSpace.exists_unique_reduced_closed_subspace`.
Its only proof is `sorry`; no definitions or proved helpers are introduced.

Sources read directly: `literature/stacks-project/spaces-properties.tex`,
Tag 03IQ, `lemma-reduced-closed-subspace`, lines 1466–1499; Tag 03H4,
`lemma-points-cartesian`, lines 280–309; Tag 0ABJ,
`lemma-subspace-induced-topology`, lines 1388–1410; and
`literature/stacks-project/spaces.tex`, Tag 02YW,
`lemma-base-change-immersions`, lines 1975–1987.
03IQ gives the unique reduced structure, 02YW gives closedness under arbitrary
base change, 03H4 gives the inverse-image support, and 0ABJ gives the induced topology.
The theorem docstring carries all eight accepted proof steps, including the
atlas construction, invariant descent, omitted uniqueness, and the closed-map argument.

Clause-by-clause correspondence:

| Node hypothesis or clause | Lean rendering |
| --- | --- |
| Scheme base S in the size convention | Explicit `universe u`, `{S : Scheme.{u}}`; no other universe restrictions |
| Algebraic space X over S | `(X : AlgebraicSpace S)`, the recorded full subcategory of fppf sheaves |
| Closed subset of its atlas point space | `(T : Set (Point X.obj.obj)) (hT : IsClosed T)` using `pointTopologicalSpace` |
| Existence of a closed subspace | `∃ C : ClosedSubspace X`; the subtype property is exactly representability by closed scheme immersions |
| Inclusion i of the subfunctor | `C.val.arrow.hom.hom`; subobjects identify isomorphic presentations over X |
| Z reduced, meaning all etale charts reduced | `IsReduced (C.val : AlgebraicSpace S)`, the existing chartwise predicate |
| Underlying support equals T | `pointImage C.val.arrow.hom.hom = T` |
| Uniqueness of reduced closed structure with that support | `∀ D : ClosedSubspace X, IsReduced (D.val : AlgebraicSpace S) → pointImage D.val.arrow.hom.hom = T → D = C` |
| Every arbitrary algebraic-space morphism q | `∀ (W : AlgebraicSpace S) (q : W ⟶ X)`; no flatness, etaleness, finite-type or reducedness hypotheses |
| Actual sheaf fibre product Z times_X W | `Limits.pullback C.val.arrow.hom q.hom` in the sheaf category; the recorded fibre-product theorem makes this an algebraic space |
| Projection is a representable closed immersion | `IsRepresentableWith (fun _ _ p ↦ IsClosedImmersion p.left) (Limits.pullback.snd C.val.arrow.hom q.hom).hom` |
| Homeomorphism onto the inverse-image subset | `∃ e : Point (Limits.pullback C.val.arrow.hom q.hom).obj ≃ₜ {w : Point W.obj.obj | mapPoint q.hom.hom w ∈ T}, ...`; the subtype has its subspace topology |
| This is the projection's own point map | `∀ z, (e z).val = mapPoint (Limits.pullback.snd C.val.arrow.hom q.hom).hom z`; thus the homeomorphism cannot be unrelated to the canonical projection |
| No reducedness of base change asserted | The reducedness conjunct concerns only C; neither W nor the sheaf pullback is required to be reduced |

Recorded statement-dependency declarations used:

- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`,
  `AlgebraicSpace.IsRepresentableWith`, `AlgebraicSpace.EtaleSite`,
  and `AlgebraicSpace.etaleForget`.
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`.
- `def-weil-size-convention` is a metatheoretic convention with no Lean object;
  the explicit universe binder renders it.
- `Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology`:
  `AlgebraicSpace.pointTopologicalSpace`, `AlgebraicSpace.pointImage`;
  its existing dependency `AlgebraicSpacePointClasses` supplies `Point`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers`:
  `AlgebraicSpace.fibreProduct_isAlgebraicSpace` (sheaf pullback closure).
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`:
  `AlgebraicGeometry.IsClosedImmersion` on each representing scheme projection.
- Added the already landed node `def-sfb-space-closed-subspace`:
  `Sheaf.AlgebraicGeometry.AlgebraicSpaceClosedSubspace`,
  `AlgebraicSpace.ClosedSubspace`. This avoids a new private subfunctor definition.
- Added the already landed node `def-sfb-reduced-algebraic-space`:
  `Sheaf.AlgebraicGeometry.ReducedAlgebraicSpace`, `AlgebraicSpace.IsReduced`.
  Its definition quantifies over all small-etale-site objects and uses the existing
  scheme predicate, equivalent to reduced local rings.
- Added the already landed node `def-sfb-proper-curve-moduli` only as the owner of
  the existing canonical `AlgebraicSpace.mapPoint`, defined in
  `Sheaf.AlgebraicGeometry.ProperCurveModuli`. No curve structure or hypothesis
  enters this statement. Its `Quot.map` construction was read in full.

The three added statement dependencies are existing landed nodes, permitted by
brief-stage2 section 5. They merely name existing notions used in the statement;
no natural-language statement or proof field changes. A read-only transitive
traversal confirmed that none depends on this item. No new nodes, dependency
repairs, or statement corrections are needed.

All recorded proof-dependency modules are imported privately where stated.
`lem-a1-space-point-open-calculus` has no recorded Lean module, so its future
proof import is omitted; its eight-step uses remain in the docstring.
No proof dependency was replaced by an axiom or a new assumption.

Edge cases checked mathematically before writing:

- T empty: the empty closed subspace is reduced; every pullback point space and
  inverse-image subtype are empty, so the homeomorphism clause includes this case.
- T all of X: C is the reduction, including when X has nilpotents; the statement
  does not force C to be X as a scheme or space with structure sheaf.
- Empty X or empty W: all point conditions have their expected empty meanings;
  neither a nonempty atlas nor a point is added as a hypothesis.
- q the identity: the pullback identifies the reduced closed support with T.
- Non-reduced base change: take X = Spec k[t], T = V(t),
  W = Spec k[u], q induced by t mapping to u squared. Then Z = Spec k, but
  Z times_X W = Spec k[u]/(u squared) is non-reduced. The theorem still asserts
  exactly the correct closed immersion and one-point inverse-image support.
- Non-flat q: the closed immersion Spec k -> Spec k[t] at t = 0 is permitted;
  its pullback of Z = Spec k is Spec k, with exactly the predicted support.
- Non-Noetherian X, arbitrary characteristic, and non-separated spaces are not
  excluded by any binder. The proof route uses reducedness etale locality without
  a Noetherian assumption.
- Uniqueness compares all reduced closed subspaces with the same support, before
  imposing any base-change conclusion; it is not uniqueness only among objects
  already satisfying the theorem's desired conclusion.

Searches actually run with the prescribed msearch wrapper:

- LeanFinder: `Every closed subset of an algebraic space has a unique reduced closed subspace and its arbitrary base changes have inverse image support`.
  Eight hits, all scheme/topology facts: `Scheme.IdealSheafData.support`,
  scheme `IsReduced`, `IsClosedImmersion.instSubschemeι`, and related facts.
  None states the algebraic-space result.
- Loogle: `AlgebraicGeometry.AlgebraicSpace, IsReduced, IsClosedImmersion`.
  Zero hits; the service reports unknown identifier
  `AlgebraicGeometry.AlgebraicSpace` (a project definition, absent from its index).
- Mathlib grep, AlgebraicGeometry: `reduced.*[Cc]losed|[Cc]losed[Ss]ubspace|[Aa]lgebraic[Ss]pace`.
  Three hits, in `IdealSheaf/IrreducibleComponent`, `Group/Smooth`, and
  `IdealSheaf/Basic`; none is the algebraic-space statement.
- LeanSearch: `unique reduced closed subspace of an algebraic space supported on a closed subset`.
  Eight hits, including scheme vanishing ideals, reduced schemes and closed
  subscheme construction; none is the target.
- `rg` on `lean/WeilConjectures`, `lean/Sheaf`, and `dag/lean_names_upstream.json`
  for reduced/closed-subspace phrases, the item id, `reduced_closed_support`,
  `ReducedClosed`, `reducedClosed`, and `exists_reduced_closed_subspace`.
  Existing scheme results and uses in proof docstrings were found, but no target
  declaration. Searches in `lean/Sheaf/AlgebraicGeometry/AlgebraicSpace*.lean`
  found the existing ClosedSubspace and point APIs; a focused reduced-space search
  found `ReducedAlgebraicSpace.IsReduced`, so it was reused rather than copied.

No statement dispute or node fault was found. The source and target statements
agree. No repair note for this item was present.

Validation: `scompile.py Q138 lem-sfb-space-reduced-closed-support` on the sole
module completed both sandbox and library compiles with no errors or warnings
(14.1 s and 12.4 s respectively). Every line is at most 100 characters,
`autoImplicit` is disabled, and the JSON signature is verbatim from the file.

## Second reading by Q138

This is the worker's own second pass; the maintainer supplies the independent
review requested by the dispatch brief. I reread the source, node, and complete
Lean module. S is explicitly a scheme, X is precisely the recorded algebraic
space over it, and hT is the sole topological hypothesis. ClosedSubspace carries
representability by closed scheme immersions, rather than merely a point subset.
The existing IsReduced quantifies over all etale scheme charts. pointImage
expresses equality of the image of the inclusion with T. The D quantifier ranges
over all closed subobjects, assumes exactly reducedness and that image equality,
and concludes equality in ClosedSubspace; it therefore includes the full
scheme-theoretic uniqueness of 03IQ.

For each W and q the fibre product uses the sheaf morphisms underlying C's
inclusion and q. The second projection is the one to W. Its scheme-test predicate
is closed immersion, with no extraneous representability or flatness hypothesis.
The homeomorphism has precisely the preimage subtype as target. The last equality
pins its underlying function to that second projection's canonical point map,
so mere existence of an unrelated abstract homeomorphism cannot satisfy the clause.
Reducedness is not imposed on this pullback, as confirmed by t mapping to u squared.

No mismatch was found and no statement correction was made. The only DAG field
changes are lean and the three already-landed statement-dependency additions.
No new nodes or dependency modules are included; no claim of independent
self-review is made.
