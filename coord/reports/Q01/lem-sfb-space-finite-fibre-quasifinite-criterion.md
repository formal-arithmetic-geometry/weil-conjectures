## Worker report

The module `Sheaf.AlgebraicGeometry.SpaceFiniteFibreQuasifiniteCriterion` states
`AlgebraicGeometry.AlgebraicSpace.finite_field_fibre_iff_quasiFinite_at_fibre`.
Its sole proof is `sorry`, as required for stage 2. No definitions, helper theorems,
new nodes, dependency repairs or statement corrections are introduced.

The source was read in `literature/stacks-project/decent-spaces.tex`,
`lemma-conditions-on-fibre-and-qf` (0ACK), particularly (4), (5), (8), and
`lemma-conditions-on-space-over-field` (0ACA). Also read the quasi-compactness
definition, its underlying-topological-map consequence, and base change (03HF)
in `spaces-morphisms.tex`. The current blueprint direct-images proof (3) was
read under `literature/blueprint/latest/`; this is a supporting lemma, not a unit
statement. The declaration docstring carries all four steps of the DAG proof.

Hypotheses and clauses, matched individually:

* Schemes and the size convention: `{S : Scheme.{u}}`, explicit `universe u`,
  and `K : Type u` use the same scheme/field universe as the existing algebraic
  space and point-class APIs. Point classes themselves live in `Type (u + 1)`.
* An algebraic space over S: `E : AlgebraicSpace S`, the recorded full subcategory
  of fppf sheaves with representable diagonal and a surjective etale scheme atlas.
* Its map h to S: `h : E.obj.obj ⟶ yoneda.obj (Over.mk (𝟙 S))`. The target is
  the Yoneda presheaf of S as an S-scheme. This retains the structural morphism;
  since this target is terminal, it supplies no additional choice of structure.
* Separatedness: `hsep : MapToSchemeIsSeparated E (Over.mk (𝟙 S)) h` unfolds
  to `IsRepresentableWith (fun _ _ p ↦ IsClosedImmersion p.left)
  (pullback.diagonal h)`, exactly the closed-immersion scheme tests of the diagonal.
* Quasi-compactness: `hqc` quantifies over `V : S.Opens`, assumes
  `IsCompact (V : Set S)`, and asserts compactness of its inverse image in
  `Point E.obj.obj`. `schemePointMap (𝟙 (yoneda.obj (Over.mk (𝟙 S))))` is the
  canonical identification of scheme points with Yoneda point classes, and
  `mapPoint h` is the existing induced map on point classes. This is literally
  the stated inverse-image-of-quasi-compact-opens condition. No Hausdorff
  hypothesis is implicit in `IsCompact`.
* Local finite type: `hft : MapToSchemeIsLocally (@LocallyOfFiniteType)
  E (Over.mk (𝟙 S)) h` tests every representable etale scheme chart by the
  recorded Mathlib scheme property. Together with `hqc` this is finite type.
* The chosen point: `s : S` is arbitrary.
* Any extension of its residue field: `(K : Type u) [Field K]
  [Algebra (S.residueField s) K]`. Both rings are fields, so the algebra map is
  an embedding; no finiteness, algebraicity or algebraic closure is assumed.
* E_K: the explicit `Limits.pullback` of h with the Yoneda map induced by
  `Spec.map (CommRingCat.ofHom (algebraMap (S.residueField s) K)) ≫
  S.fromSpecResidueField s`. `Over.mkIdTerminal.from` is the canonical arrow
  to S in `Over S`. Presheaf fibre products compute underlying sheaf fibre
  products, so this is the actual E times_S Spec K, without a chosen atlas.
* Clause (i): `Finite (Point (Limits.pullback ...))` is finiteness of its
  existing field-valued point classes, with their recorded atlas topology.
* The equivalence is `↔`.
* Clause (ii): for every `U : Over S` and `a : yoneda.obj U ⟶ E.obj.obj`,
  `IsEtale a` means representable etale. For each `x : U.left` whose composite
  scheme map satisfies `(yoneda.preimage (a ≫ h)).left x = s`, that composite
  satisfies `.IsQuasiFiniteAtPoint x`. This is exactly the node's chartwise
  definition at every point of E over s: a chart point gives such a point of E,
  and every point of E has chart representatives. Quantifying all chart points
  over s combines the node's quantifiers over space points and their chart lifts.
* Every representative field: the theorem is universally quantified in K and
  its extension structure, while its right side contains no K. Thus it yields
  the equivalence for every K, including the identity extension and any
  algebraic closure, and equates finiteness for any two such extensions.
* Empty fibres: no `Nonempty` binder is present; `Finite` includes the empty
  type, and the right side has no chart point mapping to s in this case.

Dependency declarations used, with their source modules read:

* `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`,
  `IsRepresentableWith`, `IsEtale`, `IsSurjective`, `IsAlgebraicSpace`.
* `Mathlib.AlgebraicGeometry.Scheme`: `Scheme` and `Scheme.Hom`.
* `Sheaf.AlgebraicGeometry.AlgebraicSpacePointClasses`: `Point`,
  `PointRepresentative`, its common-field-extension relation, `schemePointMap`.
* `Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology`:
  `pointTopologicalSpace`, the final topology for etale scheme-source maps.
* `Sheaf.AlgebraicGeometry.ProperCurveModuli`: `mapPoint`,
  `MapToSchemeIsLocally`, `MapToSchemeIsSeparated`. The already landed node
  `def-sfb-proper-curve-moduli` is added to `stmt_deps` solely to cite these
  existing general helper definitions; no proper-curve hypothesis is used.
* `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`;
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`: the scheme convention was
  read for comparison, but `hqc` is stated directly for the space point map.
* `WeilConjectures.AlgebraicGeometry.QuasiFiniteMorphism`:
  `Scheme.Hom.IsQuasiFiniteAtPoint` (with its affine-neighbourhood finite-type
  condition), rather than Mathlib's predicate omitting that condition.
* `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`.
* `Mathlib.Algebra.Field.Defs`: `Field`.
* `Mathlib.AlgebraicGeometry.ResidueField`: `Scheme.residueField` and
  `Scheme.fromSpecResidueField`; `CategoryTheory.Over.mkIdTerminal.from` supplies
  the canonical structural arrow to S.
* `Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers`:
  `fibreProduct_isAlgebraicSpace`, `etaleCover_pullback`,
  `etale_fibreProduct_isScheme`; its module is publicly imported.
* Stated proof inputs are imported privately:
  `Sheaf.AlgebraicGeometry.AlgebraicSpacePointOpenCalculus` (`point_open_calculus`)
  and `Sheaf.AlgebraicGeometry.SpaceFieldDiscretenessCriterion`
  (`space_field_discreteness_criterion`). The other three proof dependencies
  (`lem-sfb-stack-finite-type-calculus`, `lem-sfb-space-separated-fp-composition`,
  `lem-sfb-space-quasifinite-locus-open`) currently have no Lean records and hence
  no modules to import; no new statement notion is required from them here.

Edge cases checked before writing: empty E and empty fibre; identity and arbitrary
transcendental residue-field extensions; algebraic closures; finite nonreduced
field fibres such as Spec K[epsilon]; positive-dimensional affine-line fibres
(both sides false); non-quasi-compact S (only its quasi-compact opens occur in
`hqc`). An infinite disjoint union of field points explains the role of `hqc`:
its map to a point fails that hypothesis. No integrality, reducedness, properness,
Noetherianity or surjectivity hypothesis is imposed.

Searches for an existing exact statement:

* `msearch.py ... leanfinder`: "A separated finite type algebraic space has finite
  field fibre if and only if it is quasi-finite at every point of that fibre".
  Eight hits, all ring-level or scheme-level finiteness/quasi-finiteness; no
  algebraic-space assertion with this fibrewise equivalence.
* `msearch.py ... loogle`: `AlgebraicGeometry.LocallyQuasiFinite, Finite`.
  Zero hits.
* `msearch.py ... grep`: `finite.*fiber|finite.*fibre|QuasiFiniteAt` in
  `AlgebraicGeometry`. Eighteen hits in Mathlib, including scheme quasi-finite
  fibres and Zariski's main theorem; no space criterion.
* `rg` in `lean/WeilConjectures/AlgebraicGeometry` found the scheme-only
  `Morphisms/ProperQuasiFinite.lean` and other scheme fibre statements.
  Searching the item id in `lean/WeilConjectures` returned no match.
* `rg` in `lean/Sheaf` found the field-discreteness criterion, chart/property
  definitions and point-map helper. The field-discreteness theorem does not state
  the relative fibre equivalence; those helpers are reused without duplication.
  The proposed full theorem name and module name have no existing declarations.

No statement dispute or node fault was found. The first compiler attempt exposed
namespace shadowing by the existing algebraic-space sheaf pullback; the fibre
product is now qualified as `Limits.pullback`.

## Validation

Every compile uses the prescribed `scompile.py`, with one module at a time and
the default 60-second server limit. No diagnostic commands remain in the module.
The final signature is copied verbatim into the node's `lean.statement`.
Delivery is validated by `deliver2.py --no-push` before the normal push.

## Second reading by Q01

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
