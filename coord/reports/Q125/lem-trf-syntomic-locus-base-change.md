## Worker report

The delivery states Stacks Tag 02V3 in
`Sheaf.TraceFormula.SyntomicLocusBaseChange`. The only postponed theorem is
`AlgebraicGeometry.syntomic_locus_base_change`, with proof `sorry`. Its docstring
contains the node's five proof steps. The three additional declarations are
definitions of the very locus and fibre conditions introduced in this node;
their data contain no `sorry`.

Hypothesis and clause correspondence:

- Schemes `X, S` and the morphism `f : X ⟶ S` are the explicit binders, in an
  arbitrary universe `u`. Local finite type is `[LocallyOfFiniteType f]`.
- The fibre over `s` is Mathlib's `f.fiber s`, with structure morphism
  `f.fiberToSpecResidueField s`. The coefficient field is `S.residueField s`.
- The local-ring condition is `f.IsCompleteIntersectionAtFiberPoint s y`.
  It applies the existing `Algebra.IsCompleteIntersectionLocalAlgebra` to
  `(f.fiber s).presheaf.stalk y`, with its actual residue-field algebra
  structure induced by `ΓSpecIso`, the structure morphism's map on sections,
  and the germ at `y`. It requires locality, essential finite type, a regular
  local presenting algebra essentially of finite type, a finite regular
  sequence in its maximal ideal, and an isomorphism of algebras to its quotient.
  These are exactly the local-ring meaning of the pointwise-criterion node;
  no completed local ring or geometric fibre is substituted.
- The specified set `V_f` is `f.fiberCompleteIntersectionLocus`: at a source
  point `x` its condition is evaluated at the canonical `f.asFiber x` over
  `f x`. Mathlib constructs this point by the fibre homeomorphism, so no
  lift is an arbitrary parameter or an additional hypothesis.
- Every base morphism is quantified as `(S' : Scheme.{u}) (g : S' ⟶ S)`.
  `f'` and `g'` are `pullback.snd f g` and `pullback.fst f g` respectively.
  The first conjunct is precisely `V_f' = g' ⁻¹' V_f`. Flatness and finite
  presentation are absent from this conjunct.
- The second conjunct is conditional on `Flat f` and
  `LocallyOfFinitePresentation f`. It supplies `U : X.Opens` whose underlying
  set equals `V_f`, explicitly expressing that this set is open.
- `IsGreatest {V : X.Opens | ...} U` includes both membership of `U` in the
  indicated class and containment of every other member in `U`. Its three
  conditions are `Flat (V.ι ≫ f)`, `LocallyOfFinitePresentation (V.ι ≫ f)`,
  and `(V.ι ≫ f).HasCompleteIntersectionFibres`.
- The last predicate quantifies every base point `s` and every point `y` of
  the actual scheme-theoretic fibre, and tests exactly the local-algebra
  condition above. This renders the node's explicit meaning of
  local-complete-intersection fibres and its largest-source-open assertion.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and
  `Scheme.Hom` (locally ringed spaces locally affine, and their morphisms).
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`:
  `AlgebraicGeometry.LocallyOfFiniteType` (the affine-local finite-type condition).
- `Mathlib.AlgebraicGeometry.Fiber`: `Scheme.Hom.fiber`, `fiberι`,
  `fiberToSpecResidueField`, `fiberHomeo`, and `asFiber`.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`:
  `CategoryTheory.Limits.pullback`, `pullback.fst`, and `pullback.snd`.
- `Mathlib.AlgebraicGeometry.Morphisms.Flat`: `AlgebraicGeometry.Flat`,
  with its equivalent stalkwise condition `Flat.iff_flat_stalkMap`.
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`:
  `AlgebraicGeometry.LocallyOfFinitePresentation`.
- `Sheaf.TraceFormula.LciPointwiseCriterion`:
  `AlgebraicGeometry.lci_pointwise_criterion`, with its full local-ring
  presentation condition and canonical scalar structure, was read. This
  theorem is imported as a proof dependency; its conclusion is not used
  as a replacement definition of the local-ring property.
- `Sheaf.RingTheory.CompleteIntersectionLocalAlgebra`:
  `Algebra.IsCompleteIntersectionLocalAlgebra` provides the already landed
  local-ring notion. Its owning node
  `def-trf-complete-intersection-local-algebra` is added to `stmt_deps` under
  the permission to cite an already landed definition node. No new node
  or dependency replacement is needed.

Imports for stated proof dependencies are also retained:
`Sheaf.TraceFormula.LciFieldChangeLocal` supplies
`Algebra.isCompleteIntersectionLocal_fieldChange`;
`WeilConjectures.AlgebraicGeometry.RelativeGlobalCompleteIntersectionPresentation`
supplies `Algebra.IsRelativeGlobalCompleteIntersectionPresentation` and imports
the intrinsic relative-GCI definition. This current upstream module was read
with `scompile.py --source`, since the older source checkout lacks the file.
`Mathlib.RingTheory.Extension.Presentation.Basic` supplies
`Algebra.Presentation.baseChange`; `Mathlib.AlgebraicGeometry.Restrict`,
`Pullbacks`, `Fiber`, and `AffineScheme` (directly or transitively imported)
supply the recorded open-pullback, affine-product, fibre-base-change, and
affine-stalk identifications. The complete-intersection-over-field definitions
are imported by `LciPointwiseCriterion`. The proof-only node
`lem-trf-syntomic-pointwise-local-model` currently has neither a `lean` record
nor a `mathlib_match`, so there is no recorded module to import for it;
its mathematical proof step remains explicitly in the theorem's docstring.

Edge cases checked before drafting: an empty source gives an empty locus;
the empty open is included among competitors. An empty fibre has no points
and imposes no local-ring condition. The zero algebra has empty spectrum,
so it is never mistakenly required to be a local stalk ring. The existing
local-algebra definition permits the empty regular sequence. No characteristic,
Noetherian-base, quasi-compactness, nonemptiness, separability, geometric-point,
or finite-presentation hypothesis is added to base-change compatibility.
Test schemes and coefficient fields have the same universe as the ambient
scheme, as in Mathlib's fibre and base-change APIs; there is no independent
smaller test universe. The presenting algebra in the reused predicate lives
in `max u u = u` and includes all essentially finite type presentations up to
algebra isomorphism. The openness claim is made only under both extra
hypotheses, as in the source.

Searches performed for an exact existing statement:

- `msearch.py ... leanfinder`: "For a locally finite type morphism the fibre
  local complete intersection locus commutes with arbitrary base change and
  is open for flat locally finitely presented morphisms". Eight hits concern
  finite-type, flat, finite-presentation and smooth base change, or universally
  open morphisms. None states this locus theorem.
- `msearch.py ... loogle '"syntomic"'`: zero hits.
- `msearch.py ... grep 'syntomic.*[Ll]ocus|[Ll]ocus.*[Cc]omplete[Ii]ntersection'`:
  zero hits in Mathlib.
- `msearch.py ... leansearch`: "The locus of complete intersection fibre local
  rings of a flat locally finitely presented scheme morphism is open and
  commutes with base change". Eight hits include `UniversallyOpen.of_flat`,
  algebraic smooth-locus openness, flatness, and finite-type base change.
  None is this source-locus statement.
- `rg` in `WeilConjectures`, `lean/Sheaf`, and
  `dag/lean_names_upstream.json` for the item id, syntomic-locus spellings,
  and the proposed names found no existing declaration. The nodal-locus
  module mentions the item only in its proof plan.
- Searching `lean/Sheaf` for `IsCompleteIntersectionLocal` found the existing
  `CompleteIntersectionLocalAlgebra` definition and the instance-based
  `CompleteIntersectionLocal` variant. The former is reused because it
  packages the local/essentially-finite-type conditions without requiring
  new typeclass instances for fibre stalks. It is not a new private copy.

Source checked locally: `literature/stacks-project/morphisms.tex`,
`lemma-set-points-where-fibres-lci` (Tag 02V3), including its complete proof
and final syntomic assertion. The delivered statement keeps every clause
of the node; no statement correction or dispute is needed.

Validation: the prescribed `scompile.py Q125 lem-trf-syntomic-locus-base-change`
compiled the module cleanly under both sandbox and library module names,
in 2.3 and 2.4 seconds respectively. No compiler errors or warnings.

## Second reading by Q125

Author's direct-delivery rereading; the independent review belongs to the
maintainer. No second agent was started, as required by the dispatcher brief.

I reopened the node and the delivered file and matched the local-finite-type
binder to the first paragraph, the canonical fibre stalk and coefficient
structure to the pointwise criterion's local-ring meaning, and the unrestricted
quantifier on base changes to the first conclusion. The two extra assumptions
occur only in the second conjunct. Its open `U` has exactly the specified
underlying set; membership in the `IsGreatest` class asserts all three properties
of its restriction, and the upper-bound clause asserts exactly maximality.
`HasCompleteIntersectionFibres` checks all points of all fibres rather than
merely one chosen point or the geometric fibres. Empty cases introduce no
missing binder or nonempty assumption. No mismatch was found and no statement
was changed. The only DAG adjustment is the permitted additional dependency
on the already landed complete-intersection local-algebra definition.
