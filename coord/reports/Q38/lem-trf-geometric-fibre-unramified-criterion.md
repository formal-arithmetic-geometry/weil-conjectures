## Worker report

The module `Sheaf.AlgebraicGeometry.GeometricFibreUnramifiedCriterion` states
`AlgebraicGeometry.unramified_iff_unramified_geometric_fibres`, with proof `by sorry`.
There are no new definitions, dependency modules, or statement corrections.

Clause-by-clause translation:

- Schemes and the morphism `h : Z → B` are `{Z B : Scheme.{u}} (h : Z ⟶ B)`.
  The universe `u` is explicit and arbitrary.
- “Locally of finite type” is the sole hypothesis `[LocallyOfFiniteType h]`.
- Each point is quantified by `∀ s : B`. Its residue field is `B.residueField s`.
- The chosen algebraic closure is Mathlib's `AlgebraicClosure (B.residueField s)`,
  with its canonical `algebraMap`. This is precisely the chosen closure allowed by
  the node and its geometric-fibre dependency record; it is in the same universe.
  The criterion is independent of replacing this closure by an isomorphic closure.
- The canonical geometric point is
  `Spec.map (CommRingCat.ofHom (algebraMap (B.residueField s)
  (AlgebraicClosure (B.residueField s)))) ≫ B.fromSpecResidueField s`.
- The fibre morphism to the spectrum of that closure is `pullback.snd h` applied
  to this composite, whose domain is exactly the required scheme fibre product.
  This expression is repeated verbatim in the two clauses of unramifiedness.
- On both sides, “unramified” is the recorded inline form
  `LocallyOfFiniteType f ∧ IsOpenImmersion (pullback.diagonal f)`.
- The equivalence is `↔`; “every” is `∀ s : B` without restricting to closed points.
- Empty geometric fibres are allowed: there is no `Nonempty` or surjectivity
  hypothesis. No flatness, local finite presentation, quasi-compactness, separatedness,
  characteristic restriction, or Noetherian condition is assumed on either scheme.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`:
  `AlgebraicGeometry.LocallyOfFiniteType`, the local-finite-type component of
  `def-weil-finite-type-morphism` and of `def-weil-unramified-morphism`.
- `Mathlib.AlgebraicGeometry.ResidueField` (public through `Fiber`):
  `AlgebraicGeometry.Scheme.residueField` and `Scheme.fromSpecResidueField`.
  The induced `Scheme.Hom.residueFieldMap` was also read; it is not needed in this signature.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback` (public through `Fiber`):
  `CategoryTheory.Limits.pullback` and `pullback.snd`. These implement exactly
  the inline `def-weil-geometric-fibre` record. The diagonal is
  `CategoryTheory.Limits.pullback.diagonal` from
  `Mathlib.CategoryTheory.Limits.Shapes.Diagonal`.
- `Mathlib.AlgebraicGeometry.OpenImmersion` (public through the statement imports):
  `AlgebraicGeometry.IsOpenImmersion`.
- `Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure`: `AlgebraicClosure` and its field
  extension structure. This is the standard closure construction, not a new notion.

The three already-stated non-Mathlib proof dependencies are imported non-publicly:
`WeilConjectures.AlgebraicGeometry.Morphisms.UnramifiedBaseChangeOpen`
(`AlgebraicGeometry.unramified_baseChange_restrict_open`, read with `scompile.py --source`),
`Sheaf.AlgebraicGeometry.FieldExtensionFpqcCover`
(`AlgebraicGeometry.fpqcCover_specMap_algebraMap_of_field`), and
`Sheaf.AlgebraicGeometry.Morphisms.UnramifiedDescent`
(`AlgebraicGeometry.locallyOfFiniteType_and_openDiagonal_of_fpqcCover`).
The ordinary-fibre definition is already supplied by `Mathlib.AlgebraicGeometry.Fiber`.
`lem-trf-unramified-field-fibre-decomposition` and
`lem-trf-unramified-ordinary-fibre-criterion` have no Lean record yet, so there is no
module to import for these proof-only dependencies. Both remain in the node and
are cited explicitly in the four-step proof docstring. They are unnecessary for
stating the item and are not restated here.

Source and edge cases:
Read `literature/stacks-project/morphisms.tex`, the lemmas
`lemma-unramified-over-field` (02G7) and `lemma-unramified-etale-fibres` (02G8),
including all clauses and their proofs. Also read Descent,
`lemma-descending-property-unramified` (02VM), and the open-diagonal criterion
02GE. The ordinary-fibre criterion needs local finite type only;
local finite presentation belongs to its separate G-unramified clause.
The geometric-to-ordinary passage is fpqc descent along the closure extension.
An empty base makes the right side vacuous and forces the source empty; an empty
source and empty individual geometric fibres are also permitted. Identity maps
satisfy both sides. A purely inseparable finite field extension fails both sides,
since its geometric fibre is nonreduced; closed immersions such as
`Spec (Z/p) → Spec Z` satisfy the criterion without a flatness hypothesis.
Arbitrary disjoint unions are permitted because no quasi-compactness was imposed.
No node fault or disputed statement was found.

Searches for existing declarations (all performed for this item using `msearch.py`):

- LeanFinder: “A locally finite type morphism of schemes is unramified if and only if
  every geometric fibre is unramified”. Eight hits, including
  `FormallyUnramified.isOpenImmersion_diagonal`, `formallyUnramified_iff`, and étale
  postcomposition facts; no scheme geometric-fibre criterion.
- Loogle: `AlgebraicGeometry.FormallyUnramified,
  AlgebraicGeometry.Scheme.Hom.fiberToSpecResidueField`. Zero hits.
- Grep: `unramified.*[Ff]ib|[Ff]ib.*[Uu]nramified` in `AlgebraicGeometry`.
  Zero Mathlib hits.
- LeanSearch: “A locally finite type morphism of schemes is unramified if all geometric
  fibres are unramified”. Eight hits: formal-unramified definitions, constructors,
  local quasi-finiteness, and algebra unramifiedness; no exact theorem.
- `rg` for unramified/fibre combinations in the upstream `WeilConjectures/` and
  side `lean/Sheaf/` found field-fibre tools and local decomposition lemmas, not this
  criterion. `rg` of the item id in `WeilConjectures/` and
  `dag/lean_names_upstream.json` found no declaration. Separate `geometricFiber`
  searches found the etale fibre functor and upstream fibres over an already-given
  field; these do not state the required arbitrary-base criterion.

The delivery changes only the item's `lean` record. Its `statement` field is copied
verbatim from the declaration signature. Compilation is through `scompile.py` only. The final module compiled without
errors or warnings as both the isolated sandbox file (7.6 s) and its actual
library-path file (11.9 s), within the standard 60 s limit.

## Second reading by Q38

Self-review only: this dispatcher brief prohibits starting other agents and assigns
independent review to the maintainer; no independent reviewer is claimed here.
Re-read the node and final file side by side. Checked each binder and both conjunctions,
the direction and codomain of `Spec.map`, the order of composition with the canonical
residue point, and that the second pullback projection is the structure morphism
rather than the projection to `Z`. The initial extra geometric-fibre helper module
was removed because the existing dependency record already specifies the exact
inline pullback. The final delivery reuses that record directly, contains only
one theorem, and retains exactly the local-finite-type hypothesis. The header,
100-character width, explicit universe, source, and all four proof steps were checked.
