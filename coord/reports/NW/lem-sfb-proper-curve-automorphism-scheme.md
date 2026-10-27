## Worker report

The module `Sheaf.AlgebraicGeometry.ProperCurveAutomorphismScheme` states
`AlgebraicGeometry.AlgebraicSpace.exists_proper_curve_automorphism_scheme`.
Its proof is `sorry`. Its three helpers have actual data: the canonical map of a
space to its represented base, its automorphisms over a test scheme, and their
canonical base-change operation. No new DAG node or dependency replacement is needed.
The TeX statement and seven-step proof are unchanged. Three already landed definition
nodes are added to `stmt_deps`, since their declarations supply exactly the existing
space properties and point topology used in this statement.

Every hypothesis and conclusion clause is rendered as follows (names below are in
`AlgebraicGeometry.AlgebraicSpace` unless indicated otherwise):

- Field K: `{K : Type u} [Field K]`; one explicit universe covers the base field and
  all scheme and algebraic-space tests, in the project's fixed-size convention.
- Algebraic space C over K: `C : AlgebraicSpace (Spec (.of K))`, the existing full
  subcategory of fppf sheaves with representable diagonal and an etale surjective atlas.
- Its structural morphism is `automorphismSchemeStructureMap C`. On a test scheme
  `T : Over S` this sends every section to `Over.homMk T.hom`, the uniquely determined
  morphism to `Over.mk (𝟙 S)`. It is a concrete natural transformation, not an arbitrary
  map or a choice of a representable model of C.
- Properness, with exactly the node's four constituent conditions: `hsep` is
  `MapToSchemeIsSeparated` (every scheme test of the diagonal is a closed immersion);
  `hqc` is `MapIsQuasiCompact` (compact point spaces over affine tests); `hlft` is
  `MapToSchemeIsLocally (@LocallyOfFiniteType)` (the property on every representable
  etale scheme chart); and `hclosed` is `MapToSchemeIsUniversallyClosed` (closed maps
  of the existing point spaces after every scheme base change). The conjunction of
  quasi-compactness and local finite type is finite type. These are the existing
  predicates from the proper-curve moduli module; flatness, finite presentation and
  geometric dimension are NOT separately assumed.
- Dimension at most one: `hdim : topologicalKrullDim (Point C.obj.obj) ≤ 1`, using
  the existing quotient of field-valued points and its existing etale atlas topology.
- Group scheme: `G : CategoryTheory.Grp (Over (Spec (.of K)))`. The bundled structure
  contains `GrpObj G.X`, hence actual scheme morphisms for multiplication, unit and
  inverse, with all group diagrams. No commutativity is required.
- Separated finite type: `IsSeparated G.X.hom ∧ LocallyOfFiniteType G.X.hom ∧
  QuasiCompact G.X.hom`. This is exactly the recorded scheme terminology.
- Representation on every K-scheme T: `θ : ∀ T : Over (Spec (.of K)),
  (T ⟶ G.X) ≃* curveAutomorphisms C T`. A multiplicative equivalence is a bijection
  preserving composition and identity (and therefore inversion).
- The actual target automorphism group is
  `Aut ((Over.forget T).op ⋙ C.obj.obj)`. Here `Over T` is the slice of `Over S`,
  canonically equivalent to schemes over `T.left`. A sheaf over `h_T` is equivalently
  a sheaf on this slice; the sheaf `C ×_S h_T` becomes exactly this restriction.
  Consequently its natural automorphisms are precisely the automorphisms of
  `C ×_K T` over T, with their usual composition. This uses the sheaf fibre product,
  and agrees with scheme fibre products under Yoneda when C is a scheme.
- Naturality for every `a : T' ⟶ T` and `g : T ⟶ G.X` is
  `θ T' (a ≫ g) = curveAutomorphismBaseChange C a (θ T g)`.
  The helper is `Functor.isoWhiskerLeft (Over.map a).op`; the equality
  `Over.map a ⋙ Over.forget T = Over.forget T'` is definitional. This is canonical
  pullback of the automorphism to the actual base-changed sheaf. Naturality together
  with the group equivalences includes compatibility of composition after every
  base change. There are no restrictions on T or a.

Dependency declarations read and used:

- `def-weil-field`: Mathlib `Field` (Algebra/Field/Defs), the standard field structure.
- `def-trf-algebraic-space`: `Sheaf.AlgebraicGeometry.AlgebraicSpace`, declaration
  `AlgebraicGeometry.AlgebraicSpace`, its full signature and sheaf/atlas definition.
- `def-kun-topological-krull-dimension`: `Mathlib.Topology.KrullDimension`,
  `topologicalKrullDim`, defined as the Krull dimension of `IrreducibleCloseds`.
- `def-sc-group-scheme`: `Mathlib.CategoryTheory.Monoidal.Grp`, `CategoryTheory.GrpObj`
  and `CategoryTheory.Grp`; the functor-of-points group is Mathlib
  `CategoryTheory.Hom.group` from `Mathlib.CategoryTheory.Monoidal.Cartesian.Grp`.
  The scheme interpretation agrees with the docstring of the recorded upstream
  `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs`.
- `def-weil-finite-type-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`,
  `AlgebraicGeometry.LocallyOfFiniteType`, together with
  `AlgebraicGeometry.QuasiCompact`. The record explicitly specifies their conjunction.
- `def-weil-proper-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Proper`,
  `AlgebraicGeometry.IsProper`, `IsSeparated`, `UniversallyClosed`; for spaces use
  exactly their existing scheme-test/chartwise versions listed below.
- `def-pc-fibre-product`: `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`,
  `CategoryTheory.Limits.pullback` and its projections; the existing space-property
  definitions use these presheaf fibre products. The restriction description of
  base change uses the same fibre product via the slice equivalence.
- Added landed node `def-sfb-proper-curve-moduli`:
  `Sheaf.AlgebraicGeometry.ProperCurveModuli`, `MapToSchemeIsSeparated`,
  `MapIsQuasiCompact`, `MapToSchemeIsLocally`, `MapToSchemeIsUniversallyClosed`.
  The full module and the definitions of `mapPoint` and the curve-family predicate
  were read. The stronger `IsProperCurveFamily` predicate is not used as a hypothesis.
- Added landed nodes `def-a1-algebraic-space-point-classes` and
  `def-a1-space-point-topology`: modules
  `Sheaf.AlgebraicGeometry.AlgebraicSpacePointClasses` and
  `Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology`, declarations `Point` and
  `pointTopologicalSpace`. Both defining modules were read in full.

All already stated proof dependencies are imported: projectivity from
`Sheaf.AlgebraicGeometry.Curve.ProperProjective`, dimension invariance from
`Sheaf.AlgebraicGeometry.DimensionExtension`, the graph representative from
`Sheaf.AlgebraicGeometry.ProjectiveCurveIsomGraphs`, and the Mathlib Noetherian,
flatness, finite-presentation, quasi-separatedness, finite-type, pullback, group-object,
and Yoneda APIs available through the listed imports. These three project modules
were read in full. The sole still-unstated non-Mathlib proof dependency is
`lem-sfb-separated-space-dimension-one-scheme`; there is no module to import for it.
It is a proof dependency, not a prerequisite needed to state this theorem.

Edge cases checked mathematically:

- Empty C is allowed: its dimension is bottom, and its automorphisms on every test
  scheme are trivial; its representative is the terminal K-scheme, with trivial group.
- Zero-dimensional, disconnected and nonreduced C are not excluded. For
  `Spec K[ε]/(ε²)`, automorphisms of a base change are the algebra automorphisms over
  the test base; the full slice restriction retains nilpotents and their deformation
  information. No reduction or field-points-only approximation is used.
- `P¹` has the expected noncommutative group PGL₂; there is no commutativity binder.
- Identity and arbitrary base-change maps, including nonreduced and empty test
  schemes, enter the universal naturality quantifier. Pullback is actual restriction,
  not a freely supplied map. No smoothness, connectedness, reducedness, projectivity,
  stability or nonemptiness assumption occurs.
- The automorphism types can live in universe u+1 because they are natural
  transformations on a large slice; `MulEquiv` relates them to the small group of
  scheme morphisms without adding a smallness hypothesis or restricting test schemes.

Searches for an existing statement (2026-10-22):

- `msearch.py ... leanfinder "The automorphism functor of a proper algebraic space of
  dimension at most one over a field is represented by a separated group scheme of
  finite type"`: eight hits on abstract Galois categories, field spectra, and scheme
  morphism properties; no statement of this representability theorem.
- `msearch.py ... loogle "AlgebraicGeometry.AlgebraicSpace, CategoryTheory.GrpObj,
  Aut"`: no hit; the Mathlib index does not contain the project AlgebraicSpace type.
- `msearch.py ... leansearch "Automorphism functor of a proper curve over a field
  is represented by a finite type group scheme"`: eight hits on abstract automorphism
  groups and Galois functors, including `CategoryTheory.Aut`; no curve representative.
- `msearch.py ... grep "automorphism.*scheme|Aut.*[Cc]urve|[Pp]roper.*[Aa]lgebraic[Ss]pace"
  AlgebraicGeometry`: no Mathlib hit.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for the item id, automorphism
  representability, and all four proposed declaration names: no existing statement;
  only the downstream infinitesimal-DM-locus docstring cites the DAG item.
- Further project searches for properness and point maps found
  `ProperCurveModuli.lean`; its landed predicates are reused. DAG lookup confirmed
  the owning definition node, point-class node, and point-topology node already exist.
  No duplicate definition node is introduced.

Sources checked locally: Stacks `moduli-curves.tex`, Tag 0DSQ and its proof,
including the boundedness paragraph for arbitrary proper curves and the preceding
scheme/projectivity reduction; `spaces-more-groupoids.tex`, Tag 0B8F.
No mathematical statement correction or dispute is needed.

The previous worker's claimed blocker confused Q32's stage-1 merge with a stage-2
landing: the current node has `reviewed` from Q32 but no `lean` or `reviewed_lean`.
This delivery supplies the missing stage-2 interface.

Validation: `scompile.py NW lem-sfb-proper-curve-automorphism-scheme` compiled the
module in both its sandbox and its final library name with no errors or warnings.
The only postponed theorem is the main theorem above. The definition helpers
contain no `sorry` and use no arbitrary choice of data.

## Second reading by NW

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
