## Worker report

The module `Sheaf.AlgebraicGeometry.NeronLftWeilRestrictionGeometry` states
`AlgebraicGeometry.exists_neronLft_weilRestriction_geometry`. Its only postponed proof is
that theorem, with the node's seven-step proof in its docstring. The three auxiliary
definitions belong to the same construction: the canonical base-changed evaluation,
the canonical generic evaluation, and the geometric neutral subset. They contain real
data and no `sorry`. There are no new nodes, dependency repairs or statement changes.

Source read: the primary BLR scan at
https://www.math.stonybrook.edu/~kamenova/homepage_files/Bosch_Raynaud_Neron_Model_tc.pdf,
7.6 (PDF pages 197–204), especially the definition and base-change formula, Theorem 4
and Proposition 5; 10.1 (PDF pages 295–297), Definition 1, the paragraph on the identity
component, and Proposition 4. The local source is marked WANTED in the inherited node.
The statement follows these places without adding quasi-projectivity, quasi-compactness
of M, separability of E'/E, connectedness of V, or finite component groups.

Hypotheses and their Lean renderings:

- D and D' are commutative Dedekind domains: `[CommRing D]`, `[CommRing D']`,
  `[IsDedekindDomain D]`, `[IsDedekindDomain D']`, with `_dimD` and `_dimD'` asserting
  `ringKrullDim ... = 1`. Mathlib's Dedekind class includes dimension zero, so these
  two conditions render the node's explicit dimension-one convention exactly.
- The given map D → D' is `algebraMap D D'`. Its finiteness as a module is
  `[Module.Finite D D']`, and faithful flatness is `[Module.FaithfullyFlat D D']`.
  The map is injective by faithful flatness, so a separate injection assumption is
  unnecessary.
- E and E' are fields with `[IsFractionRing D E]` and `[IsFractionRing D' E']`.
  The E-algebra structure on E' and the two `IsScalarTower` instances specify the
  canonical compatible inclusions in the square. These are the fraction-field maps,
  not an arbitrary independent extension. S and S' are literally `Spec (.of D)` and
  `Spec (.of D')` everywhere.
- V is `Grp (Over (Spec (.of E')))`. `IsCommMonObj V.X` is commutativity,
  `Smooth V.X.hom` and `IsSeparated V.X.hom` are smoothness and separatedness,
  and `LocallyOfFiniteType V.X.hom` with `QuasiCompact V.X.hom` is finite type.
- M is a group object over `Spec D'`, smooth and separated. Its generic-fibre
  isomorphism is `e`; `IsMonHom e.hom` records that it is the group-scheme
  generic identification. No finite type or quasi-compactness of M is assumed.
- `_neron` quantifies over every `Y : Over (Spec D')` with `Smooth Y.hom`, and
  requires bijectivity of the actual map `f ↦ (Over.pullback j').map f ≫ e.hom`.
  Thus it is restriction followed by the specified generic identification.

Conclusions, clause by clause:

- `∃ W : Grp (Over (Spec D))` supplies the scheme and its actual group operations.
  `IsCommMonObj W.X`, `Smooth`, `IsSeparated` and `LocallyOfFiniteType` give exactly
  the first geometric conclusions.
- `ev : (Over.pullback p).obj W.X ⟶ M.X` is universal evaluation. For every
  `X : Over (Spec D)`, `Function.Bijective (fun f => (Over.pullback p).map f ≫ ev)`
  states the required Hom bijection. This is a natural family because pullback is
  a functor and the map is composition with one fixed evaluation morphism; no
  arbitrary family of set equivalences is substituted. `IsMonHom ev` says that
  these bijections identify group operations with pointwise operations, including
  the identity and inverse, since pullback preserves group objects.
- Every scheme `T : Scheme.{u}`, every `t : T ⟶ Spec D`, and every `X : Over T`
  occur in the base-change clause. Its target is the pullback of M along
  `pullback.fst p t : S' ×_S T ⟶ S'`, over `S' ×_S T`, exactly as corrected in
  the stage-1 review. `weilRestrictionEvaluationBaseChange` is obtained from
  the original `ev` using `Over.pullbackComp`, the equation of the pullback square,
  and pullback of `ev`. Bijectivity is asserted for that specific map. The
  comparisons are canonical, so the family has the usual compatibility with
  precomposition and further base change.
- The next two conjuncts are `LocallyOfFiniteType` and `QuasiCompact` of W's
  pullback to `Spec E`, hence finite type of W_E. The generic Hom bijections
  use `weilRestrictionGenericEvaluation D D' E E' ev e`, built from the original
  evaluation, pullback composition, the scalar-tower equality and e. Thus the
  stated functor is precisely `Hom_E'(X ×_E E', V)`, with the given identification.
- The last existential supplies a group scheme W₀ and a homomorphism `i` into W.
  `IsOpenImmersion i.left` makes it an open subgroup with its open subscheme
  structure. `Set.range i.left.base = neronGeometricNeutralSet W` specifies
  exactly which open subgroup. The defining set is the union, over every base
  point s, of the images under `pullback.fst` of the connected component of the
  identity in the geometric fibre over `AlgebraicClosure (S.residueField s)`.
  The algebraic-closure choice does not affect this union. The last two
  conjuncts give local finite type and quasi-compactness, hence finite type of W₀.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `Scheme`, `Scheme.Hom`, `Spec`, `Spec.map`.
- `Mathlib.RingTheory.Finiteness.Defs`: `Module.Finite` (top submodule finitely generated).
- `Mathlib.RingTheory.Flat.FaithfullyFlat.Basic`: `Module.FaithfullyFlat`, extending flatness.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `Smooth` (affine-locally smooth ring maps).
- `WeilConjectures.AlgebraicGeometry.BaseChangeConventions`: the documented scheme
  convention `Over.pullback`; its object and morphism source was read in
  `Mathlib.CategoryTheory.Comma.Over.Pullback`. The module-base-change declaration
  is not substituted for scheme base change.
- `Mathlib.Topology.Connected.Basic`: `ConnectedSpace`, `connectedComponent`.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`, `fst`, `snd`;
  `Mathlib.AlgebraicGeometry.Fiber`: fibre as the pullback along the residue-field map.
- `Mathlib.CategoryTheory.Monoidal.Grp`: `Grp`, `GrpObj`, `Functor.mapGrp`;
  `Mathlib.CategoryTheory.Monoidal.Mon`: `IsCommMonObj`, `IsMonHom`.
  Group objects work over any scheme, so the field-based group-scheme node needs no copy.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`;
  `Mathlib.AlgebraicGeometry.Morphisms.Separated`: `IsSeparated` is exactly that
  the diagonal is a closed immersion.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`;
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`: `QuasiCompact`.
- `WeilConjectures.AlgebraicGeometry.GroupScheme.Basic`: `GrpObj.onePoint` supplies
  the identity point of each geometric-fibre group.

All recorded proof-dependency modules that currently have statements are imported.
The four newly split geometric/Néron proof inputs have no recorded Lean modules in
this snapshot; no nonexistent module import is invented. The Mathlib proof inputs
are also imported (finite morphisms, affine finite-flat bases, finite free spectra,
finite localization, localization base change, affine spectra pullbacks, affine
quasi-compactness, continuous compact images, smooth base change and Yoneda).

Edge cases checked: D'=D and E'=E are allowed; no nontrivial-extension hypothesis.
Ramified and inseparable extensions are allowed. The trivial generic group and
models with infinitely many components are allowed; the conclusion only asserts
finite type of the generic fibre and the neutral part. V need not be connected.
Smooth test schemes Y, all test schemes X, and arbitrary base-change schemes T may
be empty, nonreduced, nonaffine and non-quasi-compact. Their Hom maps remain the
same literal canonical maps. Arbitrary residue characteristics are included.
Every ring and test scheme is in the common arbitrary universe u, so test objects
are not in an independently smaller universe. All binders and universes are
explicit and `autoImplicit` is false. Fields are excluded for D and D' only because
the node explicitly defines Dedekind domains to have dimension one.

Searches actually run with `msearch.py Q114 lem-sfb-neron-lft-weil-restriction-geometry`:

- `leanfinder`: "Weil restriction of a Neron lft group scheme finite flat Dedekind domain
  smooth separated finite type identity component". Eight results, concerning
  Weierstrass integral models, algebraic smooth descent/base change, and scalar
  extension of elliptic points; none states this node.
- `loogle`: `"WeilRestriction"`. Zero hits.
- `grep`: `WeilRestriction|Neron|neron|neutralComponent` in AlgebraicGeometry. Zero hits.
- `leansearch`: "Neron lft model mapping property restriction of scalars smooth group
  schemes". Eight hits, all ordinary module/algebra restriction of scalars; no match.
- Local `rg` searches of both `lean/WeilConjectures` and `lean/Sheaf` for Neron,
  Néron, neron, WeilRestriction, weilRestriction, geometricIdentity and neutralComponent
  found only the field-group component-translate theorem and unrelated coefficient
  Weil restrictions. The node-id grep in WeilConjectures had no hit. No existing
  module states the theorem or supplies the relative geometric neutral set.
- The DAG definition-node search for Néron lft and Weil restriction found no such
  definition interface. The required constructions are helpers of this node,
  recorded in its `lean.declarations`, rather than private copies of dependencies.

Validation: scompile.py compiled the module in both sandbox and library module modes
cleanly within 60 seconds (latest run before final import list: 2.9 seconds each).
The delivery dry run performs the final compile and preflight.

## Second reading by Q114

A second source-to-signature pass was made with the node and the completed module
open. This was a separate pass by the same worker; the dispatcher explicitly
forbids starting other agents, so an independent worker reading is not claimed.
The maintainer's independent delivery review remains applicable.

The pass checked the dimension-one convention against Mathlib's dimension-at-most-one
class, checked that finite means module-finite, and checked both fraction-field
towers. It checked the generic group, M, e and the smooth-test restriction map;
then each existential conclusion and every conjunct against the node. Two changes
were made during the pass: removed an unnecessary commutativity assumption on M,
and replaced an existential generic evaluation by the specific evaluation
constructed from ev and e. In particular the generic Hom bijection cannot be
chosen independently of the given identification. Arbitrary base change is over
all schemes T and uses M ×_{S'} (S' ×_S T), not the erroneous product over S.
The identity subgroup is pinned by the full geometric-fibre union, not by the
connected component of the total space or an unspecified open subgroup. No
remaining mismatch or disputed statement was found.
