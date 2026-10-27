## Worker report

The module `Sheaf.AlgebraicGeometry.AbelianSubvarietyCentral` states
`AlgebraicGeometry.abelianSubvariety_central`, with its sole proof `sorry`.
No new definitions, dependency repairs, or statement corrections are needed.
Only the item's `lean` field changes. All variables and the universe are explicitly bound.

Hypotheses and clauses, checked against the full node statement:

- Algebraically closed field: `{k : Type u} [Field k] [IsAlgClosed k]`.
- The two group schemes: `(G A : Over (Spec (.of k))) [GrpObj G] [GrpObj A]`.
  The slice category supplies their structure maps and all morphisms over k.
- Smooth G: `[Smooth G.hom]`.
- Connected G: `[ConnectedSpace G.left]`, including nonemptiness.
- Separated G: `[IsSeparated G.hom]`, whose defining field says its diagonal is
  a closed immersion.
- Finite type G: `[LocallyOfFiniteType G.hom] [QuasiCompact G.hom]`, exactly the
  conjunction prescribed by the finite-type dependency's record.
- Abelian variety A: `[IsAbelianVariety A]`, whose three parent classes are
  `IsProper A.hom`, `Smooth A.hom`, and `ConnectedSpace A.left`. Its group structure
  is separately supplied by `[GrpObj A]`, as that dependency requires.
- Closed subgroup inclusion: `(i : A ⟶ G) [IsClosedSubgroupScheme i]`. The class
  supplies the homomorphism and injectivity on algebra points through its
  `IsSubgroupScheme` parent, and the closed immersion of `i.left`.
- Every commutative k-algebra: `∀ (B : Type u) [CommRing B] [Algebra k B]`.
  This uses the same universe convention as `IsSubgroupScheme` and
  `IsNormalSubgroupScheme`, rather than an independent possibly smaller test universe.
- Every point a and g: morphisms from
  `Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k B)))` to A and G respectively.
- The asserted identity is `(a ≫ i) * g = g * (a ≫ i)`. Composition is the actual
  functor-of-points map, and multiplication is the group-object multiplication
  on the Hom set, enabled by `open scoped CategoryTheory.MonObj`.
- Centrality is precisely the preceding universally quantified identity. The
  explicit final conjunct `IsNormalSubgroupScheme i` records the stated consequence
  of normality for every algebra, using the dependency's existing definition.
- There is no affine, proper, or commutative structure on G among the binders.
  The dimension convention in the node introduces no dimension bound or dimension
  conclusion; accordingly the signature has no artificial dimension hypothesis.

Dependency declarations read and used:

- `Mathlib.Algebra.Field.Defs`: `Field`.
- `Mathlib.FieldTheory.IsAlgClosed.Basic`: `IsAlgClosed` (the algebraic-closure
  node's match explicitly identifies this as the algebraically closed predicate).
- `Mathlib.CategoryTheory.Monoidal.Grp`: `CategoryTheory.GrpObj`; its Cartesian
  companion gives `CategoryTheory.Hom.group`, while Cartesian.Mon gives
  `CategoryTheory.IsMonHom.monoidHom` with `toFun := (· ≫ i)`.
- `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs`:
  `AlgebraicGeometry.IsClosedSubgroupScheme`, `IsSubgroupScheme`, and
  `IsNormalSubgroupScheme`, using their actual full signatures and docstrings.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth`.
- `Mathlib.Topology.Connected.Basic`: `ConnectedSpace`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`;
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`: `QuasiCompact`.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `IsProper`;
  `Mathlib.AlgebraicGeometry.Morphisms.Separated`: `IsSeparated`.
- `Mathlib.Topology.KrullDimension`: `topologicalKrullDim` was read; there is no
  dimension expression in this item's assertion. It is already transitively
  imported by the abelian-variety interface.
- `WeilConjectures.AlgebraicGeometry.AbelianVariety.Defs`: `IsAbelianVariety`.
- Proof-only imports: `WeilConjectures.AlgebraicGeometry.AbelianVariety.Basic`
  supplies `IsAbelianVariety.geometricallyIntegral`, and
  `WeilConjectures.AlgebraicGeometry.AbelianVariety.Rigidity` supplies
  `exists_eq_snd_comp`. These are the recorded proof dependencies, imported without
  `public`. No recorded proof dependency is omitted and there is no import cycle.

The module docstring includes the source and blueprint id, and the theorem docstring
carries all four proof steps: geometric integrality, construction and axis identities
of the mixed commutator, rigidity and the identity section, evaluation and cancellation
on algebra points, with normality as in the subgroup definition.

Sources opened locally using pdftotext: Milne, Algebraic Groups, paragraph preceding
Proposition 8.12, Corollary 8.13 and Definition 8.15 (printed p.151); Milne, Abelian
Varieties, Theorem 1.1 and its proof (printed pp.8–9). The former explicitly gives
centrality of anti-affine subgroups and identifies complete connected group varieties
as anti-affine; the latter supplies rigidity for the two contracted coordinate axes.
The recorded upstream rigidity declaration is the factorization form for schemes,
with arbitrary fibre point and a separated target. Its signature was read in full.

Edge cases checked before writing: trivial A, identity inclusion G=A, and
G=A×SL₂ (properness and commutativity of G must not be assumed). Empty A or G is
excluded by the existing nonempty connectedness convention and group identity.
No positive dimension assumption excludes the trivial subgroup. All characteristics
are allowed. B may be nonreduced, e.g. dual numbers, or the zero algebra: it is not
required to be a field, reduced, nontrivial, or finite type. The proof is an equality
of scheme morphisms before evaluation, so it applies to these tests too.

Searches performed with msearch.py (the sandbox searches.jsonl records raw results):

- LeanFinder: "An abelian variety closed subgroup of a connected algebraic group
  scheme is central". Eight hits, headed by `CommGroup.center_eq_top`,
  `Subgroup.center.isMulCommutative`, `Subgroup.centerCharacteristic`, and
  `commutator_eq_bot_iff_center_eq_top`: abstract group statements, no match.
- Loogle: `"IsAbelianVariety", "GrpObj"`. Zero hits.
- Mathlib grep: `abelian.*centr|centr.*abelian|anti.affine`, subdirectory
  AlgebraicGeometry. Zero hits.
- LeanSearch: "Every abelian subvariety of a connected algebraic group is contained
  in its centre". Eight abstract group/Lie algebra hits, headed by
  `Subgroup.le_centralizer`; none is the scheme centrality assertion.
- Direct rg over lean/WeilConjectures and lean/Sheaf with the same regexp and the
  exact node id found only unrelated abelian-category concentration references.
  A further central/center scan of the upstream group-scheme files found
  `GeneralLinearGroup.central_subgroupSchemeHom_le_center`, whose hypotheses and
  objects concern an explicitly presented affine linear group and its already
  constructed centre, not an arbitrary non-affine G and abelian subvariety.
- Exact declaration-name search `abelianSubvariety_central` in Mathlib, upstream,
  Sheaf and dag/lean_names_upstream.json found no existing declaration.

No statement dispute or node fault found. The example CompactObject Sheaf module
is now explicitly withdrawn; its node points to the upstream declaration, consistent
with using the existing upstream interfaces here.

Validation: scompile.py compiled the delivered file in sandbox and library mode,
1.8 seconds each, with no errors or unexpected warnings.

## Second reading by Q138

I reopened the node and the completed signature for a separate reading. No other
agent was started, as the dispatcher brief expressly forbids it; this is a worker
self-check, and the maintainer's independent delivery review remains separate.
The field and algebraic-closed binders match k; slice objects and GrpObj match the
two group schemes; Smooth, ConnectedSpace, IsSeparated, LocallyOfFiniteType and
QuasiCompact match every stated G hypothesis; IsAbelianVariety supplies exactly the
three A properties; IsClosedSubgroupScheme supplies exactly the closed subgroup
homomorphism. The quantifier binds arbitrary algebras and both points, not only
k-points, and the multiplication identity has the right order on each side.
The IsNormalSubgroupScheme conjunct preserves the final normality conclusion.
There is no extra dimension, affineness, properness or commutativity assumption on G.
The proof documentation uses the recorded rigidity theorem and the actual identity
section, not a chosen factorization map as a hypothesis. No mismatch was found and
no statement change was made.
