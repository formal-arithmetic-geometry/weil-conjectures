## Worker report

`Sheaf.AlgebraicGeometry.GroupScheme.Geometry` states the complete bundle as
`AlgebraicGeometry.algebraicGroup_geometry`, with one `sorry` and no new definitions.
The node changes in `lean`, the missing Lie API citation in `statement`, its matching
`stmt_deps` entry, and the required citation-only `statement_change` record. The source read was the current
`literature/blueprint/latest/blueprint/sec-algebraic-groups-lie-algebras/sk-p-geometry/`
section and proof, together with the accepted node's ten expanded proof steps.
The theorem docstring carries all ten steps and names their dependencies.

Hypothesis and clause correspondence:

| Node | Lean |
| --- | --- |
| Algebraically closed field L, characteristic zero | `(L : Type u) [Field L] [IsAlgClosed L] [CharZero L]` |
| A group scheme over L | `(G : Over (Spec (.of L))) [GrpObj G]` |
| G is finite type | `[LocallyOfFiniteType G.hom] [QuasiCompact G.hom]` |
| Finitely many connected components | `Finite (ConnectedComponents G.left)` |
| Identity component with its open subscheme structure | The existing `GrpObj.identityComponent G` and inclusion `GrpObj.identityComponentι G` |
| Open and closed identity component | `IsOpenImmersion ...left` and `IsClosedImmersion ...left` for that inclusion |
| Irreducible | `IrreducibleSpace (GrpObj.identityComponent G).left` |
| Normal subgroup scheme, on all algebra-valued points | `IsNormalSubgroupScheme (GrpObj.identityComponentι G)`; its definition quantifies over every commutative L-algebra R |
| All components are cosets | For every scheme point x, there is a rational point g whose left translation sends the identity component to `connectedComponent x` |
| A homomorphism of algebraic groups | The H binder has `GrpObj`, local finite type and quasi-compactness; `(f : G ⟶ H) [IsMonHom f]` |
| Underlying image closed | `IsClosed (Set.range f.left)` |
| Reduced induced closed scheme on that image | `IsReduced f.left.image` and `Set.range f.left.imageι = Set.range f.left`; `imageι` is already a closed immersion by construction |
| The image is a subgroup scheme | There exists a `GrpObj` on the canonical object `Over.mk (f.left.imageι ≫ H.hom)` with `IsClosedSubgroupScheme` for its canonical inclusion |
| Image on L-points exactly the subgroup's L-points | Equality of ranges of postcomposition by f and by that canonical inclusion, on `𝟙_ (Over (Spec (.of L)))`-points |
| G connected for either equality criterion | `∀ [ConnectedSpace G.left]` governs just the final conjunct |
| Closed subgroup K of G | `(K : Over (Spec (.of L))) [GrpObj K] (i : K ⟶ G) [IsClosedSubgroupScheme i]` |
| Lie equality via the inclusion differential | `Function.Bijective (GrpObj.differential i)` |
| Conclusion K = G as a closed subscheme | `IsIso i.left` for the specified inclusion |
| Dimension complement | `topologicalKrullDim K.left = topologicalKrullDim G.left → IsIso i.left` |

The first image assertion already covers arbitrary finite-type group schemes and hence
its matrix-group complement; the equality of ranges explicitly includes the complement's
rational-point claim. The final dimension criterion likewise directly covers the stated
closed subgroup J. Neither complement is dropped. No representation or extra affineness
hypothesis is imposed. `sk-d-geometry` has no usable recorded Lean binding, but no
matrix-specific notion is needed in this universal formulation: its matrix cases are
instances of the same quantified group-scheme clauses. Thus no replacement definition
of matrix groups is introduced, and no dependency-node modification is needed.

The canonical scheme-theoretic image gives the specified reduced induced closed structure
here: a map from a reduced source has radical kernel ideals; Cartier makes G reduced.
Together with the stated closed support, uniqueness in
`lem-weil-pbc-reduced-induced-closed-subscheme` identifies this with the node's structure.
There is no arbitrary choice of a map or an unspecified subgroup.

The Lie encoding is the existing canonical tangent encoding, rather than an equality of
abstract Lie algebras: `GrpObj.lieIdentityTangentEquiv` identifies `GrpObj.Lie` with
`schemeTangentSpace` at the identity, with the canonical residue-field identification.
The docstring and defining formula of `GrpObj.differential` give postcomposition on
infinitesimal points; `GrpObj.tangentPoint_differential` explicitly says
`tangentPoint (differential i v) = tangentPoint v ≫ i`. Thus bijectivity is exactly the
node's assertion that the inclusion identifies the tangent spaces. The recorded tangent
module is publicly imported, and the recorded identity-tangent equivalence is imported
with the proof dependencies.

Statement dependency interfaces read:

- `def-wf-lie-algebra-derivation`: the existing `AlgebraicGeometry.GrpObj.Lie`
  construction and canonical `AlgebraicGeometry.GrpObj.lieEquivTangent`, recorded in
  `WeilConjectures.AlgebraicGeometry.GroupScheme.Lie.Bracket`. Its additive group,
  module and Lie bracket are the recorded upstream instances. The module's existing
  public import of `WeilConjectures.AlgebraicGeometry.GroupScheme.Lie.Differential`
  publicly imports that exact recorded Bracket module; its `GrpObj.differential`
  is the map in the signature. The repaired node explicitly cites this owner in the
  sentence explaining Lie equality and adds its id to `stmt_deps`. The current node
  record, full defining signatures and docstrings, the Bracket tangent equivalence,
  and the Differential postcomposition formula were reopened for this repair.

- `def-sc-group-scheme`: `CategoryTheory.GrpObj`, in
  `Mathlib.CategoryTheory.Monoidal.Grp`, together with the detailed group-scheme
  specialization in `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs`.
- `def-weil-finite-type-morphism`: `AlgebraicGeometry.LocallyOfFiniteType`, in
  `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`, and
  `AlgebraicGeometry.QuasiCompact`, in `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`.
- `def-weil-connected-scheme`: Mathlib `ConnectedSpace` in
  `Mathlib.Topology.Connected.Basic` (nonempty preconnected space).
- `def-sc-scheme-tangent-space`: `AlgebraicGeometry.schemeTangentSpace`, its additive
  group and module, and `schemeTangentMap`, in
  `WeilConjectures.AlgebraicGeometry.SchemeTangentSpace`.
- `def-sc-group-scheme-subgroup`: `AlgebraicGeometry.IsSubgroupScheme`,
  `IsClosedSubgroupScheme`, `IsNormalSubgroupScheme`, in
  `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs`.
- `lem-weil-pbc-reduced-induced-closed-subscheme`:
  `AlgebraicGeometry.Scheme.IdealSheafData.reduced_induced_closed_subscheme`, in
  `WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme`; its radical
  affine ideals, reduced closed immersion, support and uniqueness were read.
- `def-weil-field-valued-points`: the hom type in `CategoryTheory.Over`, in
  `Mathlib.CategoryTheory.Comma.Over.Basic`. The monoidal unit is the identity
  L-scheme, so its homs into G are exactly G(L).
- `sk-d-geometry`: its statement and absence of a Lean record were read. Its concrete
  matrix construction is unnecessary to formulate a theorem that applies to every
  algebraic group, including those closed matrix subgroups; see the complement check above.

Other existing constructions used are `GrpObj.identityComponent`,
`GrpObj.identityComponentι`, `GrpObj.onePoint`, and `GrpObj.mulLeft`, all from
`WeilConjectures.AlgebraicGeometry.GroupScheme.Basic`, and `Scheme.Hom.image` /
`imageι` from `Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme`. The full signature and
construction of the identity component were read: it is the open subscheme whose
underlying set is `connectedComponent (GrpObj.onePoint G)`.

Recorded proof modules are imported plainly, including regularity, identity components,
geometric products, groupoid image closure, reduced-source factorization, separatedness,
rational-point density, smooth Lie dimension, identity tangent transport, identity local
dimension and dimension drop. The Mathlib proof leaves' modules are also imported.
The three proof nodes with neither a Lean record nor a Mathlib match (general Cartier,
affine Nullstellensatz, affine constructible-open) have no recorded module to import;
their mathematical steps remain explicit in the proof docstring. The existing Cartier
API is available through GroupScheme.Basic.

Edge cases checked before writing:

- The empty scheme cannot carry a group scheme over a field because it cannot admit
  the required identity section. No extra nonemptiness assumption was added.
- The identity component of a disconnected group is retained; connectedness appears
  only in the closed-subgroup equality criteria.
- Finite groups and the trivial group have zero-dimensional identity component;
  all clauses apply, including the equality criterion in dimension zero.
- The dimension complement also covers GL of a zero-dimensional vector space, which
  is the trivial group. No matrix-size binder or positive-size condition is introduced.
- A nonreduced closed subgroup in characteristic zero is automatically smooth and
  reduced by Cartier; reducedness is not assumed of K.
- Positive characteristic would permit infinitesimal counterexamples (for example
  the trivial subgroup inside alpha_p in dimension zero). The source's characteristic
  zero condition is retained.
- Algebraic closedness is needed for rational coset representatives and point-image
  surjectivity; over R, squaring on the multiplicative group would fail the latter.
- A non-quasi-compact constant infinite group can have a nonclosed homomorphism image;
  both finite-type hypotheses on G are retained.
- The coset assertion quantifies over every point of the scheme, not only closed points.
- All universes and variables are explicitly bound. Objects and coefficients use the
  project's standard single-universe scheme convention; there is no independent smaller
  universe for quantified test algebras or components.

Searches for existing full statements:

- `msearch.py ... leanfinder`: query “A finite type group scheme over an algebraically
  closed field of characteristic zero has finitely many components, normal irreducible
  identity component, closed homomorphism image and equal Lie closed subgroup is equal”.
  Eight results concerned Galois-category automorphism groups and their topology; no match.
- `msearch.py ... loogle 'AlgebraicGeometry.Scheme, "isMonHom"'`: two hits,
  `Scheme.isMonHom_fst_id_right` and an affine-group base-change instance; neither
  states this result.
- `msearch.py ... grep 'isClosed_range_of_isMonHom|isIso_left_of_topologicalKrullDim_eq|identityComponent' AlgebraicGeometry`:
  no Mathlib hits.
- `msearch.py ... leansearch`: query “The image of a morphism of algebraic group schemes
  is a closed subgroup scheme”. Eight hits for scheme image constructions and immersion
  lemmas; none gives this group-scheme bundle.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf`, for the blueprint id and component,
  normality, closed-image and Lie-differential names, located the existing general
  GroupScheme.Basic declarations and matrix-group specializations. Their signatures
  were opened. Basic already gives finiteness, the identity component and dimension
  criterion; its closed-image theorem states only closedness of the underlying range,
  and GroupScheme.Image assumes a proper source. Neither gives this full bundle,
  particularly the general reduced subgroup image with exact L-point range and the
  connected equal-inclusion-differential criterion. All existing notions are reused.
- `rg 'algebraicGroup_geometry'` in Mathlib and both project Lean roots: no collision.

The only statement-text change is the reviewer-requested missing citation, recorded below.
There are no new nodes, dependency modules, mathematical corrections, or disputes.

## Second reading by Q48

A second pass by this same worker reopened the node and the module; no additional agent
was started, as the dispatcher's brief prohibits it. The maintainer's independent review
remains the independent reading of this delivery; this paragraph does not claim a second
person or agent performed it.

The pass checked each row above against the actual signature. In particular the ambient
field is algebraically closed and characteristic zero; G and H both have the two finite
type hypotheses; connectedness is confined to the last conjunct; K has no extra smooth,
reduced or finite-type assumption; the coset quantifier covers every scheme point; the
normality predicate is the all-algebra-points predicate; and both image ranges are in the
same H(L) hom type. The canonical image's reducedness and support identify it with the
specified reduced induced closed subgroup, rather than merely asserting a closed set.
The inclusion differential, not an arbitrary Lie-space equivalence, is required. The two
complements follow directly from the corresponding general clauses. The initial compile
found an underdetermined source for `Over.homMk`; both occurrences now explicitly name
`U := Over.mk (f.left.imageι ≫ H.hom)`. No mathematical statement changed.


## Repair of returned delivery 5767f2c88869

H2: repaired by adding `def-wf-lie-algebra-derivation` to the item's `stmt_deps`
and citing it in the sentence explaining that Lie(K) = Lie(G) means bijectivity of
that inclusion differential. The existing Lean file and its signature are unchanged.
The missing dependency has a usable current upstream record and is already exposed
by the existing public import of Lie.Differential, so no new interface is written.
The current main node matches the returned sandbox node outside `lean`; the wrapper
will rebase the repair on current main when building the delivery. Independent review
accepted all mathematical clauses and edge cases; this repair addresses its sole H2
request. The citation edit is documented as a statement change to satisfy the field
checks; it does not alter the blueprint unit's mathematical statement.

## Statement corrected

Old statement: the complete prior text is preserved verbatim in
`statement_change.old_statement`. The only edited sentence was:

> For a closed subgroup scheme $K\hookrightarrow G$ [def-sc-group-scheme-subgroup],
> equality $\operatorname{Lie}(K)=\operatorname{Lie}(G)$ means that the differential of
> this inclusion identifies the two tangent spaces.

That sentence now additionally cites the canonical Lie algebra and differential of
`[def-wf-lie-algebra-derivation]`, whose existing `GrpObj.Lie` and differential are
used in the signature. The prior dependency list omitted the owner of this API.
Source: current blueprint `sk-p-geometry/_section.md`, equal-Lie clause, and the
`sk-d-tangent` definition `def-wf-lie-algebra-derivation`. No mathematical assertion,
hypothesis, conclusion or proof step changes. No citer is edited.

All direct statement/proof citers on current main were read and audited:

- `sk-i-restriction`: holds. Its normality and identity-component uses are unchanged;
  the Lie convention is now explicit and agrees with its own convention.
- `sk-p-comparison`: holds. It applies the same equal-inclusion-differential criterion
  to the closed stabilizer in connected G; the citation now names its Lie API.
- `sk-p-product`: holds. Its multiplication-image and equal-Lie uses apply the same
  clauses; adding the owner citation changes neither result.

Repair second reading: reopened the current item, added dependency's recorded module,
and unchanged Lean signature. Verified that `Function.Bijective (GrpObj.differential i)`
is now covered by the new text citation and `stmt_deps` entry, and that the public
Lie.Differential import publicly imports the recorded Lie.Bracket module. No duplicate
construction or extra hypothesis was introduced. Every original clause correspondence
in the table above still applies.
