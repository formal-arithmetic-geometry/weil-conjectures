## Worker report

The module `Sheaf.AlgebraicGeometry.RegularGroupGenericAmpleness` states
`AlgebraicGeometry.regularGroupGenericAmpleness`. Its only theorem has proof `sorry`;
there are no definitions or extra assertions. No statement correction is needed.
The item node changes only in `lean` and by adding five already-landed statement
prerequisites to `stmt_deps`, as authorized by brief §5.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

| Node text | Lean rendering |
| --- | --- |
| A scheme S | `{S : Scheme.{u}}`, with explicitly bound universe `u`. |
| Regular and locally Noetherian | `hS : IsRegularScheme S`; the recorded definition is exactly `IsLocallyNoetherian S ∧ IsRegular S`. |
| A group scheme p:G → S, including multiplication, inverse, identity and group laws | `G : Grp (Over S)`; its structure map is `G.X.hom` and its underlying scheme is `G.X.left`. |
| Commutative | `[IsCommMonObj G.X]`. |
| Smooth | `[Smooth G.X.hom]`. |
| Separated, meaning closed diagonal | `[IsSeparated G.X.hom]`, whose field is `IsClosedImmersion (pullback.diagonal G.X.hom)`. |
| Finite presentation | `[LocallyOfFinitePresentation G.X.hom] [QuasiCompact G.X.hom]`; the required quasi-separatedness follows from the separately supplied separatedness. |
| Geometrically connected fibres | `[GeometricallyConnected G.X.hom]`, Mathlib's geometric fibrewise connectedness, including nonemptiness. |
| Every geometric fibre fits into the stated fppf-exact split-torus/abelian sequence | `hG : HasSemiabelianGeometricFibres G`, the already-landed predicate, not a new hypothesis standing in for an unspecified notion. It quantifies over every algebraically closed field in the scheme universe and every geometric point; the kernel is an actual pullback square and the quotient is fppf locally surjective. |
| r is nonnegative and rank zero is allowed | The reused predicate existentially quantifies `r : ℕ`; it does not impose positivity. |
| A is proper, smooth and geometrically connected | The reused predicate uses `IsAbelianVariety A.X`: proper, smooth, connected over the algebraically closed geometric field. This implies geometric connectedness, as documented in that predicate. |
| Dense open V ⊆ S | `V : S.Opens`, `hV : Dense (V : Set S)`; the open scheme and inclusion are `V.toScheme` and `V.ι`. |
| G_V → V proper, hence abelian | `hproper : IsProper (G.X.hom ∣_ V)`; inherited smoothness, connectedness and group structure give the stated abelian-scheme interpretation, without an extra assumption. |
| An invertible O_G-module L | `L : G.X.left.Modules` and `[L.IsInvertible]`. |
| Symmetric, [-1]*L ≃ L | `symmetry : (Scheme.Modules.tensorPullback ι[G.X].left).obj L ≅ L`; `ι[G.X]` is the inverse of this very group object. |
| Ample over every component's generic point | `hgeneric` quantifies over every `C : Set S` with `C ∈ irreducibleComponents S`, then every `ξ : S` with `IsGenericPoint ξ C`. |
| The actual scheme-theoretic fibre and restricted L | `G.X.hom.fiber ξ` and `(tensorPullback (G.X.hom.fiberι ξ)).obj L`. |
| Ampleness on those fibres | The existing `Scheme.Modules.IsAmple` applied to the preceding module, with its invertibility witness from `invertible_pullback_tensor`. |
| Relatively ample over S, meaning ample on p⁻¹(W) for every affine open W | Conclusion quantifies `∀ W : S.Opens, IsAffineOpen W →` the same absolute `IsAmple` on `(G.X.hom ⁻¹ᵁ W).toScheme` and the tensor restriction along its inclusion. |

The explicit invertibility witnesses merely use the recorded preservation theorem;
they impose no additional assumptions. An input isomorphism for symmetry represents
the existence of such an isomorphism in the usual witness-parametrized theorem form.
No rigidification of L is assumed: the proof obtains it locally along the identity.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Mathlib.AlgebraicGeometry.Noetherian`: `AlgebraicGeometry.IsLocallyNoetherian`.
- `Sheaf.AlgebraicGeometry.IsRegularScheme`: `AlgebraicGeometry.IsRegularScheme`;
  its upstream factor `IsRegular` was read in `WeilConjectures.AlgebraicGeometry.Regular`.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth`.
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`:
  `AlgebraicGeometry.LocallyOfFinitePresentation`.
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `AlgebraicGeometry.IsOpenImmersion`,
  used through canonical inclusions of scheme opens.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `AlgebraicGeometry.IsProper`;
  `Mathlib.AlgebraicGeometry.Morphisms.Separated`: `AlgebraicGeometry.IsSeparated`.
- `WeilConjectures.AlgebraicGeometry.Modules.Invertible`:
  `AlgebraicGeometry.Scheme.Modules.IsInvertible`.
- `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`: public re-export of
  `AlgebraicGeometry.Scheme.Modules.tensorPullback`, constructed by the tensor formula
  in `WeilConjectures.AlgebraicGeometry.TensorPullback`; the recorded normalized
  adjunction and its docstring were also read.
- `WeilConjectures.AlgebraicGeometry.Ample`:
  `AlgebraicGeometry.Scheme.Modules.IsAmple` (absolute ampleness, not a substitute
  very-ample-power predicate).
- Added landed dependency `def-sc-group-scheme`: `Mathlib.CategoryTheory.Monoidal.Grp`,
  `CategoryTheory.Grp`, `GrpObj`, `IsCommMonObj`, and the actual inverse `GrpObj.inv`.
- Added landed dependency `def-sfb-semiabelian-geometric-fibres`:
  `Sheaf.AlgebraicGeometry.SemiabelianGeometricFibres`,
  `AlgebraicGeometry.HasSemiabelianGeometricFibres`.
- Added landed dependency `def-pc-scheme-fibre`: `Mathlib.AlgebraicGeometry.Fiber`,
  `AlgebraicGeometry.Scheme.Hom.fiber` and `fiberι`.
- Added landed dependency `def-pc-geometrically-irreducible`: the connectedness clause
  is `AlgebraicGeometry.GeometricallyConnected`, in the explicitly imported
  `Mathlib.AlgebraicGeometry.Geometrically.Connected`, as the node record's note directs.
- Added landed dependency `lem-weil-pbc-invertible-pullback-tensor`:
  `WeilConjectures.AlgebraicGeometry.Modules.InvertiblePullbackTensor`,
  `AlgebraicGeometry.Scheme.Modules.invertible_pullback_tensor`.

Every already-stated proof dependency is imported privately:
`RegularNormalDecomposition`, `NoetherianFibreAmpleNeighbourhood`,
`SchemeRelativeAmpleAffineCover`, and `RigidifiedLineExtension`, at the module paths
in the node records. The two proof dependencies
`lem-trf-smooth-connected-fibre-normal-integrality` and
`lem-sfb-symmetric-ample-power-extension` presently have no Lean record or Mathlib match,
so there is no module to import for them. They are not required to type this statement.
The module docstring gives all six proof steps and their DAG citations.

Source check: read Deligne's scan at
https://www.numdam.org/item/AST_1985__127__131_0.pdf, pp. 141–144, §§4.1–4.3 and 4.8.
It supplies the symmetric canonical line, reduction to a regular base with dense
smooth open, and the invocation of Raynaud XI 1.13. As the reviewed DAG explicitly
records, the present general group-scheme criterion is an agent-extracted supporting
formulation, rather than the literal stable-Picard proposition. The original Raynaud
reference remains marked locally wanted in the source record; this delivery does not
claim to have read it. The latest blueprint ancestry was checked with
`python3 tools/blueprint_refs.py ancestor lem-sfb-regular-group-generic-ampleness`,
which reports the inherited `from.node = None`.

Edge cases checked before and after writing:

- Empty base: no nonemptiness assumption; the group is then empty. The generic-point
  condition is vacuous and the conclusion is ampleness on the empty inverse images,
  which are compact and have no point requiring a nonvanishing section.
- Reducible or disconnected regular base: all components C and their generic points
  are quantified, not one selected global generic point.
- Locally Noetherian base not quasi-compact: no `CompactSpace S` or `IsNoetherian S`
  is imposed. Quasi-compactness belongs to the finitely presented structure morphism.
- Rank-zero torus and zero-dimensional abelian variety are admitted by the reused
  semiabelian predicate. No positive dimension or characteristic restriction appears.
- Base a field: dense V is the whole nonempty base and the statement reduces to its
  fibre ampleness criterion for the proper group; positive-characteristic fields remain allowed.
- V may be empty when S is empty; W may always be empty, and the conclusion still
  uses the ordinary ampleness predicate with its quasi-compactness clause.
- Universes: `u` is explicit; the geometric tests in the shared predicate range over
  fields in the scheme's own universe, not an independent smaller universe.

Searches for existing declarations, all performed for this item through `msearch.py`
and direct read-only source search:

1. LeanFinder: “A symmetric invertible sheaf on a smooth separated semiabelian group
   scheme over a regular locally Noetherian base is relatively ample if ample on
   generic fibres”. Eight affine-space and scheme-limit hits; no matching theorem.
2. Loogle: `"IsAmple", "Smooth"`. Zero hits.
3. Mathlib grep: `generic.*ample|ample.*generic|Raynaud|IsRelativelyAmple`.
   Four hits: two SGA1 bibliographic references, an order-filter comment, and an
   étale-descent Raynaud–Gruson comment; none gives this criterion.
4. LeanSearch: “A symmetric line bundle on a semiabelian scheme over a regular base
   is relatively ample if it is ample on each generic fibre”. Eight hits on affine
   schemes, finite/proper morphisms, étale terminology and Riemannian symmetry;
   none gives generic ampleness of group-scheme lines.
5. `rg` in `lean/WeilConjectures` and `lean/Sheaf` for semiabelian predicates,
   generic ampleness, relative ampleness and the proposed declaration name found
   the shared semiabelian definition and related line-prolongation statements,
   but no copy of this theorem. The exact blueprint-id search in
   `lean/WeilConjectures` also found none. `dag/lean_names_upstream.json` has no
   `regularGroupGenericAmpleness` name.

Validation: `scompile.py N7 lem-sfb-regular-group-generic-ampleness` compiled both
its sandbox module and final named library module cleanly. The initial notation
collision from naming a variable `η` while opening `MonObj` was repaired by `ξ`.
No warnings other than the permitted sorry warning and no unbound implicits remain.

## Second reading by N7

A separate second pass compared the final file to the full node text and the dependency
signatures, clause by clause as in the table above. This is the dispatcher's single
worker self-check, not a claim that another agent independently reviewed the delivery;
the prompt prohibits starting another agent and assigns the independent delivery review
to the maintainer. The pass verified that symmetry uses the given group inverse, the
semiabelian predicate has the complete exact-sequence content, finite presentation
includes quasi-compactness and inherited quasi-separatedness, all component generic
points occur, and the conclusion uses every affine base open and the same tensor
pullback. It found no semantic discrepancy and required no statement correction,
new notion or dependency-interface replacement. The five existing prerequisite node
ids were added to expose the actual shared declarations used in the signature.
