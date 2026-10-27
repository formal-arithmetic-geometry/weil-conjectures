## Worker report

This delivery states `lem-sfb-unipotent-exponential-construction` in
`Sheaf.AlgebraicGeometry.UnipotentExponentialConstruction`. Its helpers and six theorems
jointly render the whole unchanged mathematical statement. Every theorem proof is `sorry`;
every definition has actual data. The only selected data is the vector group's group
structure, selected from unique existence fixing its identity, multiplication and inverse.

The source was read directly in `literature/milne-algebraic-groups_iAG2017.pdf`: 2.6,
printed pp.40--41, and 14.28--14.31, printed pp.287--289. In particular the source constructs
an actual scheme morphism and gives the homomorphism naturality square before 14.32.
This delivery does not assert the isomorphism of 14.32. The local withdrawn compact-object
example was read, followed by its recorded upstream replacement for the actual conventions.

Hypotheses and clauses, in the namespace `AlgebraicGeometry.UnipotentExponential`:

| Node text | Lean rendering |
| --- | --- |
| k is a characteristic-zero field | `{k : Type u} [Field k] [CharZero k]` on every theorem |
| G is a k-group scheme | `G : Over (Spec (.of k))` with `[GrpObj G]` |
| G is affine | `[IsAffine G.left]` |
| G is finite type over k | `[LocallyOfFiniteType G.hom] [QuasiCompact G.hom]` |
| n >= 1 | `{n : ℕ} (hn : 0 < n)` |
| closed group-scheme embedding into U_n | `i : G ⟶ GeneralLinearGroup (ULift (Fin n)) k`, `[IsClosedSubgroupScheme i]`, and `hi : IsUnitriangular i` |
| U_n has upper unitriangular matrices over every algebra | `IsUnitriangular` quantifies over all `R`, ring/algebra structures and `x : points G R`, and requires diagonal 1 and lower entries 0 |
| g is the scheme tangent space at e | the existing `GrpObj.Lie G`, with the existing canonical `GrpObj.lieIdentityTangentEquiv G` to the recorded `schemeTangentSpace`; that equivalence explicitly identifies the identity residue field and restricts scalars to k |
| di is the tangent map in matrices | `GeneralLinearGroup.RationalHom.differential i`, built upstream from `GrpObj.differential` and `lieAlgebraEquivMatrix` |
| same linear equations over R identify R tensor g with tangent matrices | `matrixDifferential i R` is the actual scalar extension of di, evaluated entrywise through the tensor right-unit map; `tangent_description` says it is injective and that its range is exactly the matrices `M` with a point `x` of G over `DualNumber R` whose image is `dualUnit M` |
| those matrices are strictly upper triangular | the last clause of `tangent_description`: every entry with `b ≤ a` is zero |
| g finite-dimensional | first conclusion of `tangent_description`: `FiniteDimensional k (GrpObj.Lie G)` |
| additive vector scheme after choosing a basis of size d | arbitrary `d : ℕ`, `b : Module.Basis (Fin d) k (GrpObj.Lie G)`, and `FiniteVectorGroup.scheme k d`; the new definition node supplies its coordinatewise additive law and representability |
| actual k-scheme morphism exp_G | `construction` gives `∃! E : FiniteVectorGroup.scheme k d ⟶ G, ...` in the over category |
| natural on R-points | `coefficients_natural`, with every `α : R →ₐ[k] S`, the canonical tensor coefficient map `α.toLinearMap.rTensor`, and `points.map` |
| specified finite matrix sum | `IsExponential i b E`: for every R and X, the matrix of `point b R X ≫ E ≫ i` is `∑ r ∈ Finset.range n, ((r.factorial : k)⁻¹) • matrixDifferential i R X ^ r` |
| characterized by this sum | the unique-existence conclusion of `construction` |
| independent of unitriangular embedding | `embedding_independent`: the same E satisfies `IsExponential j b E` for every other closed unitriangular embedding j, of any positive size m; uniqueness then identifies the morphisms |
| another such H, arbitrary group homomorphism f | `hom_natural` repeats the group, affine, finite-type and closed unitriangular hypotheses for H, with `(f : G ⟶ H) [IsMonHom f]` |
| f_R(exp_G X) = exp_H((1 tensor df)X) | conclusion of `hom_natural`, with `(GrpObj.differential f).toLinearMap.baseChange R X`; E and F are the morphisms characterized by their matrix formulas, rather than arbitrary maps |
| commuting matrix images imply exp(X+Y)=exp(X)exp(Y) | `commuting_add`, hypothesis `Commute (matrixDifferential i R X) (matrixDifferential i R Y)`, conclusion using the existing multiplication of `points G R` |
| no invertibility of exp asserted | no inverse, isomorphism, or surjectivity/injectivity of E appears in any conclusion |

A closed GL embedding with upper unitriangular matrices on all algebra-valued points
is exactly a closed U_n embedding: its coordinate map kills every lower coordinate and
diagonal-minus-one relation, so it factors through the closed unitriangular subscheme;
the original closed immersion remains a closed immersion into that subscheme. This uses
the same embedding and the same tangent matrices, not a different notion of unipotence.
No smoothness, reducedness, connectedness, perfectness, algebraic closedness, or
nontriviality of a test algebra is imposed. A chosen basis is a coordinate choice, not an
extra condition on the group: finite-dimensionality is concluded separately, and the
construction is stated for every finite basis. Individual objects/test algebras share
universe u, with ULift only for the finite matrix indices required by the upstream GL.

Dependency declarations read and used:

- `def-weil-field`: Mathlib `Field`.
- `def-sc-group-scheme`: `CategoryTheory.GrpObj`, `IsMonHom` and the induced group of
  morphisms, from Mathlib's monoidal group-object interface through
  `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs`.
- `def-weil-finite-type-morphism`: Mathlib
  `AlgebraicGeometry.LocallyOfFiniteType` and `AlgebraicGeometry.QuasiCompact`.
- `def-weil-closed-immersion` and `def-sc-group-scheme-subgroup`:
  `AlgebraicGeometry.IsClosedImmersion` and
  `AlgebraicGeometry.IsClosedSubgroupScheme`; the latter includes homomorphism,
  point injectivity, and the closed immersion of the underlying scheme map.
- `def-sc-general-linear-group`: the recorded `Sheaf.AlgebraicGeometry.LinearGroupSchemes`
  imports the existing `AlgebraicGeometry.GeneralLinearGroup` and `homMulEquiv` from
  `WeilConjectures.AlgebraicGeometry.GroupScheme.GeneralLinear`; no second GL is defined.
- `def-sc-scheme-tangent-space`: `schemeTangentSpace` in
  `WeilConjectures.AlgebraicGeometry.SchemeTangentSpace`; its full definition uses dual
  numbers of the residue field, the specified closed point, and the base-map equation.
  The added landed dependency `lem-ag-lie-identity-tangent-equiv` records
  `GrpObj.lieIdentityTangentEquiv` in its upstream module. Its exact signature provides
  the canonical k-linear identity-point identification, without smoothness hypotheses.
- The added landed definition dependency `def-wf-lie-algebra-derivation` records the
  existing `GrpObj.Lie` and `lieEquivTangent` in the upstream `GroupScheme.Lie` hierarchy.
  The differential is the existing postcomposition differential, not an arbitrary map.
- `def-sc-dual-numbers`: Mathlib `DualNumber`; `GeneralLinearGroup.dualUnit M`
  is the existing matrix point 1 + epsilon M with inverse 1 - epsilon M.
- `def-weil-pbc-module-tensor-product`: Mathlib `TensorProduct`, `LinearMap.rTensor`,
  and canonical tensor maps. `LinearMap.baseChange` and
  `TensorProduct.AlgebraTensorModule.rid` build the scalar-extended differential entrywise.
- `def-weil-affine-spectrum`, `def-weil-pbc-mv-polynomial-ring`, `def-sc-gm-ga`:
  Mathlib `Spec`, `Spec.map`, `MvPolynomial`, `MvPolynomial.aeval`, and the recorded
  `StandardGroupSchemes.affine`, `map`, `identitySection`, `multiplication`. The vector
  group is built from exactly these objects and coordinate maps.
- Proof imports: `Sheaf.AlgebraicGeometry.RationalRepresentationComoduleDictionary`
  (`RationalRepresentation.dictionary`, finite/trivial/tensor clauses),
  `Sheaf.AlgebraicGeometry.AffineGroupTensorReconstruction`
  (`RationalRepresentation.affineGroup_tensor_reconstruction`), and
  `Mathlib.RingTheory.Nilpotent.Exp` (`IsNilpotent.exp_eq_sum`, `map_exp`,
  `exp_add_of_commute`, and inverse identities). The fixed-vector proof node has no
  recorded Lean module in the read repository; its ID and use are retained in the
  construction's natural-language proof rather than inventing a module import.

Edge checks before writing and again after compilation:

- n=1: there are no strict upper coordinates. The tangent module is zero and the
  characterized exponential is the identity point; the sum has its r=0 identity term.
- d=0 and the trivial group: the polynomial algebra has no variables, the vector scheme
  is Spec k, and all scalar extensions and tuples are zero/empty. No d>0 assumption occurs.
- R the zero ring: all matrices and tuples are unique; no Nontrivial R or CharZero R
  instance is requested. Factorials are inverted in k and mapped to R by scalar action.
- G_a embedded in U_2: the matrix is square-zero and the sum is I+X, agreeing with the
  standard additive parametrization.
- Noncommuting E12,E23 in U_3: `commuting_add` does not apply; its genuine Commute
  hypothesis is retained, so noncommutative multiplication is not incorrectly additive.
- H=G, f=identity, constant identity homomorphisms, and different ambient matrix sizes:
  all occur in `hom_natural` without extra assumptions. Different bases for G and H
  identify their own scalar extensions explicitly through the respective point maps.
- For a general R, reducing the point x in the tangent range clause gives the identity
  after composing with i; injectivity of i on R-points forces its reduction to be the
  identity of G. No missing reduction hypothesis is needed.

Searches (the exact msearch queries/results are also in sandbox searches.jsonl):

1. LeanFinder: “The finite exponential gives a natural morphism from the tangent vector
   scheme of a unipotent algebraic group in characteristic zero into the group”:
   8 hits, including `IsNilpotent.exp`, Lie derivation exponentials and `AffineSpace`;
   none asserts the group-scheme-valued result.
2. Loogle: `"IsNilpotent", "exp"`: 11 hits, supplying the finite ring exponential and
   its identities, not subgroup membership or group-scheme functoriality.
3. msearch grep `unitriangular|unipotent.*exp|exp.*unipotent` in AlgebraicGeometry:
   0 hits. Direct rg in `lean/WeilConjectures` and `lean/Sheaf` found related
   classification/filtration results and the existing Lie/matrix interfaces, no matching
   exponential construction. The required grep for this item ID in WeilConjectures had
   no hits.
4. LeanSearch: “A nilpotent tangent vector of a unipotent group scheme exponentiates
   naturally to a group point”: 8 hits, the finite ring exponential and Lie derivation
   APIs, no matching geometric statement.
5. New vector-scheme searches: LeanSearch on representing scalar extensions (8 hits,
   unrelated additive modules); LeanFinder on the polynomial additive vector scheme
   (8 hits, principally `AffineSpace` and `AffineSpace.SpecIso`); msearch grep
   `vectorScheme|vectorGroup|MvPolynomial.*HopfAlgebra` (0 hits). Direct project/DAG
   searches and blueprint_refs searches found no definition of this additive vector
   scheme with its scalar-extension points. See the new node's mathlib_searches.

No statement correction, disputed statement, or unusable dependency interface was found.
All original node fields are preserved except lean and the authorized addition of the
new vector-scheme node and the two already recorded identity-tangent/Lie dependencies.

## New nodes

`def-sfb-additive-vector-scheme` constructs the additive vector scheme in any finite
basis, following Milne 2.6, printed pp.40--41, and 14.31, printed p.288. It owns
`Sheaf.AlgebraicGeometry.FiniteVectorGroup`. The underlying scheme is the existing
spectrum of the existing polynomial ring; its three explicit coordinate substitutions
give the additive group structure, uniquely. The actual point is evaluation at the
coefficients of the scalar-extended basis, not an unspecified equivalence. The two
postponed named theorems check these structure data and the stated representing/additive/
naturality properties. Their docstrings give the complete proofs. The searches above
and the new node's exact search results distinguish this construction from existing
bare affine space and from the characteristic-zero vector-group classification theorem.
The node cites every bracketed dependency in its statement and is cited directly by the item.
Its blueprint ancestor is null, matching the output of blueprint_refs ancestor on this
indirectly sourced item; its via chain starts with the item and continues the item's chain.

## Second reading by ND

I reopened the unchanged node and both completed files and checked the table above
against their actual signatures. This was a self-review: the dispatcher explicitly
prohibits starting other agents, and the maintainer performs the independent review.
The checks found no mathematical change required. I specifically checked that the
all-algebra tangent image is stated as a conclusion rather than an assumption, that
finite-dimensionality is a conclusion, that the exponential is an over-scheme morphism,
that every formula quantifies over actual tensor vectors, and that homomorphism
naturality uses the canonical differential. I also rechecked the n=1, d=0, R=0 and
noncommuting U_3 cases against the exact formulas. The vector group has actual polynomial
coordinate data and only uniquely characterized chosen structure. All variables and
universes are explicitly bound under autoImplicit false; no file-local notation,
private definition, or file-local instance occurs. The ordinary associative-matrix
LieRing instance is supplied only inside the body of matrixDifferential, whose public
signature is an R-linear map and does not require that local instance from its callers.

Both files compiled with scompile.py on the server without errors or non-sorry warnings
(1.7 s for FiniteVectorGroup and 2.2 s for UnipotentExponentialConstruction in the clean
run). The wrapper's local compiler reported OSError(28), then its prescribed server
fallback succeeded; no launcher file or live library file was edited.
