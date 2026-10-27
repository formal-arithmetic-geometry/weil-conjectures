## Worker report

The module `Sheaf.AlgebraicGeometry.LinearGroupSchemes` completes the definition node without
redefining the existing general linear scheme. Its main declaration is
`AlgebraicGeometry.LinearGroupSchemes.specialLinear`. The node's natural-language statement,
statement dependencies and proof are unchanged. No new or dependency node is needed.

Sources read: the entire node and its eight proof steps; the current blueprint at
`literature/blueprint/latest/blueprint/sec-smooth-purity/sk-prop-an/def-sc-general-linear-group.md`;
Stacks `groupoids.tex`, examples `example-general-linear-group` (022W) and
`example-determinant` (022X); the recorded dependency definitions and their source signatures.
The CompactObject example module has now been withdrawn; its node records the upstream
replacement, so the module-mode/header conventions of the standing brief were followed.

### Hypothesis and clause correspondence

- A field k: `(k : Type u) [Field k]`. All test algebras are `(R : Type u) [CommRing R]
  [Algebra k R]`; none is assumed reduced, nonzero or a field. This follows the common-universe
  convention of the recorded group-scheme dependency. The finite index set is
  `Index.{u} c := ULift.{u} (Fin c)`, canonically the c indices in the field's universe. No
  universe equality beyond that existing API is imposed. For test algebras in a larger universe
  one uses the same lifted base field and the canonical scalar transport.
- c >= 1: every positive c is admitted. The constructions are defined uniformly for `c : ℕ`
  and extend canonically to the empty matrix; no positive rank or field characteristic is
  excluded. The signed-minor statement uses `c = d+1`, covering exactly positive ranks.
- The polynomial algebra P and generic matrix X are the existing
  `MvPolynomial (Index c × Index c) k` and
  `Matrix.GeneralLinearGroup.genericMatrix (Index c) k`; the latter is `Matrix.mvPolynomialX`.
- D is `Matrix.det` of this generic matrix. Its existing `Matrix.det_apply` is the
  column-indexed Leibniz formula. Reindexing permutations by inverse gives the node's
  row-indexed formula: the sign is unchanged and the factors are permuted.
- A=P[1/D] is the existing `Matrix.GeneralLinearGroup.CoordinateRing (Index c) k`, defined
  literally as `Localization.Away` of this determinant. The algebra map is Mathlib's
  `algebraMap`; the inverse denominator is `IsLocalization.Away.invSelf`.
- GL is the existing `AlgebraicGeometry.GeneralLinearGroup (Index c) k`, literally Spec A
  over Spec k, with its upstream `GrpObj` instance from the coordinate Hopf algebra.
  There is no second scheme definition or second GL group structure in this delivery.
- Comultiplication is the existing `Matrix.GeneralLinearGroup.comulAlgHom`, with
  `comulAlgHom_coord` sending x_ij to `∑ r, coord i r ⊗ₜ[k] coord r j`. The tensor is Mathlib's
  commutative algebra tensor product, with the dependency's `includeLeft`, `includeRight`,
  `productMap` and `ext` universal property.
- Counit is upstream `counitAlgHom` and `counitAlgHom_coord`, whose value is the (i,j) entry
  of the identity matrix, hence the Kronecker delta.
- Antipode is upstream `antipodeAlgHom`, evaluation at the inverse generic matrix.
  The new `generalAntipode_minor` states its precise signed, transposed-minor formula.
  `j.succAbove` deletes row j and `i.succAbove` deletes column i. Zero-based indices change
  i+j by two from the paper's indices and hence do not change the sign. Its minor is a
  `Fin d` square matrix; at d=0 its determinant is 1.
- Values on D inverse are forced by the existing localization lift and its uniqueness
  (`IsLocalization.ringHom_ext` / the upstream `algHom_ext`); they are not arbitrary data.
- GL points, as groups, are upstream `GeneralLinearGroup.homMulEquiv`; their coordinates
  are identified by `homMulEquiv_mapMulEquiv` and the coordinate-ring `algHomMulEquiv`.
  Naturality is upstream `homMulEquiv_specMap_comp`. Matrix multiplication, identity and
  inverse are the existing `Matrix.GeneralLinearGroup` operations, not merely a bijection
  of carriers.
- SL has exactly the specified polynomial quotient: `specialIdeal` is
  `Ideal.span {D-1}`, `SpecialAlgebra` is P modulo that ideal, and `specialLinear` is its
  `StandardGroupSchemes.affine` spectrum over k. `specialMatrix` consists of the residues.
  Its multiplication, counit and antipode are real `Ideal.Quotient.liftₐ` constructions in
  `specialComul`, `specialCounit` and `specialAntipode`; the latter uses adjugate since D=1.
  `specialRelations` states precisely the ideal-killing proofs needed by those definitions.
- `specialGroup_existsUnique` fixes the identity, multiplication and inverse scheme maps
  using the recorded `StandardGroupSchemes.identitySection`, `.multiplication` and `.map`.
  The instance `specialGroup` uses this unique specification. It is not a group structure
  selected from an unspecified existence assertion.
- The canonical A-to-P/(D-1) map is `specialQuotient`, the localization lift of the actual
  polynomial quotient homomorphism, justified by `specialDet_isUnit`. The inclusion is
  its contravariant affine spectrum `inclusion`. `inclusion_specification` states both
  `IsClosedSubgroupScheme` (hence closed immersion), surjectivity of the coordinate map,
  its values x_ij to their residue classes, and D inverse to 1. The subgroup and closed
  immersion predicates are exactly the recorded dependency declarations.
- SL points are the existing determinant-one matrix group `Matrix.SpecialLinearGroup`.
  `specialPoints_existsUnique` specifies the group equivalence by its compatibility with
  the fixed inclusion and `Matrix.SpecialLinearGroup.toGL`; this specifies the matrix
  entries and determines the equivalence uniquely. `specialPoints` takes that unique
  equivalence, and `specialPoints_natural` states naturality for every algebra homomorphism.
- The target of the determinant morphism is exactly the recorded
  `StandardGroupSchemes.multiplicative k`, not another model of G_m.
  `determinantCoordinates` is actual Laurent evaluation at the determinant unit of the
  upstream generic invertible matrix, with coefficient compatibility supplied by
  `determinant_commutes`. `determinant` is its contravariant spectrum map.
  `determinant_specification` states it is `IsMonHom` and that `LaurentPolynomial.T 1`
  maps to D in A. Thus its value at every matrix point is that matrix's determinant.

### Dependency declarations read and used

- `Mathlib.Algebra.Field.Defs`: `Field`.
- `Mathlib.Algebra.MvPolynomial.Basic` and `.Eval`: `MvPolynomial`, `MvPolynomial.aeval`,
  `MvPolynomial.algHom_ext`.
- `Mathlib.LinearAlgebra.Matrix.Defs`, `.Determinant.Basic`, `.Adjugate`: `Matrix`,
  `Matrix.det`, `Matrix.det_apply`, `Matrix.adjugate`, `Matrix.mul_adjugate`,
  `Matrix.adjugate_mul`, `Matrix.adjugate_fin_succ_eq_det_submatrix`.
- `Mathlib.GroupTheory.MonoidLocalization.Away` and
  `Mathlib.RingTheory.Localization.Away.Basic`: `Localization.Away`,
  `IsLocalization.Away.invSelf`, `IsLocalization.Away.liftAlgHom`.
- `Mathlib.AlgebraicGeometry.Scheme` and `.GammaSpecAdjunction`: `Spec`, `Spec.map`,
  `Spec.homEquiv`.
- `Mathlib.CategoryTheory.Monoidal.Grp` and `.Mon`: `GrpObj`, `IsMonHom` and the scoped
  group structures on point Hom sets.
- `Mathlib.RingTheory.TensorProduct.Basic` and `.Maps`: `Algebra.TensorProduct` algebra
  structure, `includeLeft`, `includeRight`, `productMap`, `ext`.
- `Mathlib.Algebra.Algebra.Hom`, `Mathlib.RingTheory.Ideal.Quotient.Operations`:
  `AlgHom`, `Ideal.Quotient.algebra`, `Ideal.Quotient.mkₐ`, `Ideal.Quotient.liftₐ`.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`;
  `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs`: `IsSubgroupScheme`,
  `IsClosedSubgroupScheme`, the exact recorded subgroup interface.
- `Sheaf.AlgebraicGeometry.StandardGroupSchemes`: `affine`, `map`, `multiplication`,
  `identitySection`, `multiplicative`, `multiplicativeGroup`.
- `WeilConjectures.AlgebraicGeometry.GroupScheme.GeneralLinear`: `GeneralLinearGroup`,
  its `GrpObj` instance, `GeneralLinearGroup.homMulEquiv`,
  `GeneralLinearGroup.homMulEquiv_specMap_comp`.
- `WeilConjectures.RingTheory.HopfAlgebra.GeneralLinearGroup`: the coordinate ring,
  generic matrix and invertible matrix, coordinate functions, all three Hopf maps,
  their coordinate formulas and `algHomMulEquiv`.
- Proof-only import `WeilConjectures.LinearAlgebra.Matrix.CauchyBinet` supplies the
  recorded `Matrix.cauchy_binet`; the remaining recorded proof dependencies are in the
  public imported closure. No additional proof dependency imports are missing.

### Edge cases and data audit

At c=1, the inverse formula uses the empty determinant 1, SL has coordinate quotient
k[x]/(x-1), GL is the one-variable localization, and the determinant is the coordinate
map to G_m. At c=2, the signed transposed minors give [[d,-b],[-c,a]]/det, confirming both
the transpose and sign. In characteristic 2 the same signs reduce appropriately. At
rank zero the uniform auxiliary constructions give determinant 1 and trivial matrix
groups, a consistent extension beyond the positive-rank node. No division by c and no
restriction on characteristic is used. The zero test algebra and algebras with nilpotents
are admitted: the polynomial quotient condition is det=1 over the whole algebra, not
only over geometric points. All universes and variables are bound, and no file-local
notation, private definition or local instance is introduced.

Every definition has explicit data. All nine postponed theorems are named and listed in
`lean.declarations`, with their source and the corresponding part of this definition
node's eight-step proof in their docstrings. The selected group structure and point
equivalence are fixed uniquely by the stated canonical maps. There is no hollow choice,
no definition containing `sorry`, and no new theorem proof in this stage-2 delivery.
No node fault, source correction or STATEMENT-DISPUTED issue was found.

### Searches

All searches below were performed for Q54/def-sc-general-linear-group with `msearch.py`:

- LeanFinder: "general and special linear group schemes Spec polynomial ring localization
  determinant quotient determinant minus one". Eight hits, headed by the matrix group
  `Matrix.SpecialLinearGroup`; none gives the special-linear quotient scheme.
- Loogle: "AlgebraicGeometry.GL, AlgebraicGeometry.SL, Matrix.GeneralLinearGroup".
  No hits; the first expected short identifier is unknown.
- LeanSearch: "special linear group scheme quotient determinant one". Eight hits,
  including `Matrix.SpecialLinearGroup`, its determinant-one results, `toGL` range facts
  and the linear-transformation group `SpecialLinearGroup`; no scheme construction.
- Mathlib grep: "specialLinear|SpecialLinear|generalLinear|GeneralLinear" in
  `AlgebraicGeometry`: zero hits. Matrix group declarations were read in their actual
  `LinearAlgebra/Matrix` source files.
- Project rg on the same alternatives in `lean/WeilConjectures/AlgebraicGeometry` and
  `lean/Sheaf/AlgebraicGeometry`, plus an exact node-id search in `lean/WeilConjectures`:
  upstream GL is implemented, and many consumers use it; no SL scheme was found.
  The only item-id mention is a consumer comment in TorusRegularSemisimpleElement.
- `dag/lean_names_upstream.json` search confirmed upstream GL/Lie and determinant-line
  material. Follow-up source search read `GeneralLinearGroup/Regular.lean`: its detGL
  is a matrix-group homomorphism to GL_1, not the scheme map to the recorded Laurent G_m.
  No duplicate of the new SL scheme or that specific scheme map was found.

### Validation

`scompile.py Q54 def-sc-general-linear-group` compiles the module cleanly in module mode,
both as a sandbox file and at its actual library path. The only first-pass issues were
explicit algebra arguments for the affine-map helper and the required `MonObj` point-group
scope; both were repaired. No extra hypotheses or statement changes were needed.

## Second reading by Q54

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
