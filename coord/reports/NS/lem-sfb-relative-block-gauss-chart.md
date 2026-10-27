## Worker report

Stage 2, NS, item `lem-sfb-relative-block-gauss-chart`.
Module: `Sheaf.AlgebraicGeometry.RelativeBlockGaussChart`.
Main declaration: `AlgebraicGeometry.RelativeBlockGauss.relative_block_gauss_chart`.

The inherited BLOCKED ending concerned stage 1. The current node has no Lean
record and is queued for stage 2. The 2026-10-22 stage handoff at the beginning
of `coord/brief-stage2.md` explicitly authorizes this formalization without
reopening the accepted split. No statement correction or split change is made.
Only the item's `lean` record changes.

All new definitions are concrete helpers of the chart in this one module.
There is one postponed theorem, containing the clauses of this node; there are
no helper axioms, no arbitrary choices, and no data supplied by a sorry.
The source is the agent generalization recorded in the node, supporting Milne,
Algebraic Groups (2017), §23h, (152)–(153), printed pp.510–511. I read the local
PDF at that place and the complete eight-step node proof. Milne supplies the
lattice block setting; the node explicitly supplies the arbitrary-ring proof.

Clause-by-clause correspondence (names below are in `AlgebraicGeometry.RelativeBlockGauss`):

| Node hypothesis or clause | Lean rendering |
| --- | --- |
| A any commutative ring | `(A : Type u) [CommRing A]`; no Field, domain or Nontrivial assumption |
| s ≥ 0 | `{s : ℕ}` |
| positive r_1,...,r_s | `(r : Fin s → ℕ)` and `hr : ∀ i : Fin s, 0 < r i` |
| E = direct sum of A^{r_i} | `Index r = Σ i : Fin s, ULift (Fin (r i))` is exactly the concatenated standard basis of this free module |
| GL_E, polynomial coordinates with determinant inverted | The existing `GeneralLinearGroup (Index r) A` and `Matrix.GeneralLinearGroup.CoordinateRing (Index r) A` are used verbatim; the latter is `Localization.Away (genericMatrix ...).det` |
| Lower unitriangular L | `factor A r 0`; `constrained r 0 i j` means row-block ≤ column-block, so these entries equal the full identity matrix; lower off-diagonal blocks are free |
| Upper unitriangular U | `factor A r 2`; constraints are row-block ≥ column-block, so diagonal blocks are identities and lower blocks zero |
| Closed subschemes of GL | `factorIdeal` is the span of the prescribed coordinate-minus-identity entries in GL coordinates; `factorι` is Spec of the quotient homomorphism. The first conclusion asserts `IsClosedImmersion` |
| D = product of block GL, embedded diagonally | `factor A r 1` kills exactly the off-block entries. The witness `d : factor A r 1 ≅ diagonalProduct A r` identifies it with `∏ᶜ i, GeneralLinearGroup (ULift (Fin (r i))) A`; its equation says the inclusion is the actual `Matrix.blockDiagonal'` of those points |
| Leading block determinant Δ_j | `leadingMinor r g j = (g.toSquareBlockProp fun a ↦ a.1 ≤ j).det`; Fin's index 0 is the first, nonempty block |
| V principal open at product of minors | `minors A r` is the product of leading determinants of the generic invertible matrix; `cell` is Spec of `Localization.Away (minors A r)` and `cellι` is induced by localization |
| Meaning as open subscheme | `IsOpenImmersion (cellι A r).left` and the exact range equality with `PrimeSpectrum.basicOpen (minors A r)` |
| Its points over every A-algebra | The next clause is `∃ y, cellPoint ... y = g ↔ ∀ j, IsUnit (leadingMinor r g.val j)` for every commutative A-algebra B |
| L ×_A D ×_A U | `factors` is the threefold categorical product in `Over (Spec A)`. Products in this category are the specified scheme fibre products, canonically associated as a threefold product |
| Isomorphism of A-schemes | `e : factors A r ≅ cell A r` is an isomorphism in that same Over category |
| Multiplication (l,d,u) ↦ ldu | `IsMultiplication A r e` says on every B-valued product point that the matrix of `x ≫ e.hom` is `productPoint ... x 0 * productPoint ... x 1 * productPoint ... x 2` |
| Inverse gives unique factors | The `∃! x` clause specifies the unique product-valued point whose product is the given matrix; `inverseFactor ... e B y t` is concretely the t-th projection of `y ≫ e.inv`, included into GL |
| Functoriality over all A-algebras | The ψ clause is an equality of `inverseFactor` after precomposition with Spec ψ and `Matrix.GeneralLinearGroup.map ψ.toRingHom` of the original factor |
| Arbitrary change of base ring | The A' clause compares any multiplication chart over A' with e on every common test algebra B. Equal underlying matrices give equal inverse factors. In particular, for A→A' and an A'-algebra B this is precisely the canonical base-change square; it makes no flatness assumption |
| Block diagonal conjugation | For every diagonal-factor point h, cell points y,z related by h-conjugation have every inverse factor related by the same conjugation. `IsMultiplication` also gives the forward equality by associativity |
| s=0, product of minors 1 | The final implication asserts `minors A r = 1` and that each factor and the cell is isomorphic over A to `Over.mk (𝟙 (Spec A))`; their product is consequently the same terminal A-scheme |
| Zero ring and nonreduced algebras | No `Nontrivial`, reducedness or characteristic hypothesis occurs anywhere |

The point formulations of the compatibility clauses do not mean field-point
compatibility: they quantify over every commutative test algebra B, including
universal coordinate rings. Thus they determine the scheme morphisms themselves.
For base change, the canonical identification is the one preserving all matrix
coordinates. Tensor-product, quotient and localization universal properties
identify the base changes of the displayed coordinate algebras with their A'
versions. On these identifications the forward map has the same entrywise
multiplication formula, and the A' clause identifies the inverses. This includes
nonflat maps and the map to the zero ring. The theorem for A' supplies existence
of the comparison multiplication chart; the clause is not assuming an unproved
base-change isomorphism as a premise.

The algebraic test universe is the same u as A, matching the existing upstream
GL equivalence. All finite indices are lifted to u explicitly. Every universe
and variable is bound; there are no auto-bound implicit parameters, local
instances, private definitions, or file-local notation.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Spec`, `Spec.map`.
- `Mathlib.LinearAlgebra.Matrix.Determinant.Basic`: `Matrix.det`, including its empty-index convention.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`, `pullback.fst`, `pullback.snd`, `pullback.lift`; via the standard limits in Over, the threefold product is the fibre product over A. `Mathlib.AlgebraicGeometry.Pullbacks` supplies scheme limits and the affine tensor-product description.
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `AlgebraicGeometry.IsOpenImmersion`.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `AlgebraicGeometry.IsClosedImmersion`.
- Existing upstream `WeilConjectures.AlgebraicGeometry.GroupScheme.GeneralLinear`: `GeneralLinearGroup`, `GeneralLinearGroup.homMulEquiv`, whose full signatures and naturality theorem were read. These require a commutative ring, not a field.
- Existing upstream `WeilConjectures.RingTheory.HopfAlgebra.GeneralLinearGroup`: `Matrix.GeneralLinearGroup.CoordinateRing`, `coord`, `genericUnit`, and the polynomial/localization construction; read the definitions and their docstrings.
- The recorded proof-dependency modules are imported privately: MvPolynomial.Basic, Matrix.Adjugate, Matrix.SchurComplement, TensorProduct.Basic and Maps, Localization.Defs, ResidueField and AffineScheme. The remaining proof dependency modules are already public statement imports. Schur factorization and determinant signatures were read, including their absence of a Nontrivial hypothesis.

Edge cases checked before and after writing:

- s=0: `Index` is empty, the determinant and empty product are 1, all coordinate algebras are A, and the unique empty invertible matrix gives the stated terminal schemes.
- s=1: both unitriangular factors are identities, D is GL_{r_0}, and the cell is all of GL because its only leading minor is the determinant already inverted.
- Zero A or zero B: the code requires no distinctness of 0 and 1; the unique zero matrix is the identity and is invertible in the zero matrix ring. No excluded field-point convention is present.
- Nonreduced B, e.g. Z/4: the cell condition is `IsUnit`, not nonvanishing; a nonzero nonunit minor is excluded. All constraints are coordinate ideals rather than just set-theoretic field loci.
- Conjugation: diagonal identity blocks remain identities even for nonscalar h_i; off-diagonal zero blocks remain zero; every leading minor is unchanged.
- The leading-block predicate is ≤ j, so the first minor includes the first block and the last includes the full matrix. There is no off-by-one omission.
- Base change uses common test algebras, so both identities and arbitrary maps, including nonflat ones and maps to the zero ring, are covered.

Searches for existing statements and notions:

- `msearch.py ... leanfinder "Block Gauss decomposition of general linear group scheme over a commutative ring as lower unitriangular times block diagonal times upper unitriangular on open set of invertible leading principal minors"`: eight results, including two-block Schur identities, triangular inverses and field transvection elimination; no scheme-level multi-block chart.
- `msearch.py ... loogle "Matrix.fromBlocks_eq_of_invertible₁₁, Matrix.det_fromBlocks₁₁"`: zero results for the combined name query; I independently opened both declarations in the source rather than relying on the empty combined-name search.
- `msearch.py ... grep "gauss|unitriangular|GeneralLinearGroup" AlgebraicGeometry`: zero Mathlib matches.
- `msearch.py ... leansearch "Block Gauss decomposition as an isomorphism of schemes over a commutative ring"`: eight results, notably both Schur identities, `basicOpenIsoSpecAway` and general spectrum isomorphism lemmas; no exact chart.
- `rg` over `lean/WeilConjectures`, `lean/Sheaf`, and `dag/lean_names_upstream.json` for Gauss, unitriangular and block chart names found no chart. Targeted searches for GeneralLinearGroup found the existing arbitrary-base-ring group scheme and coordinate Hopf algebra, which this file reuses.
- Search of DAG node statements for block Gauss, unitriangular and general linear schemes found `lem-sfb-block-gauss-scheme-chart` (field-only, no Lean record) and `def-sc-general-linear-group` (field-specific SL and GL bundle). Its GL object is exactly the upstream declaration reused here; its special-linear declarations are irrelevant. Neither is a second arbitrary-base chart.
- The item id has no occurrence in upstream Lean. No exact declaration exists to record with `existing: true`.

No new independent notion is introduced: the ideals, schemes, projections and
point formula helpers all belong to the chart specified by this item. No new
DAG node or dependency-module repair is necessary. No statement fault or
STATEMENT-DISPUTED issue was found.

Validation: prescribed `scompile.py` compiled the entire module separately in
sandbox and library modes, with no errors or warnings. The first compilation
was 11.0 s / 8.3 s. The final dependency-import version is compiled again before
delivery. The only postponed proof is `relative_block_gauss_chart := by sorry`.

## Second reading by NS

I made a separate clause-by-clause reread of the complete node, concrete
coordinate definitions, and final theorem in this same worker session; the
brief prohibits starting another agent, and the maintainer performs the
independent review after delivery. This section records that reread without
claiming an independent worker was used.

Checked the constraints explicitly: at t=0, ≤ constrains the diagonal and
strictly upper blocks; at t=2, reversed ≤ constrains the diagonal and strictly
lower blocks; at t=1, ≠ constrains only off-block entries. The identity entry is
the full indexed identity matrix, so each diagonal block is the identity, not
merely a scalar matrix. This matches all three schemes.

Checked that D is not silently substituted for an unrelated closed subscheme:
the `d` witness is an actual isomorphism to the product of the existing block GL
schemes, and the blockDiagonal' equation fixes its embedding. Checked that the
cell is the localization of GL coordinates, not of an arbitrary matrix algebra,
and that its open-immersion range and all-algebra unit-minor characterization
are both asserted. Checked all seven conclusions and all four inverse clauses
against the table above. The base-change and conjugation formulations quantify
over arbitrary algebra-valued points, so equality tests retain nilpotents.

Checked the empty family, one block, zero ring, and zero target algebra again;
none are dropped by a typeclass. Verified explicit universes and inspected all
18 helper declarations plus the one theorem. The reread found no statement
mismatch and required no correction; the final edit only made dependency and
proof imports explicit. The accepted stage-1 fields remain unchanged.
