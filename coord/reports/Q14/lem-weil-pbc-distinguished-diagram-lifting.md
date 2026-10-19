## Worker report

The module `Sheaf.Paper.PbcDistinguishedDiagramLifting` states
`AlgebraicGeometry.Scheme.pbcDistinguishedDiagramLifting`, with one postponed proof in the item module.
Its other declarations are real data definitions encoding the finite input language
and its evaluations using the existing coefficient system. A dependency compilation
repair is described below. No mathematical node statement or data definition changes. The syntax helpers
belong to this simultaneous-lifting interface, under the owning-node helper permission.

Clause-by-clause translation:

- The prime is `(l : ℕ) [Fact l.Prime]`; the fixed algebraic closure is
  `(Ω : Type c) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]`.
- The scheme is `T : Scheme.{u}` with `[IsNoetherian T]`, `hDim` recording a finite
  topological Krull dimension, and `hInv` recording invertibility of l in every stalk.
  `Fact` packages these same hypotheses for the existing common-cone API. There is no
  universe equality between scheme and coefficient field; both are explicitly bound.
- `X : A → PbcFiniteStagePairCategory ...`, `[Finite A]`, gives the specified vertices.
  A `Vertex A` is an index and a natural number of applications of [1]. Its pair value
  is literally `(E_X, K_X[1]...[1])`, via `pbcDiagramVertex`; its pair shift comparison
  is `Iso.refl`, using the published common-stage shift, not another shift.
- `[Finite B]`, `s t : B → Vertex A`, and `f` give all specified arrows between these
  occurrences. A shared endpoint always refers to the same `X` value. Arrows may have
  the same endpoints and need not be distinct, invertible, or nonzero.
- `Expr` is the typed finite grammar for arrow variables, identities, zero,
  composition, addition, negatives and [1]. `Expr.eval` evaluates exactly these
  operations. In particular its shift clause is `sigma_X.hom ≫ u[1] ≫ sigma_Y.inv`.
  Thus a separately specified shifted arrow can be related to its original arrow
  by a finite equation; derived shifted expressions always use that exact formula.
- `[Finite J]` and `eqs : J → Equation s t` select finitely many parallel expressions.
  `heqs` asserts their actual equality in the pair category. This includes arbitrarily
  nested shifts and arbitrary parentheses; no bound on term length is imposed.
- `[Finite R]` and `rows : R → Row s t` select finitely many rows of terms, with the
  third term ending at the shifted first occurrence. `Row.triangle` is Mathlib's
  `Triangle.mk`. `hrows` is exactly the published `pbcCommonStageDistinguished` of
  each such pair triangle, with no pretriangulation assumed on the pair category.
- `M0 : Padic.FiniteCoefficientFields l Ω` is the prescribed initial intermediate field.
  The conclusion gives `M`, `M0 ≤ M`, and `h : ∀ j, (X j).stage ≤ M`. These fields are
  finite-dimensional intermediate fields, not finite sets.
- The family `u` gives actual raw stage arrow representatives. Its endpoints are
  `pbcDiagramStageVertex ... x = T_(M/E_X)(K_X[1]...[1])`. No stage object is chosen
  separately, and the same lift is used at every occurrence.
- The first conjunct recovers each finite expression (hence each arrow slot) by
  `PairCategory.mkHom M ... = Expr.eval ... f`. This also says that every composite,
  identity, sum, negative, zero, and repeated shifted arrow has the specified class.
- The second conjunct is every selected equation evaluated in the raw stage at M.
- The third conjunct says every selected corrected stage triangle belongs to the
  recorded `distTriang (pbcStageCategory ... M)`. `Row.triangle` composes its raw
  third arrow with `(pbcDiagramStageShift ... first).hom`; in the unshifted row
  this is precisely `p_M ≫ sigma_(M/E_X,K_X)`, that is sigma composed with p_M in
  the node's usual right-to-left convention. This is not a bare arbitrary row lift.
- `pbcDiagramStageShift` uses the existing transition's `commShiftIso 1`, which is
  the prescribed sigma. `pbcDiagramIteratedSigma` explicitly iterates it to identify
  the raw lift of K_X[n] with the iterated shift of X_M. Nothing assumes sigma is
  identity at distinct fields. For every shift expression, its normalized map is
  the shift of its lifted map by the evaluator's conjugation formula.
- The fourth conjunct is recovery through the canonical `isoToStage` vertex maps:
  rho_X followed by j_M of the representative equals the original term followed
  by rho_Y. `pbcDiagramVertexIso` reuses `StageSystem.isoToStage`; its representatives
  are the prescribed associator components, equal to identity after the normalized
  unit identifications by `pbcScalarSystem_units`. This is the node's identity
  representative convention. The shift comparisons also recover the last arrows
  of triangle rows; no arbitrary vertex isomorphisms enter the theorem.
- The final conjunct explicitly gives a triangle isomorphism from each original row
  to the image of its corrected stage row. Its three component arrows are required
  to be precisely these canonical vertex maps, so recovery also includes the shifted
  last-arrow square, not just an unspecified isomorphism class.

Dependencies read and used:

- `Sheaf.Paper.FiniteStagePairCategory`: `PbcFiniteStagePairCategory`,
  `pbcStageCategory`, `pbcScalarSystem`, its normalized `pbcScalarExtension`,
  `pbcScalarAssociator`, and `pbcScalarSystem_units`.
- `WeilConjectures.CategoryTheory.StageSystem.Basic`: `PairCategory.toStage`,
  `PairCategory.mkHom`, `StageSystem.isoToStage`, and the representative recovery
  lemma `mkHom_eq_isoToStage`. The source was read from the current published side
  source (also confirmed using `scompile.py --source`).
- `Sheaf.Paper.CommonStageCalculus`: `commonStageCalculus`, the published
  `pbcRationalHasShift`, `pbcScalarCommShift`, `pbcScalarAssociatorCommShift`,
  `pbcPairHasShift`, `pbcStageInclusionCommShift`, finite-graph representation and
  finite-equality detection. Their actual signatures and docstrings were read.
- `Sheaf.Paper.PbcCommonStageCones`: `pbcCommonStageDistinguished`,
  `qbarStagePretriangulated`, and its unique integral-image normalization.
- `Sheaf.CategoryTheory.StageSystemCommonStageCones`:
  `StageSystem.CommonStageDistinguished` and `commonStageCone`, read in full.
- Mathlib `CategoryTheory.Triangulated.Basic`: `Pretriangulated.Triangle`,
  `Triangle.mk`, `TriangleMorphism`, and triangle isomorphisms; Mathlib
  `CategoryTheory.Triangulated.Pretriangulated`: `Pretriangulated` and `distTriang`.
  The node's Mathlib leaves intentionally need no private Lean record.
- `Sheaf.Paper.PbcRationalCategory`: `PbcRationalDerivedCategory` and its actual
  raw `PbcRationalCategory`, retained without a Karoubi completion.
- `Sheaf.CategoryTheory.ScalarLocalizationTriangulated`:
  `ScalarLocalization.exists_triangulated_scalarLocalization`, the exact
  integral-image triangulation used by the common-cone dependency.
- `Sheaf.Paper.PbcScalarExtension`: `pbcCoherentScalarExtension` and the exact
  coherent tensor comparisons, imported as proof input. The concrete pair system
  and its sigma are taken from its published owning interfaces above, rather than
  replaced with arbitrary functors. The source proof's six steps are reproduced
  in the theorem docstring. The downstream pair Verdier theorem is not imported.

Edge cases checked before writing: all four finite families can be empty; empty
vertices force arrow, equation and row data to be empty, but M0 still supplies a
stage. With no selected rows this is ordinary simultaneous finite-equation lifting.
Zero objects, zero arrows and identity arrows are allowed by the grammar. Parallel
arrows are separate slots; repeated endpoints and triangles sharing vertices use
one fixed scalar extension. An object occurring both unshifted and shifted uses
its same base index, so its raw lifted shift is corrected by sigma, with repeated
shifts using the recursive iterated comparison. A row and its signed rotation are
expressible, including the negative shifted first arrow. Triangle isomorphisms and
their inverse identities are finite arrow/equation data, so the statement serves
TR3 as well as TR2 and TR4. M can equal M0 or a vertex field; no strict inclusion
or faithful transition hypothesis is imposed. The empty scheme is allowed: no selected point or nonemptiness assumption is
needed, and the stalk invertibility hypothesis is then vacuous as in the source.
No edge case suggests a dispute.

Searches for an existing statement or notation:

1. `msearch.py ... leanfinder` with "A finite diagram of distinguished triangles
   and equations in a filtered common-stage category lifts to one finite coefficient
   field": eight hits, including `CategoryTheory.IsFiltered.sup_exists`, individual
   triangle results, and T-structure lemmas. None lifts distinguished rows and the
   prescribed shifted equations in this coefficient pair category.
2. `msearch.py ... loogle` with
   `CategoryTheory.Pretriangulated.Triangle, CategoryTheory.StageSystem`: no hits;
   Loogle reports the project-local StageSystem name is unknown to its index.
3. `msearch.py ... grep` with
   `StageSystem|CommonStageDistinguished|distinguished.*lifting`, under
   Mathlib CategoryTheory: no hits. The project's own stage system is therefore
   read directly, not inferred from a Mathlib search.
4. `rg` over the upstream project, `lean/Sheaf`, and the DAG for distinguished
   lifting, finite graphs/equalities, common-stage distinguishedness, and expression
   syntax. Existing common-stage calculus only lifts ordinary diagrams/equalities;
   the cone module defines individual distinguishedness. No declaration of the
   simultaneous distinguished-row assertion or its typed expression helpers was
   found. The exact node-id grep in upstream source found no match. The source-name
   index likewise gives no declaration for this item. Generic filtered diagrams,
   cone independence and the downstream Verdier theorem have different statements.

Validation: the required single-file `scompile.py` wrapper is used; its final result
and the delivery preflight are recorded below after completion. Every theorem proof
in this delivery is `sorry`. The item has one theorem. The dependency module retains
its existing named statements and postpones three adapter proofs under their same existing
names and Prop signatures. No new DAG nodes or statement corrections are needed.

## Dependency modules

`prop-weil-pbc-scalar-extension`: the recorded `Sheaf.Paper.PbcScalarExtension`
module repeatedly exceeded the 60-second compiler limit, both as an import and on
server confirmation. A diagnostic run with a reduced 20,000-heartbeat limit
isolated the nested chosen-witness conversion in `pbcScalarRationalIsTriangulated`.
The sandbox copy retains all data definitions, all categories and their selected
structures, all scalar-extension functors, and every comparison unchanged. It
replaces the expensive proof projections in the three Prop-valued adapters
`pbcScalarRationalZero`, `pbcScalarRationalShiftAdditive` and
`pbcScalarRationalIsTriangulated` with explicit `@[instance] theorem` declarations
of the identical names and types and `sorry` proofs, as appropriate at stage 2.
Their expanded docstrings give the full proofs: project the zero-object proposition,
additive-shift laws and TR4 from the same `pbcRationalTriangulationData` witness; the other adapters are the identical
zero, shift, additive-shift and pretriangulation projections, and proof irrelevance
identifies the remaining Prop arguments. This is a proof postponement, not a data
choice or replacement triangulation. The node changes only in `lean`, with the
required note. Compilation of the dependency and this consumer is requested together
in dependency order, including both sandbox and actual module-path checks.

The adapter theorem binders explicitly retain the original prime, coefficient-field,
Noetherian, finite-dimension and invertibility hypotheses. They are not left to
section-variable inference, which could omit unused geometric proofs in a `sorry`
body. The combined compilation passed all overlay, preliminary, sandbox and actual
module-path checks without errors or unexpected warnings before this explicit-binder
review adjustment; the final delivery dry run checks that adjustment as well.

Final validation: the final explicit-binder version and this consumer both compiled
cleanly in dependency order, at both sandbox and actual module paths, through the
required wrapper. `deliver2.py Q14 lem-weil-pbc-distinguished-diagram-lifting --no-push`
printed `OK (dry run)` for commit `d7f6e82be0`: server preflight and all compilation
checks passed. The submitted record changes are exactly the two `lean` fields;
the dependency source delta is exactly the three named Prop proof postponements
and their proof docstrings and explicit original binders.

## Second reading by Q14

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
