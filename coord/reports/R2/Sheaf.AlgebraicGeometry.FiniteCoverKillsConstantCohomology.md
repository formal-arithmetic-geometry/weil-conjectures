## What changed

Proved `AlgebraicGeometry.Etale.exists_isFinite_surjective_constant_cohomology_eq_zero`
without changing its signature. The argument follows Stacks 09ZD (2): obtain the integral
surjective cover of part (1), kill the class on its closed base change, approximate by
finite finitely presented schemes, use continuity to obtain a zero at a stage, and deduce
surjectivity of that stage from the factorization of the integral cover.

Two proved private helpers provide the glue. `subsingleton_H_of_isZero_derived_cohomology`
uses the source library's `Functor.homologyRightDerivedFunctorObjSingleFunctorIso`,
Mathlib's `Sheaf.ΓNatIsoSheafSections`, `NatTrans.rightDerived` and its composition rule,
and the existing `Sheaf.cohomology_nonempty_addEquiv_rightDerived_evaluation_succ`.
The degree-zero branch uses `Sheaf.H.equiv₀` and `rightDerivedZeroIsoSelf`.
`finite_stage_zero` applies `exists_cofiltered_etale_cohomology_cocone` and the concrete
filtered-colimit equality theorem `Limits.IsColimit.eq_iff'`. Its proof is adapted from
the source library's `Etale.exists_cohomologyMap_eq_zero_of_isLimit`; that declaration
cannot be imported here because its Gabber module imports this item.

The approximation is lifted to `Over X` using `Over.isLimitLiftCone`, then mapped by
`Over.pullback i ⋙ Over.forget Z`. Their preservation of limits and connected limits,
respectively, gives the required base-changed limit. This uses scheme continuity directly
and does not pass through affine spectra or tensor products. The original declaration
docstring describes the original DAG plan; the updated node and proof comments record the
implemented scheme-level route. Neither the unit statement nor any of its realized steps
is bypassed: this item is below the unit's own steps.

Added proof imports of `Sheaf.CategoryTheory.Sites.CohomologyDerivedEvaluation`,
`Sheaf.AlgebraicGeometry.CofilteredEtaleCohomologyCocone`, and
`Mathlib.CategoryTheory.Limits.ConcreteCategory.Filtered`. All original public imports
remain. The existing node's `proof`, `proof_deps`, and `proof_origin` now follow this proof.
Local compilation succeeds without warnings, using the required `lcompile.py` wrapper.

## Proved and sorry left

Proved the item's single original sorry:
`AlgebraicGeometry.Etale.exists_isFinite_surjective_constant_cohomology_eq_zero`
(node `lem-weil-pbc-integral-cover-kills-constant-cohomology`). Both private helpers are
fully proved. No sorry remains in the delivered module; no new module, theorem with
sorry, definition, axiom, or statement change is delivered.

The proof still depends on the existing named open interfaces
`AlgebraicGeometry.exists_integral_cover_trivial_cohomology`
(`lem-weil-pbc-integral-cover-trivial-cohomology`),
`CategoryTheory.Sheaf.cohomology_nonempty_addEquiv_rightDerived_evaluation_succ`
(`new-sheaf-cohomology-derived-evaluation`), and
`AlgebraicGeometry.Etale.exists_cofiltered_etale_cohomology_cocone`
(`lem-weil-pbc-cofiltered-etale-cohomology-cocone`). Their sorries are not part of this
delivery. This is a proof from the stage-3 interfaces, not an assertion that the entire
transitive proof is already axiom-free.

## No longer needed

Removed imports:
- `Sheaf.LinearAlgebra.TensorProduct.ColimitVaryingRings`.
- `Sheaf.AlgebraicGeometry.EtaleCohomologyLimitOfSchemes` as a direct import.
- `Sheaf.AlgebraicGeometry.EtaleCohomologyPullbackFunctorial` as a direct import.
- `WeilConjectures.ConstructibleSheaf.Defs` as a direct import.

Removed direct DAG proof dependencies:
- `def-weil-affine-spectrum`.
- `lem-weil-pbc-spec-colimit-limit`.
- `lem-weil-pbc-fibre-product-affine-spectra`.
- `lem-weil-pbc-filtered-colimit-tensor-varying-rings`.
- `lem-weil-pbc-etale-cohomology-limit-of-schemes`.
- `lem-weil-pbc-cohomology-pullback-functorial`.

The first four belong to the unused ring/tensor route. The last two remain required
transitively by the cohomology-cocone theorem; removing the direct edges does not claim
that their modules are globally unreached. Constant-sheaf pullback comparison remains
used, through `Scheme.upperStarConstantSheafIso` from the existing public import.
Whether any of the removed modules leaves the full target closure is for the maintained
queue to compute; no unrelated module was altered.

## Where the brief, the DAG or earlier work was wrong

No false statement was found. The vanishing theorem for the integral cover states
`IsZero` of the source library's derived cohomology, whereas this item states vanishing
in Mathlib's Ext-based `Sheaf.H`. The necessary comparison was not a direct dependency
of the original node. The existing Ext/right-derived-evaluation interface and the
source library's proved total/classical derived-functor comparison supply it; no new
bridge statement is needed.

The DAG's affine-ring and tensor-colimit conversions are unnecessary when the existing
scheme-level continuity cocone is used on the base-changed approximation. Importing
`WeilConjectures.SixFunctors.Etale.Gabber` to reuse its finite-stage killing lemma would
create a cycle, confirmed by `tools/import_direction.py`; its concrete colimit argument
is therefore a proved private helper here, using the independent cocone module.

The new hypotheses in the private helpers are only the hypotheses needed by the
existing interfaces. Edge cases: the comparison helper covers degree zero and arbitrary
abelian sheaves, the finite-stage helper covers a singleton diagram and a zero class;
the main proof assumes no nonemptiness of X or Z and uses only the nonempty index supplied
by cofilteredness. Finite coefficients and positive degree enter exactly in applying the
integral-cover vanishing theorem. Surjectivity is obtained from the factorization, never
assumed of the approximation's stages.

## Second reading by R2

1. Compared the delivered module with the repository module. The sole existing
   theorem signature is byte-for-byte unchanged. No definition or public import
   changes; only proved private helpers, proof imports, and the theorem proof were
   added. The node differs only in `proof`, `proof_deps`, and `proof_origin`. Pass.
2. Compiled the complete module through `lcompile.py`: exit 0, no warnings. Scanned
   for sorry and prohibited declarations: none in the module. A scratch copy with
   `#print axioms` checks the theorem and both helpers; existing open interfaces
   account for `sorryAx`, as disclosed above. No new axiom or hollow definition. Pass.
3. No statement is split off, so there is no new open statement, node, or disguised
   restatement to review. The proved comparison helper handles q = 0 via H.equiv₀
   and q > 0 via the existing Ext/derived-evaluation interface. The finite-stage
   helper handles a singleton diagram and the zero class; no inhabited scheme is
   assumed. Empty X or Z causes no invalid choice: only the cofiltered index
   category supplies a chosen object. Pass.
4. Read the proof from the theorem downward and checked the comparison, over-category
   limit, base-change cone, colimit equality, and surjectivity factorization. Searched
   the library for cohomology vanishing/comparison results and independently queried
   Loogle for `CategoryTheory.Sheaf.H, AlgebraicGeometry.Surjective` (no hits).
   The existing Gabber finite-stage theorem has precisely the relevant proof but
   imports this module, so its private replication avoids a cycle. All four public
   imports support the unchanged statement; the five proof imports support the proof.
   Checked sk-thm-p1.realized: neither this node nor the pruned ring/tensor nodes
   realizes a unit statement or step. The same integral-cover, approximation, and
   continuity argument remains. The six removed old proof dependencies are exactly
   those listed under No longer needed. Pass.
5. Read the original and updated node and the imported interfaces. The six updated
   steps accurately describe the Lean proof, and proof_deps is exactly the union
   of their uses. No new node is needed. The theorem's existing docstring still
   describes the old affine-ring realization; the proof comments, updated DAG,
   and this report identify the current scheme-level realization. Pass.

Changes by the second reader: appended this review and recorded an independent
search and axiom inspection; no repair to the Lean proof or DAG was needed.
