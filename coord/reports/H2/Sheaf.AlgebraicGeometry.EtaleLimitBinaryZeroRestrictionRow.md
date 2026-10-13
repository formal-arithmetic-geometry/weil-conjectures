## What changed

Completed the earlier attempt in
`lean/Sheaf/AlgebraicGeometry/EtaleLimitBinaryZeroRestrictionRow.lean` without changing
its theorem signature or public imports. The directed tail above i₀ is constructed
explicitly and proved final. Apply the new single-open comparison separately to U
and V, take the functor-category biproduct, and form the comparison using
`Functor.mapBiprod` and `AddCommGrpCat.biprodIsoProd`. The colimit functor is additive,
so this finite biproduct comparison needs no filtered-colimit/finite-limit theorem.
Mayer–Vietoris initial injectivity proves component injectivity after the supplied
cohomology isomorphisms. Projection calculations and `colimit.ι_map` prove the
stage-leg equation. The `iso`, `prod`, and `comp` constructors give the certificate.

Fixed the previous projection rewrites by applying `biprod.lift_fst` and
`biprod.lift_snd` directly after unfolding `Functor.mapBiprod_hom`. The explicit
application resolves the dependent definitional identifications that `rw` did not
match. Retained a local increased heartbeat budget: the default 200000 was tested
and exhausted at the stage-leg calculation; 600000 compiles within the file timeout.
The local unused-variable linter setting accommodates the original existential
finality witness `ht`, whose name is not used by the original conclusion.

The new module `Sheaf.AlgebraicGeometry.EtaleLimitSingleOpenComparison` isolates the
single-open geometric comparison and its restriction naturality. The remaining
binary assembly is proved in the assigned module. The new theorem asserts no
injectivity and no binary/product assembly. Its named hole has its source, full
proof in words, and matching node. The item's DAG proof now follows this reduction.
No definitions or existing interfaces are changed; no forced adaptations are needed.

## Proved and sorry left

Closed: `AlgebraicGeometry.Etale.etale_limit_binary_zero_restriction_row`
(node `lem-weil-pbc-etale-limit-binary-zero-restriction-row`), originally the module's
only sorry. It is now a complete Lean proof from the single-open comparison and the
existing `etale_mayerVietoris_connecting_pullback` theorem.

Added and left: `AlgebraicGeometry.Etale.etale_limit_single_open_comparison`
(node `lem-weil-pbc-etale-limit-single-open-comparison`), exactly one public theorem
with proof `:= by sorry`, in its own new module. This is a decomposition: one upper
hole closed, one strictly smaller geometric hole added, net zero holes. It does not
claim a sorry-free proof of the full geometric construction.

The two private biproduct projection helpers are proved. There is no sorry left in
the assigned module, no sorry in any definition, and no other new hole.

## No longer needed

Removed these proof-only imports from the assigned module:

- `Sheaf.AlgebraicGeometry.EtaleCohomologyPullbackFunctorial`
- `Sheaf.AlgebraicGeometry.EtaleMayerVietoris`
- `Sheaf.AlgebraicGeometry.EtaleMayerVietorisPullback`
- `Sheaf.AlgebraicGeometry.EtaleLimitCanonicalCohomologyDiagram`
- `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`
- `Mathlib.AlgebraicGeometry.AffineTransitionLimit`
- `Mathlib.CategoryTheory.Limits.FilteredColimitCommutesFiniteLimit`
- `Mathlib.CategoryTheory.Adjunction.Limits`
- `Mathlib.CategoryTheory.Preadditive.AdditiveFunctor` (redundant proof import removed
  in the second reading; its API is already available through `Grp.AB`)
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`

The removed direct proof dependencies are
`def-weil-pbc-scheme-conventions`,
`lem-weil-pbc-cohomology-pullback-functorial`,
`lem-weil-pbc-etale-inverse-image-restriction`,
`lem-weil-pbc-etale-limit-canonical-cohomology-diagram`,
`lem-weil-pbc-etale-mayer-vietoris`,
`lem-weil-pbc-etale-mayer-vietoris-pullback`,
`lem-weil-pbc-filtered-colimits-commute-finite-limits`,
`lem-weil-pbc-inverse-image-composition`,
`lem-weil-pbc-left-adjoint-preserves-colimits`, and
`lem-weil-pbc-limit-cone-affine-projections-opens`.

The single-open geometric dependencies (scheme conventions, pullback functoriality,
restriction, canonical diagram, inverse-image composition, left-adjoint preservation,
and open limit cones) remain in the new node's proof plan and corresponding imports;
these are relocated, not claimed globally unnecessary. The row no longer uses the
Mayer–Vietoris theorem with derived-section identifications, its full pullback ladder,
or filtered-colimit/finite-limit commutation. Initial injectivity comes directly
from `EtaleMayerVietorisConnectingPullback`. This report claims pruning from this
route, not that these modules are unreachable from every other target branch.

No node realizing the unit's statement or numbered proof steps is bypassed. The
unit is `sk-thm-p1`; its `realized` lists do not contain these row-level tool nodes.

## Where the brief, the DAG or earlier work was wrong

The inherited report described two intermediate modules named core and certificate,
but neither existed in the actual sandbox. The actual attempt had already moved to
one single-open module and a binary assembly proof, failing only at the two
projection rewrites. That stale report has been replaced.

The earlier report's claim that the geometric construction had to be split to avoid
the single-file timeout is unsupported. The current split is mathematical: single-open
geometry versus binary injectivity and additive assembly. No file has been split to
work around a timeout. The only observed budget failure is the default heartbeat
limit during the binary proof, resolved locally within the file's time limit.

The original plan uses filtered-product preservation. In abelian groups, additivity
of the colimit functor already preserves finite biproducts, so filtered finite-limit
commutation is unnecessary here.

Checked the sources at https://stacks.math.columbia.edu/tag/09YQ,
https://stacks.math.columbia.edu/tag/0A50, and
https://stacks.math.columbia.edu/tag/01F7. The single-open statement records the
geometric comparison, not the continuity isomorphism asserted by 09YQ, and its
certificate makes no continuity claim. Empty W, W = O, empty/coincident U and V,
and a one-element indexing preorder do not require any extra hypothesis. For
W empty the sheaf cohomology groups vanish; for W = O the construction reduces
to tail reindexing. The least restricted tail stage is isomorphic to W, so it
satisfies the certificate's allowed-stage predicate. The target's original
signature was compared verbatim after whitespace normalization and is unchanged.

## New nodes

`lem-weil-pbc-etale-limit-single-open-comparison`, in
`dag/nodes/sec-proper-base-change/lem-weil-pbc-etale-limit-single-open-comparison.json`,
states the one-open geometric comparison with its actual restriction transformation
and stage-leg equation. Its module is
`Sheaf.AlgebraicGeometry.EtaleLimitSingleOpenComparison`. It is used twice by the row
and omits all the binary injectivity and product assembly proved there. Its searches
are in the sandbox search log; the unavailable LeanSearch service is recorded as
unavailable, not as a negative match. No change records are needed.


## Second reading by H2

Independent second reader, 2026-10-13. I did not write this proof.

1. **Interfaces — pass.** Read the full diff against the repository module.
   The complete existing theorem signature, extracted from `theorem` through
   its conclusion before `:= by`, is byte-for-byte identical. Existing public
   imports and the original theorem docstring are unchanged. The only existing
   node fields changed are `proof`, `proof_deps`, and `proof_origin`. No target,
   definition, or module held by another group is changed; no change record is
   required. The new theorem lives in its own module.
2. **Proof and axioms — pass as a decomposition.** Compiled both delivered
   modules in import order with `lcompile.py`: no errors or warnings. Read the
   proof from tail finality through component injectivity, the biproduct comparison,
   certificate constructors, and both projection equations. Scratch copies with
   `#print axioms` show only `propext`, `Classical.choice`, `Quot.sound`, and
   `sorryAx` for the two public theorems; the two private projection helpers use
   only the three permitted axioms. The assigned module has no remaining sorry.
   The single-open theorem is the sole added hole, exactly `:= by sorry`.
   There are no forbidden declarations or hollow definitions. Existential
   elimination occurs only inside the proof of a proposition; no public data
   definition chooses an arbitrary witness from an unproved existence theorem.
3. **Split statement — pass.** Read the single-open theorem, its node, the
   canonical cohomology-diagram theorem, and the complete comparison-certificate
   constructors. Restricting the system on the fixed tail gives the claimed
   diagram and canonical comparison; the least restricted stage is isomorphic
   to W, which is sufficient for the arbitrary supplied allowed predicate.
   The hypotheses supply qcqs stages and affine transitions, so the pulled-back
   compact opens satisfy the system constructor. Its docstring provides the
   geometric restriction, coherence, colimit transport, certificate, naturality,
   and stage-leg argument with sources. Checked empty W, W=O, the singleton
   preorder, zero coefficients, empty/coincident U and V, and the case O empty.
   No nonempty-open or continuity hypothesis is needed. This is strictly part
   of the row construction: it supplies neither joint injectivity nor the binary
   colimit/certificate assembly, all of which are proved in the assigned module.
   Independent LeanFinder, Loogle and grep queries (recorded on the new node)
   and rg searches of both source roots found geometric cone tools and the
   canonical diagram, but no duplicate supplying this whole single-open statement.
   In particular `isLimitOpensCone` supplies only the scheme-limit step, so the
   remaining coefficient coherence construction cannot be closed in a few minutes.
   Source checks: [09YQ](https://stacks.math.columbia.edu/tag/09YQ),
   [01F7](https://stacks.math.columbia.edu/tag/01F7), and
   [0A50](https://stacks.math.columbia.edu/tag/0A50).
4. **Route and pruning — pass.** The top-level proof uses the existing initial
   Mayer–Vietoris injectivity theorem and Mathlib's additive colimit/biproduct API;
   filtered-colimit finite-limit commutation is unnecessary. Compared the old
   and new proof dependency sets: all ten removed nodes are listed under
   `## No longer needed`, with relocated single-open dependencies distinguished
   from pruning. Read `dag/units/sk-thm-p1.json` and its `realized` statement and
   steps: no realized node is bypassed and the unit route stays intact.
   Public imports are needed for the signature; proof imports remain plain.
   The new holed module retains the imports of its recorded proof plan.
5. **DAG correspondence — pass.** Both nodes' proof dependency sets are exactly
   the union of their steps' `uses`. The row node records the actual final-tail,
   single-open, injectivity and additive assembly route. The new node has its
   source, complete proof plan, searches, split status, creation record, blueprint
   ancestry, chapter/unit and Lean declaration/signature; the Lean statement
   matches its recorded signature. No extra hole or node is hidden in a helper.

Changes made in this reading: removed the redundant plain import
`Mathlib.CategoryTheory.Preadditive.AdditiveFunctor` and confirmed the row still
compiles; added independent duplicate-search results to the new node; updated
this report and its pruning list. No mathematical statement or proof body was
changed. The delivery closes one old hole and adds one strictly smaller hole:
one decomposition, net zero holes, with the listed direct imports pruned.
