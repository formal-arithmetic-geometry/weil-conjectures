## What changed

Replaced the sole sorry in
`AlgebraicGeometry.Scheme.nonempty_rightDerived_etale_affineOpenCech_succ`
with a complete Lean composition through an actual injective-resolution Čech
double complex. Its signature and original docstrings are unchanged. Its proof
imports now use `Sheaf.CategoryTheory.SpectralSequenceNatRowZero`,
`Sheaf.AlgebraicGeometry.EtaleAffineOpenCechResolutionColumns`, and
`Sheaf.AlgebraicGeometry.EtaleOpenCechResolutionTotal`.

The four new modules contain:

- `EtaleOpenCechResolutionDoubleComplex`: the actual construction
  `C^p(U,i^*I^q)` by mapping the resolution through the Čech functor and flipping
  indices, and a proved zero-morphism-preservation instance for large coefficients.
- `EtaleAffineOpenCechResolutionColumns`: a complete proof of the zero-row complex
  identification and positive vertical-row vanishing. This uses exactness of
  products (with an explicit universe shrink), naturality of homology for the
  Čech differentials, the degree-zero derived-functor comparison, and the
  evaluation comparison for an injective resolution. Product opens equal their
  infimum by projection/lift inequalities; `IsAffineOpen.iInf` proves affineness.
  The equality `hi` transfers this to the underlying étale scheme. This lemma
  needs no covering hypothesis, no terminal object, no finite-limit preservation
  by `i`, and no finite-index hypothesis.
- `SpectralSequenceNatRowZero`: a complete generic proof for the actual
  natural-index spectral-sequence API. Vanishing propagates to every page, the
  bottom row is stationary, zero filtration quotients make successive
  inclusions invertible, and the final quotient is the whole abutment. The
  integer-index `FirstQuadrantRowCollapse` has a different filtration interface;
  it is neither imported nor assumed.
- `EtaleOpenCechResolutionTotal`: the one deferred augmentation comparison. It
  concerns total homology of the resolution, assumes neither separatedness nor
  affine opens nor affine acyclicity, and applies to every resolution and every
  degree. Its docstring gives the covering, product comparison, injective-row
  acyclicity, augmentation, and finite-diagonal argument.

The main theorem obtains the existing spectral sequence of this double complex,
proves its page-two positive rows zero by the column calculation, collapses its
actual finite abutment filtration, and composes the page-two, bottom-row and
inverse total-comparison isomorphisms. There is no unspecified auxiliary group
or choice of spectral data from an unproved existence statement.

All five modules compiled together via `lcompile.py --all`, without warnings.
The existing theorem's textual signature is unchanged. No existing definition,
statement, visibility, or public import was changed. No forced adaptations.
Edge cases checked in the argument: empty index families have empty tuple
products (zero groups); finite nonempty products of opens may be empty affine
schemes; singleton and repeated opens are allowed; the collapse proof includes
n=0 and therefore degree one of the item.

## Proved and sorry left

Holes closed in the item: one,
`AlgebraicGeometry.Scheme.nonempty_rightDerived_etale_affineOpenCech_succ`
(node `lem-sc-etale-affine-open-cech-derived-evaluation-succ`).

Holes added: one,
`AlgebraicGeometry.Scheme.nonempty_etale_openCech_resolution_total_iso`
(node `lem-sc-etale-open-cech-resolution-total`), whose body is exactly `by sorry`.
This is the only sorry in the five delivered modules. Thus this is a genuine
one-hole decomposition, not a claim of a net hole reduction or an axiom-free
proof of the original item. The total-resolution comparison is strictly a
separate step: it does not relate derived evaluation to the sections Čech
complex and has no affine acyclicity hypothesis. The independently proved
column and collapse calculations are needed to make that final comparison.

Additionally proved with no sorry:
`AlgebraicGeometry.Scheme.etale_affineOpenCech_resolution_columns` and
`CategoryTheory.SpectralSequence.nonempty_abutment_iso_row_zero`, including all
private helpers. The new double-complex definition and named instance contain
no sorry. The existing double-complex spectral-sequence theorem remains an
existing proof dependency; no claim is made that all of its dependencies are
axiom-free.

## No longer needed

Removed the item's proof imports:

- `WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Cech`, node
  `lem-sc-cech-spectral`;
- `Sheaf.CategoryTheory.Sites.CohomologyDerivedEvaluation`, node
  `new-sheaf-cohomology-derived-evaluation`.

The resulting argument does not use the Ext cohomology presheaf, cohomology at
an object versus constant-integer-sheaf cohomology, or any of the equal-universe
Čech resolution comparison modules imported by the removed spectral module:
`Sheaf.CategoryTheory.Sites.SheafCohomology.CechGeneral`
(node `stage3-cech-general-double-complex`),
`Sheaf.CategoryTheory.CechResolutionColumns`
(node `lem-sc-cech-resolution-columns`),
`Sheaf.CategoryTheory.CechResolutionTotal`
(node `lem-sc-cech-resolution-total`), and
`Sheaf.CategoryTheory.CechResolutionDoubleComplex`
(node `def-sc-cech-resolution-double-complex`). Their Ext-based column branch,
`InjectiveResolutionCohomologyPresheaf` and
`InjectiveResolutionCohomologyPresheafData`, is also unused here. These are
pruned from this item's proof route; no claim is made that other targets cease
using them. The existing general double-complex spectral-sequence theorem
`thm-sp-double-complex-spectral-sequences` stays needed. Injective Čech
acyclicity stays needed in the remaining total-comparison plan.

No original public import is removed. The unit record `sk-prop-cd` and all its
realized statement/step bindings are untouched. All retained proof imports in
the item are used.

## Where the brief, the DAG or earlier work was wrong

The previous attempt's existential auxiliary group simply repackaged the entire
item. Its rejected files remain archived only under `scratchpad/`; none is in
this payload. This delivery replaces that attempt with genuine vertical
homology and finite-filtration proofs.

The original plan's invocation of the existing Ext-valued Čech spectral theorem
is not directly applicable to the requested coefficient universe. Mathlib's
`Sheaf.cohomologyPresheaf` and the existing Čech spectral theorem constrain the
coefficient universe to the site's morphism universe, whereas this item uses
`AddCommGrpCat.{u + 1}` on a site with morphisms in universe u. Trying to state
the proposed cohomology-presheaf rows failed with a sheaf-universe type mismatch.
The existing object-cohomology/derived-sections comparison has the same
small-category/equal-universe limitation. The final proof bypasses that Ext
interface and uses the actual resolution with the larger coefficients. This
changes no target meaning and follows the same Čech double-complex argument.

LeanSearch returned Internal Server Error; its attempted queries are recorded
as unavailable. Loogle, LeanFinder, and source searches were used as well.

The local literature checkout contains citation indexes but no Stacks source
files. The cited primary pages were read directly: Tags 03AZ, 03AW, 03F6, 03P2,
011O and 0132. The node records mark the implementation proofs as agent-written
reformulations of those arguments. No literature or repository files were
written outside the authorized sandbox.

## New nodes

`def-sc-etale-open-cech-resolution-double-complex`: actual mapped-resolution
construction with the required large coefficient universe; no holed data.

`lem-sc-etale-affine-open-cech-resolution-columns`: fully proved column
calculation, independent of any covering or total-complex convergence.

`lem-sc-spectral-sequence-nat-row-zero`: fully proved collapse for the
natural-index page/abutment convention used by the existing spectral theorem.

`lem-sc-etale-open-cech-resolution-total`: the single new sorry, the general
injective-row augmentation comparison; complete proof in words and planned
existing injective Čech acyclicity/first-quadrant augmentation dependencies.

The original item's node is updated only in `proof`, `proof_deps` and
`proof_origin`. All four new nodes inherit its chapter and unit and record
three kinds of Mathlib searches, their exact Lean signatures and sources.
No change records are required because no existing interface changed.

## Second reading by K2

1. **Interfaces: PASS.** Read the full diff against the repository's item.
   The existing theorem's signature and docstrings are byte-for-byte unchanged;
   the only changes are proof imports and its proof body. The four other Lean
   modules are new. No existing definition, public import, visibility or target
   statement changed; no change record or forced adaptation is necessary.
2. **Proof and trust: PASS as a decomposition.** Compiled all five modules in
   import order using `lcompile.py --all`, without errors or warnings. Read all
   proof bodies and the actual double-complex definition. The sole textual
   sorry is the named total-comparison theorem, exactly `:= by sorry` with its
   source, full argument and node. No forbidden declarations or holed data.
   A scratch copy with `#print axioms` confirms the columns, row collapse,
   double-complex construction and zero-preservation instance use only
   `propext`, `Classical.choice`, `Quot.sound`. The main theorem and deferred
   comparison additionally use `sorryAx`, as reported. The injective resolution
   is Mathlib's real construction. Spectral data come from the existing
   double-complex theorem, whose page identifications and abutment filtration
   determine precisely the objects used in the proof.
3. **Split statement: PASS.** Independently checked the deferred comparison
   against [Stacks 03AW](https://stacks.math.columbia.edu/tag/03AW),
   [03F6](https://stacks.math.columbia.edu/tag/03F6), and the construction behind
   [03AZ](https://stacks.math.columbia.edu/tag/03AZ). Cover preservation and finite
   limits suffice without the affine functor equality hi: they send this cover
   and its intersection diagram to an étale covering and its fibre products.
   Its row augmentation is the restriction map, so H0 is sections and positive
   homology is zero for each injective term. Finite diagonals then give the
   total comparison. For an empty index, hcover makes top the empty open and
   the empty image cover forces all evaluated terms to be zero. A singleton
   cover, repeated opens, degree zero and empty intersections are consistent.
   This is strictly the total-resolution step, with neither affine vanishing
   nor a conclusion involving the sections Čech complex; it does not restate
   the item. Fresh Loogle and LeanFinder queries used resolution computation
   and augmented cochains rather than the first reader's wording. Source `rg`
   searches found `injective_cech_total_sections_nat` and
   `Sheaf.cechResolutionDoubleComplex_total`; I read their statements and
   proofs. Both constrain group values to the site's morphism universe,
   unlike this item's `AddCommGrpCat.{u + 1}`. The existing étale acyclicity and
   first-quadrant augmentation remain the valid planned building blocks.
   Closing this hole also requires the functor/product comparison and canonical
   H0 augmentation; it is not a few-minute application of an existing lemma.
4. **Route and pruning: PASS after one repair.** Read the proof from the main
   theorem down through the vertical-homology and finite-filtration arguments.
   Product exactness, the natural H0 comparison, and propagation of vanishing
   are proved, not deferred. The collapse handles n=0 explicitly. Both old
   proof dependencies (`lem-sc-cech-spectral` and
   `new-sheaf-cohomology-derived-evaluation`) are listed as no longer needed.
   The unit `sk-prop-cd` and its `realized` bindings are untouched; this changes
   only the implementation below the unit level. Removed the redundant direct
   proof import `WeilConjectures.Mathlib.Algebra.Homology.TotalComplex` from the
   item: the new total-comparison module publicly supplies it because its
   statement needs totalization. The main proof still uses the spectral theorem
   and its node remains a proof dependency; this is import deduplication, not
   pruning that node. Recompiled the item successfully after this repair.
5. **DAG: PASS.** The existing node changes only `proof`, `proof_deps`, and
   `proof_origin`. Its three steps match the actual resolution, vertical
   homology, spectral collapse and final isomorphism composition. New nodes
   record their exact signatures, sources, searches, creation provenance and
   chapter/unit. The total node records an honest remaining proof plan;
   the proved columns and collapse nodes describe the actual Lean arguments.

Second reading changed only the redundant proof import and this report.
One original hole is closed and one strictly separate lower hole is added:
net hole reduction zero. No additional theorem is claimed as axiom-free beyond
what the explicit axiom checks establish. Final delivery-tool preflight also
checks every declaration, including private helpers.
