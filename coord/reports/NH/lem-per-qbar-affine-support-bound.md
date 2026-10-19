## Worker report

The delivery states `AlgebraicGeometry.Scheme.PerAdic.qbarAffineSupportBound`
in `Sheaf.Paper.QbarAffineSupportBound`, using the actual completed adic
common-stage presentation publicly retained by the current dependency modules.
The item statement is unchanged. The Qbar direct-image extension has its own definition node, as requested by return option (b).

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- The field is `{k : Type u} [Field k]`; the prime and its invertibility are
  `l : ℕ`, `[Fact l.Prime]`, and `[Fact (IsUnit (l : k))]`.
  The algebraic closure of the coefficient field is `Ω : Type v` with
  `[Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]`. Its universe is independent.
- Separated finite-type k-schemes are `X Y : PerAdic.Base k`. The recorded
  structure stores `scheme.Over (Spec (.of k))`, locally finite type,
  quasi-compactness, and separatedness of the structure morphism. The recorded
  `baseNoetherian`, `baseDimension`, and `basePrimeUnit` instances derive the
  adic domain conditions from precisely these hypotheses; none is separately assumed.
- The affine finite-type k-morphism is `f : X.scheme ⟶ Y.scheme` with
  `[f.IsOver (Spec (.of k))] [IsAffineHom f] [LocallyOfFiniteType f]`.
  Affineness supplies quasi-compactness, so this is finite type.
- The input is a sheaf in the standard constructible heart:
  `F : CommonHeart l Ω X`, whose `F.obj` is its underlying complex.
  This is the full heart of the recorded `commonT` standard t-structure.
- The nonnegative integer is `a : ℤ` with `ha : 0 ≤ a`. Its support hypothesis is
  `hF : topologicalKrullDim (pbcQbarCohomologySupport l Ω X.scheme F.obj 0)
  ≤ (a.toNat : ℕ∞)`. This support is the closure of nonzero completed geometric
  cohomology fibres, after scalar extension to Ω; no discrete stalk is substituted.
- The direct image is `(qbarDerivedDirectImage l Ω X Y f).obj F.obj`.
  For every `q : ℕ`, the theorem bounds its degree `(q : ℤ)` closed support.
  The conclusion is guarded by `.Nonempty` and requires both `0 ≤ a - (q : ℤ)`
  and the dimension inequality with `((a - (q : ℤ)).toNat : ℕ∞)`.
  Thus negative bounds force empty support, and empty support satisfies every
  bound. This is exactly the node's dimension-minus-infinity convention.
- For every `q : ℤ` with `q < 0`, the second conjunct is `IsZero` of
  `(cohomology (commonT l Ω Y) q).obj` applied to the same direct image.
  This uses standard rational/common-stage cohomology, so torsion in an
  integral representative does not add a condition to the rational sheaf.

Dependency declarations used:

- Mathlib `AlgebraicGeometry.IsAffineHom`, `LocallyOfFiniteType`, `QuasiCompact`,
  `IsSeparated`, and `Scheme.Hom.IsOver` give the scheme/morphism conventions.
- `Sheaf.Paper.IntrinsicQbarCategory` publicly preserves `pbcQbarCategory`
  alongside its intrinsic presentation. No carrier category is redefined here.
- `Sheaf.Paper.AdicHeartIntrinsicFibres.sfAdicHeartPullbackFibres` publicly retains
  all twelve original clauses from `AdicHeartPullbackFibres`, including
  `PerAdic.Base`, `CommonHeart`, `commonT`, and `cohomology` on the raw completed
  common-stage category. These are the recorded standard-heart interface used here.
- `Sheaf.Paper.PbcSupportCondition` defines
  `AlgebraicGeometry.Scheme.pbcQbarCohomologySupport` using the fibre construction
  from `PbcCohomologySheaves`. The recorded upgraded support module publicly
  retains this interface. We import its actual defining module directly because
  importing the upgrade also imports `IntegralHomReduction`, whose current
  source fails on universe constraints at line 98 and later. The item uses the
  support construction only; no cosupport or ambient dual is needed. This is
  the exact retained support notion, with no duplicate definition or size restriction.
- `Sheaf.Paper.PbcQbarCompletedPullback.pbcQbarCompletedPull` is the canonical
  completed pullback used by the new direct-image definition. Its finite-stage maps and
  scalar comparisons are the published ones.
- `Sheaf.Paper.QbarDerivedDirectImage.qbarDerivedDirectImage` supplies the
  arbitrary-field constructible direct image. Its right-adjoint characterization
  specifies the actual functor up to the adjunction-compatible isomorphism.
  The imported `SfCommonStageDirectImage` preserves the existing integral tower
  and finite-field construction rather than replacing them.

Recorded proof-dependency modules are imported directly or through these modules
whenever their current source does not bring in the failing unrelated cosupport
closure noted above. The six previously missing imports were added explicitly:
`DerivedNakayamaResolution`, `IntegralConstructibleReductionFibres`,
`AffineDirectImageSupportBound`, `ContinuousRationalDerivedRealization`, and
`ProEtaleDirectImageComparison`, and `CompactSupportComparisonUnit`. The theorem docstring records all eleven proof
steps from the current node. Both postponed theorems belong to their owning DAG
nodes and have proof docstrings; definitions have real data.

Edge cases checked: zero F; empty X or Y; empty support; a = 0; q = 0; q > a;
negative q; identity morphisms; disconnected schemes; and integral representatives
with uniformizer-power torsion outside degree zero. For q > a a nonempty support
would require the false inequality 0 ≤ a-q, so the conclusion forces empty support.
For empty support the implication has no premise. The heart input and rational
cohomology formulation retain the torsion-representative case.

Searches: `msearch.py leanfinder` for “affine finite type Qbar ell direct image support
bound” found no relevant declaration; `msearch.py loogle` for
`pbcQbarCohomologySupport, derived direct image, affine` found no exact match; grep
of Mathlib and `WeilConjectures/` for `perverse|affine.*support|higher.*direct` found
no matching adic support theorem. Grep of `lean/Sheaf` found only the finite-field
`sfModelDerivedPush` and the lower-level finite-stage direct-image constructions.

Current-source searches also checked both delivered declaration names across
`lean/Sheaf` and the read-only `WeilConjectures` source; neither already exists.
The current six statement-dependency records and their full source interfaces were
read. Their upgraded modules explicitly reexport the raw interfaces used here.
No duplicate definition or extra hypothesis is introduced to switch presentations.

## Second reading by NH

This is the resumed author's self-check; the maintainer performs the independent
review. I reopened the item, both modules, the live N5 node and its source. Each
item hypothesis and conclusion still matches the clause mapping above, including
empty support, q > a, negative degrees, torsion representatives and independent
universes. The existing theorem signature and all mathematical constructions are
unchanged. All variables are explicitly bound, both recorded signatures are exact,
and every line is at most 100 characters.

## New nodes

`def-per-qbar-derived-direct-image` owns `Sheaf.Paper.QbarDerivedDirectImage` and its
two declarations. Its statement gives exactly the module's arbitrary-field data:
k is a field, l is an invertible prime, Ω is an algebraic closure of Q_l, X and Y
are separated finite-type k-schemes, and f is a finite-type k-morphism. The completed
pullback is `pbcQbarCompletedPull l Ω f`; the named theorem asserts it is a left
adjoint, and `Functor.rightAdjoint` constructs its right adjoint using that universal
property. The real construction and proof docstring are retained. Zero or empty
schemes, identity maps and independent coefficient universes impose no extra conditions.

Source: Bhatt--Scholze Proposition 6.8.14(2) and Remark 6.8.15, read from the local
paper. Proposition 6.8.14 gives rationalization and common finite-stage transport;
Remark 6.8.15 gives the derived inverse/direct-image adjunction and restriction to
constructible complexes under Section 6.7's finiteness assumptions. The existing
integral and finite-field constructions are publicly imported, not restated.

Searches of the DAG (`blueprint_refs.py search` and rg), Mathlib (LeanSearch,
LeanFinder, Loogle and grep), upstream WeilConjectures and project Sheaf sources
found general adjunction tools and the existing finite-field `sfModelDerivedPush`,
but no definition node for this arbitrary-field completed Qbar functor. Queries
and actual results are recorded in the new node. `blueprint_refs.py ancestor`
identifies `lem-per-artin-gabber-affine-curve`; the new node is in the item's own
chapter and unit and is added to the item's stmt_deps.

## Return repair H13/H4

The returned immutable head was `4a1328d8b19a`. The saved repair used reviewer
option (a), listing the fourteen live N5 declarations followed by the two Qbar
ones. This session's required first dry run compiled both modules but preflight
rejected all fourteen imported names because its declaration ownership check
looks for declarations in the owning file or Mathlib/upstream sources.

Applied the reviewer's option (b). The packet no longer contains a copy or edit
of `def-weil-derived-direct-image`: its live N5 record, fourteen declarations and
ownership of `SfCommonStageDirectImage.lean` remain unchanged. The Qbar extension
now belongs to `def-per-qbar-derived-direct-image`. Every blueprint marker in its
module names that new owner, whose record lists exactly its two new declarations.
The item gains that definition in stmt_deps and still retains every original
dependency. No statement, theorem signature or construction has changed.

Self-check: the new node's complete parameters match the module, its definition
has real right-adjoint data, its prerequisite theorem has the existing source and
complete proof docstring, both new declarations have one owner, and the imported
N5 module has its original owner. No live source, old declaration, adjunction
normalization, shift comparison, exchange arrow or forgetful comparison is edited.
The existing users WeilOpenImageDelta, GraphFrobeniusPointExchange and
FrobeniusCohomologyTransport retain their entire recorded interface.
