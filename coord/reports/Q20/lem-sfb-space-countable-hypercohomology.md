## Worker report

The module `Sheaf.AlgebraicGeometry.SpaceCountableHypercohomology` states
`AlgebraicGeometry.AlgebraicSpace.countable_hypercohomology_tensor_perfect`, with
one postponed theorem and no definitions. Its proof is `sorry`; its docstring
contains the complete four-step DAG proof with every proof dependency named.
Source read: `literature/stacks-project/spaces-perfect.tex`,
`lemma-countable-cohomology` (Tag 0CRU), including the complete proof. The theorem
is precisely its hypercohomology assertion, which is the assertion selected by
this node. The Ext assertion belongs to the larger source lemma and is not added.

This repairs the H2 return for immutable head `7f74d741f328`. The saved packet
passed the initial dry run (`bfd85a97e01`), but still cited the etale-local theorem
node for two definitions. The repair replaces that dependency with the existing
owners `def-sfb-space-quasi-compact-presheaf-map` and
`def-sfb-presheaf-map-separated-diagonal`. The Lean file is retained byte for byte.
The current shared node has the same mathematical statement and original eight
statement dependencies as the saved packet; only `stmt_deps` and `lean` differ.
The delivery wrapper rebases the repaired packet on the current server branch.

### Hypotheses and clauses

| Node clause | Exact Lean rendering |
| --- | --- |
| Schemes and algebraic spaces over any scheme S | `{S : Scheme.{u}} (X : AlgebraicSpace S)` and `(U : AlgebraicSpace S)`. |
| The fixed universe convention | Explicit `u wX wU`; the existing u-small ringed models preserve section universe u. `HasDerivedCategory.{wX}` and `HasDerivedCategory.{wU}` specify independently sized localizations, with no equality between those sizes. |
| X is quasi-compact | `hqc : CompactSpace (Point X.obj.obj)` for the recorded atlas point topology. |
| X is absolutely quasi-separated | `hqs : X.IsAbsolutelyQuasiSeparated`, the recorded affine-pair criterion equivalent to quasi-compactness of the absolute diagonal (Stacks 0AHR), not the diagonal relative to S. |
| K is in the unbounded D_QCoh(O_X) | `K : X.DerivedModules` and `hK : X.derivedQCohProperty K`. The predicate tests every integer cohomology sheaf, transported by the recorded inverse module equivalence, using Mathlib `IsQuasicoherent`. |
| Every cohomology sheaf has countable sections on every affine etale scheme over X | `hcount : ∀ (j : ℤ) (V : X.EtaleSite), IsAffine (X.etaleForget.obj V) → Countable (((X.smallModuleEquivalence.inverse).obj ((DerivedCategory.homologyFunctor X.SmallModules j).obj K)).val.obj (op V))`. This evaluates the actual cohomology sheaf on the original site; it neither restricts to the chosen skeleton nor uses global hypercohomology in the premise. |
| Any etale v : U to X | `(v : U ⟶ X)` and `hvet : IsEtale v.hom.hom`. This is the same representable etale predicate as the algebraic-space definition. U is an algebraic space, not required affine or a scheme. |
| v is quasi-compact | `hvqc : IsQuasiCompactPresheafMap v.hom.hom`, the recorded affine scheme-test/atlas criterion. |
| v is quasi-separated | `hvqs : IsQuasiCompactPresheafMap (diagonalPresheafMap v.hom.hom)`, testing the relative diagonal of v; separatedness is not imposed. |
| Any perfect P in D(O_X) | `(P : X.DerivedModules)` and `hP : SheafOfModules.IsPerfectOnRingedSiteOfUniverses.{u, u, u, wX} X.smallStructureSheaf P`. This is the recorded local bounded finite-free-retract definition. Bounds and ranks may vary with the covering object. |
| Tensor computed by K-flat resolutions | `(X.derivedDualityModel.closed.tensor).obj (K, P)` is the existing normalized derived tensor from the calculus node. It retains the K-flat representative model. No arbitrary tensor or comparison is a parameter. |
| Restrict this tensor along v | `(derivedTensorPullback.{u, wX, wU} v).obj (...)` is the recorded canonical total left derived ordinary module pullback. Since v is etale, ordinary pullback is exact and this is its canonical restriction on derived categories. It is not derived Zariski restriction to a scheme chart. |
| Every integer i and countability of the underlying set of H^i RΓ(U,...) | `(i : ℤ)` and `Countable ((ringedSiteZerothHypercohomologyOfUniverses.{u, u, u, wU} U.smallEtaleModelTopology U.smallStructureSheaf).obj ((...)⟦i⟧))`. In the cochain convention, H^0(F[i]) = H^i(F). The functor is exactly the recorded H^0 composed with K-injective derived global sections, with its output coerced to its underlying set. |
| No boundedness on K | No IsGE, IsLE, bounded representative, finite amplitude, or perfectness hypothesis on K occurs. |

### Recorded dependency declarations used

Every original statement dependency was read with its Lean record or Mathlib match,
and the corresponding signature and docstring were opened. The convention node has
no declaration; explicit universes realize it. The following are the interfaces used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicSpace`, `EtaleSite`,
  `etaleForget`, `structureSheaf`, `Modules`, `IsEtale`, and the exact restriction
  `pullback` (read to check the meaning of etale restriction).
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`,
  transparently the existing `SheafOfModules` category, used by SmallModules.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`; `...HomologySequence`: `DerivedCategory.homologyFunctor`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule`: `QCoh` and its
  Mathlib predicate `SheafOfModules.IsQuasicoherent`, reused by derivedQCohProperty.
- `Sheaf.Paper.StrictPerfectCoefficientPackageOfUniverses`:
  `SheafOfModules.IsPerfectOnRingedSiteOfUniverses`, including its
  `IsLocallyStrictPerfectComplexOfUniverses` definition and finite-free splittings.
- `Sheaf.Algebra.Homology.RingedSiteZerothHypercohomologyOfUniverses`:
  `CategoryTheory.ringedSiteZerothHypercohomologyOfUniverses`. Its public import
  retains the original `WeilConjectures.Algebra.Homology.RingedSiteZerothHypercohomology`
  construction. Both signatures and the actual right-derived/H^0 construction were read.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceSmallRingedModel`: `SmallModules`,
  `smallStructureSheaf`, `smallModuleEquivalence`. The restriction equivalence uses
  actual affine charts and regular functions without a coefficient universe lift.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceDerivedModules`: `DerivedModules`,
  `derivedQCohProperty`, `derivedDualityModel` and its normalized `closed.tensor`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceAbsoluteQuasiSeparated`:
  `IsAbsolutelyQuasiSeparated` (absolute affine-pair criterion).
- `Sheaf.AlgebraicGeometry.SpaceDerivedTensorPullback`: `derivedTensorPullback`,
  with independently sized source and target localizations and its actual counit.
- `Sheaf.TraceFormula.SpaceQCSeparatedEtaleLocal`: `IsQuasiCompactPresheafMap`
  and `diagonalPresheafMap` (read their actual definitions at lines 38 and 49).
  Their existing definition-node owners are respectively
  `def-sfb-space-quasi-compact-presheaf-map` and
  `def-sfb-presheaf-map-separated-diagonal`; no conclusion of
  `quasiCompact_separated_etaleLocal` is used.
- `Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology`: `Point` topology,
  used by CompactSpace. Its public import is via absolute quasi-separatedness.

The seven added statement dependencies already have landed declarations. They name
infrastructure used to render existing clauses, not new mathematical assumptions:
`def-sfb-space-small-ringed-model`, `def-sfb-space-derived-module-calculus`,
`def-sfb-space-absolute-quasi-separated`, `def-sfb-space-derived-tensor-pullback`,
`def-sfb-space-quasi-compact-presheaf-map`,
`def-sfb-presheaf-map-separated-diagonal`, `def-a1-space-point-topology`.
No new node or dependency-record repair is needed, and the mathematical statement,
proof and proof_deps are unchanged.

Proof-only imports include
`Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses` for the tensor pullback
comparison, and `Sheaf.AlgebraicGeometry.SpaceQuasiCompactAffineTests` for scheme-test
compatibility. The perfectness definition and point topology are already public.
The remaining proof dependencies have no recorded Lean module at this reading:
`lem-sfb-space-derived-etale-chart-calculus`,
`lem-sfb-affine-countable-perfect-tensor`,
`lem-sfb-space-derived-hom-mayer-vietoris`,
`lem-sfb-ringed-hypercohomology-shifted-unit`,
`lem-sfb-space-qcqs-distinguished-square-induction`,
`lem-sfb-space-qcqs-source-products`,
`lem-sfb-space-change-base-to-integers`,
`lem-sfb-qc-space-affine-etale-atlas`.
Their future modules are not guessed; all are named in the proof docstring.

### Edge cases checked

- Empty X, U or affine chart: the corresponding zero module groups have singleton
  carriers, hence are countable. No nonempty scheme/chart/space premise is added.
- K = 0 or P = 0: derived tensor and all groups are zero. Countable means at most
  countable, so singleton carriers are included.
- i = 0, positive i, negative i: the integer shift gives H^i via H^0; there is no
  natural-number restriction or sign reversal.
- P = O_X[n] and finite-free retracts: these give shifted cohomology and direct
  summands of finite sums in the affine base case, so the countability conclusion
  matches the hypothesis. No single global strict representative is assumed.
- Unbounded K: the theorem has no truncation. The proof uses unbounded
  Mayer-Vietoris and a finite perfect factor, not an infinite-product assertion.
- An uncountable coefficient ring is allowed: the premise concerns sections of
  H^j(K), not of O_X or of P. In particular zero K works over any ring.
- S need not be quasi-separated. The absolute criterion for X was used; replacing
  it by the diagonal relative to S would have changed the meaning.
- Etale v need not be separated. Only quasi-compactness of its diagonal is required.
- The original section universe is retained by the recorded small affine model;
  wX and wU remain independent.

### Searches for an existing statement

All msearch invocations used group Q20 and this item id.

- `leanfinder`: "Countable hypercohomology of an unbounded quasicoherent complex
  tensored with a perfect complex on a quasi-compact quasi-separated algebraic space".
  Eight hits, including `CategoryTheory.Sheaf.H`, K-projectives and derived
  t-structure facts; no cardinal-countability theorem for this tensor.
- `loogle`: `"Countable", "homology"`: zero hits.
- `grep` through msearch in Mathlib/AlgebraicGeometry:
  `[Cc]ountable.*([Cc]ohom|[Hh]ypercohom)|([Cc]ohom|[Hh]ypercohom).*[Cc]ountable`:
  zero hits.
- `leansearch`: "Countable hypercohomology of a quasicoherent complex tensored
  with a perfect object on a quasi-compact quasi-separated algebraic space".
  Eight hits: CountableAB4 constructors/instances, cohomology-class construction,
  continuous-cohomology complex and bounded Ext localization; none states the item.
- `rg` in both `lean/Sheaf` and `lean/WeilConjectures` for
  `countable_hypercohomology|countableHypercohomology|[Cc]ountable.*hypercohom|hypercohom.*[Cc]ountable`:
  no hits. Broader countable/cohomology/perfect searches found derived countable
  coproduct/product infrastructure but no matching statement.
- `grep -rn` for this blueprint id in `lean/WeilConjectures`: no hits.
- The expected theorem name was checked in `dag/lean_names_upstream.json` as well:
  no declaration already owns it.

No statement fault or STATEMENT-DISPUTED issue was found. No definition was copied.

### Validation

`scompile.py Q20 lem-sfb-space-countable-hypercohomology` checked the delivered
module against the published server library in both its sandbox and final module
path; exit 0, no errors or warnings (12.4 s and 17.4 s in the recorded run).
All variables and universes are explicitly bound, with autoImplicit false.

## Repair self-check by Q20

H2 is repaired: `stmt_deps` cites both live `existing: true` definition owners,
and no longer cites `lem-trf-space-qc-separated-etale-local`. The shared import
`Sheaf.TraceFormula.SpaceQCSeparatedEtaleLocal` stays because it supplies their
recorded declarations. Quasi-separatedness still tests quasi-compactness of the
canonical diagonal; it does not assume the separatedness predicate also owned by
the diagonal node. The Lean signature equals `lean.statement` verbatim, and
`statement`, `proof`, `proof_deps` and all remaining node fields are unchanged
relative to the current shared node. No new nodes or dependency modules are added.
This is a self-check; the dispatcher's instruction forbids starting another agent.
The maintainer's independent reading in the return accepted every mathematical
clause and the complete proof docstring; only this dependency ownership needed repair.

## Second reading by Q20

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
