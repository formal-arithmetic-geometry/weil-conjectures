## Worker report

The module `Sheaf.AlgebraicGeometry.ProjectiveLogRegularResolution` states
`AlgebraicGeometry.exists_projective_log_regular_resolution`, with its entire proof `sorry`.
It defines no new object and copies no dependency definition. The accepted 2026-10-24
stage-1 split is preserved. Read the resolved stage-1 repair note and Q108 route decision;
the withdrawn attachment is not reused. The proof docstring follows the fresh eleven-step
split, rather than reinstating the historical normalized-blowup argument.

Hypothesis and conclusion correspondence:

| Node clause | Lean rendering |
| --- | --- |
| Excellent Noetherian commutative ring A | `(A : Type u) [CommRing A] [IsNoetherianRing A] (hA : IsExcellent A)` |
| B = Spec A | Every occurrence of the base is `Spec (.of A)`; no unrelated base scheme is quantified. |
| Locally Noetherian fs log scheme (V,M) | `V : FineSaturatedLogScheme.{u}` carries the scheme, local Noetherianity, log structure and fs-chart property. |
| V integral | `[IsIntegral V.scheme]` |
| V log regular | `(hV : V.IsLogRegular)` |
| Structure map V to B, of finite type | `f : V.scheme ⟶ Spec (.of A)`, `[LocallyOfFiniteType f] [QuasiCompact f]` |
| Quasi-projective in the finite-space convention | `hqp` quantifies `n : ℕ` and an `IsImmersion i` into `ℙ(ULift.{u} (Fin (n + 1)); Spec (.of A))`, with the structural factorization equal to f. |
| Finite saturated log blowup tower with target V | `T : SaturatedLogBlowupTower.{u}`, `T.level 0 = V`; its fields retain every center and its saturated universal property. |
| Underlying composite b | `p : ∀ i, EtaleLogHom (T.level i) V`, `HEq (p 0) (EtaleLogHom.id V)` and `(T.arrow i).CompEq (p i.castSucc) (p i.succ)`; b is `p (Fin.last T.length)`. |
| b projective in the closed-immersion finite-space convention | `IsHProjective (p (Fin.last T.length)).base` |
| b birational, meaning an isomorphism between dense opens | Existential opens U of the last level and W of V, an actual scheme isomorphism `e : U.toScheme ≅ W.toScheme`, `Dense U`, `Dense W`, and `U.ι ≫ b.base = e.hom ≫ W.ι`. |
| Y integral | `IsIntegral (T.level (Fin.last T.length)).scheme` |
| Y regular | `IsRegularScheme (T.level (Fin.last T.length)).scheme` |
| b log etale | `(p (Fin.last T.length)).IsLogEtale` |
| For every locally Noetherian fs D and every log-smooth V to D, the composite is log smooth | `∀ (D : FineSaturatedLogScheme.{u}) (g : EtaleLogHom V D), g.IsLogSmooth → (b.comp g).IsLogSmooth`; D's local Noetherianity is already bundled. |
| Length-zero towers allowed | No positivity restriction on `T.length`; the initial identity and terminal map coincide when length is zero. |

All universes and variables are explicit (`set_option autoImplicit false`). Projective space
uses `ULift.{u} (Fin (n+1))` so the finite coordinate type has exactly the scheme universe
without restricting n or u. There is no coefficient characteristic or field restriction.

Dependency declarations read and used:

- `Sheaf.AlgebraicGeometry.FineSaturatedLogBlowup`: `FineSaturatedLogScheme`,
  `FineSaturatedLogScheme.IsLogRegular`, `EtaleLogHom`, `EtaleLogHom.CompEq`,
  `SaturatedLogBlowupTower`, whose arrows carry `IsSaturatedLogBlowup`.
- `Sheaf.AlgebraicGeometry.FSLogSmoothEtale`: `EtaleLogHom.IsLogSmooth`,
  `EtaleLogHom.IsLogEtale`. Read the canonical monoid-chart comparison and kernel/cokernel
  predicates underlying these definitions.
- `Mathlib.AlgebraicGeometry.Properties`: `AlgebraicGeometry.IsIntegral`.
- `Sheaf.AlgebraicGeometry.IsRegularScheme`: `AlgebraicGeometry.IsRegularScheme`, namely
  `IsLocallyNoetherian X ∧ IsRegular X`, including the node's local Noetherian condition.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`; the quasi-compact
  half is `QuasiCompact` from `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`.
- `WeilConjectures.AlgebraicGeometry.Morphisms.Projective`: `IsHProjective`, the requested
  finite projective-space convention, rather than the arbitrary-projective-bundle convention.
- `Sheaf.RingTheory.ExcellentRing`: `IsExcellent`, including quasi-excellence and universal
  catenarity; its Noetherian hypothesis is also made explicit as in the node.
- `Mathlib.AlgebraicGeometry.Scheme`: `Spec`.
- `Sheaf.AlgebraicGeometry.LogMorphismOperations`: `EtaleLogHom.id`, `EtaleLogHom.comp`.
  The landed definition node `def-per-log-morphism-identity` owns `EtaleLogHom.id`;
  `def-per-log-morphism-composition` owns `EtaleLogMap.comp` and its concrete fs wrapper
  `EtaleLogHom.comp`. Both definition nodes are cited in `stmt_deps` under brief-stage2
  §5's authorization to cite existing landed nodes. The theorem node
  `lem-sfb-log-morphism-operations` is not a statement dependency: no theorem conclusion
  from it is used in the signature. No dependency module is needed.

Every already-recorded proof-dependency module is imported with ordinary `import` unless
already public for a statement dependency. The following proof dependencies have no Lean
record or Mathlib match yet and hence supply no module to import:
`lem-trf-log-ideal-chart-lifting-criterion`,
`lem-trf-principal-log-ideal-tautological-polarization`,
`lem-sfb-space-relative-ampleness-fpqc-descent`,
`lem-trf-formal-chart-geometric-regularity`.
They remain in the proof plan and proof_deps unchanged; they are not needed to TYPE this
statement and no proof is attempted here.

Sources: opened the local ILO PDF with pdftotext. Read VIII 3.4.6(i), 3.4.8--3.4.9
and XVI 3.7 (the latter explicitly calls the final map log-etale, projective and birational
with regular source). No new source-based correction of the node is needed.

Edge cases checked before writing: V empty is excluded by the stated integrality, not by
an added hypothesis. A zero ring has empty spectrum, so admits no integral V with the supplied
structure map. Length zero has no arrows or centers, and its sole p is the identity; this
allows regular inputs needing no blowup. The projective-space parameter n=0 is allowed.
Trivial log structure gives characteristic rank zero and regular underlying scheme, so
identity is an admissible case. No generic-point-only condition replaces the required dense
open isomorphism. Mixed and positive characteristic are retained. D may be empty; there is
then no map from nonempty V. All conclusions refer to the same chosen tower, for every D
and g, rather than choosing a new tower for each g.

Searches made:

- `msearch.py leanfinder`: “An integral log regular scheme quasi-projective over an excellent
  affine base has a projective birational saturated log blowup tower with regular total
  space”. Eight hits: ordinary Proj properness, normalization and spectrum facts; no match.
- `msearch.py loogle`: `IsHProjective, IsQuasiProjective, IsBirational,
  SaturatedLogBlowupTower`. Zero hits; unknown identifier IsHProjective.
- `msearch.py grep`: `SaturatedLogBlowup|LogResolution|IsQuasiProjective|IsBirational`,
  Mathlib AlgebraicGeometry. Zero hits.
- `rg` of `lean/WeilConjectures` and `lean/Sheaf` for log resolution, projective log regularity,
  birationality and quasi-projectivity. The exact node id and proposed declaration are
  absent. Read `Sheaf.TraceFormula.LogRegularDesingularization`: its theorem is only for
  divisorial pairs over an algebraically closed field, gives properness rather than this
  finite-space projectivity, and does not state the present tower/log-etale/universal
  log-smooth conclusions. It is not the same statement. Upstream `IsQuasiProjective` is
  restricted to a field; the base here is an arbitrary excellent ring. The present hqp
  directly writes the node's existential immersion clause without introducing a duplicate
  quasi-projectivity definition. `GabberModification.QuasiProjective` has the same general
  existential clause but lives in the large four-stage equivariant modification interface;
  no such additional structure is needed or assumed here.
- Read all statement dependency node statements, records and recorded declaration sources;
  the CompactObject example is withdrawn and its node points to the upstream module,
  which was read instead. No names or definitions were copied from the withdrawn file.

No STATEMENT-DISPUTED condition and no statement correction.

## Second reading by Q63

A separate rereading of the node and the completed signature checked every row above.
In particular, it checked the initial p is the identity LOG map (not just the identity
underlying scheme map), each recurrence is `CompEq` in the correct order, both opens
are dense, the isomorphism commutes with b, and the log-smooth clause quantifies D and g
AFTER the single chosen tower. It also checked `IsRegularScheme` includes local
Noetherianity and `IsHProjective` uses a finite projective-space embedding. No mathematical
mismatch was found. This is the worker's own second pass; the dispatcher instruction
forbids starting other agents, and independent review belongs to the maintainer.

Validation: prescribed `scompile.py` succeeded for both the sandbox and final library
module with no errors or unexpected warnings. `deliver2.py --no-push` passed the
server preflight and per-file compile: `OK (dry run): commit 049a85330c5 passes the
preflight and compiles; nothing pushed`. Only the report, item node and module were staged.

## Returned delivery repair (H2)

The independent review of immutable head `7c0ce40d52e8` returned exactly one point:
the signature uses the definitions `EtaleLogHom.id` and `EtaleLogHom.comp`, not the
conclusion of the theorem node `lem-sfb-log-morphism-operations`. Replaced that added
statement dependency with the now-landed definition nodes
`def-per-log-morphism-identity` and `def-per-log-morphism-composition`, and corrected
the dependency list above. Read both current node records and the full concrete fs
identity/composition definitions in `LogMorphismOperations.lean` (lines 140 and 145).
Their owning records include exactly these declarations.

Compared the retained returned node with current main: only `lean` and `stmt_deps`
differed. Rebased the sandbox node on the current main record, preserving all other
fields, and reapplied the Lean attachment with the current UTC date and the two
correct definition dependencies. The prescribed delivery wrapper refreshes the Git
base and constructs the delivery commit. The Lean module and `lean.statement` are
unchanged from the returned delivery, as requested. No theorem, proof plan, mathematical
statement, hypothesis or conclusion was changed. The worker's second reading checked
that the final statement dependency list contains both definition owners and excludes
the theorem node. Fresh prescribed `scompile.py` passed without errors or unexpected warnings.
`deliver2.py --no-push` passed preflight and per-file compilation:
`OK (dry run): commit 507ba25a3f1 passes the preflight and compiles; nothing pushed`.
