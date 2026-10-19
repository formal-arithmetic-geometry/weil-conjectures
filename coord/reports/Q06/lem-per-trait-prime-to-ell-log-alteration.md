## Worker report

This is a stage-2 statement delivery, not a stage-1 split. The shared item is split and
maintainer-reviewed as a stage-1 node, but has no Lean record. The retained sandbox initially
contained only dispatcher briefs. I did not reuse or re-deliver the stage-1 split.

`Sheaf.AlgebraicGeometry.TraitPrimeToEllLogAlteration` states
`AlgebraicGeometry.exists_trait_primeToEll_log_alteration`. The two helper declarations
`uniformizerLogChartGroupMap` and `TraitUniformizerLogChart` belong to the same uniformizer-chart
notion expressly described inline in the item. They have actual data and no postponed proofs.
The only theorem is the item, with proof `sorry`. The node is unchanged outside `lean`.

Source read: ILO, Travaux de Gabber, Exposé XVI §3.7, printed pp.254--255, including the
constant-field normalization, four semistable G-alteration bullets, H-Sylow quotient T,
equivariant modification, log resolution and the final prime-to-ell degree. The formal
statement stops before the purity application. I read the item's eight proof steps and
retained them in its theorem docstring.

Hypothesis and clause correspondence:

- Prime ell: `(ell : ℕ) (hell : ell.Prime)`.
- Trait S: `R : CommRingCat.{u}`, `[IsDomain R]`, `[IsDiscreteValuationRing R]`, with
  `S = Spec R`. Mathlib's DVR is a nonfield local PID, equivalent to the node's
  Noetherian one-dimensional local domain with principal maximal ideal.
- Completeness: `[IsAdicComplete (IsLocalRing.maximalIdeal R) R]`.
- Strict henselianity: `[IsStrictlyHenselianLocalRing R]`, the existing upstream class
  extending HenselianLocalRing and separably closed residue field. The upstream docstring
  and full class signature were read.
- Mixed characteristic: `[CharZero (FractionRing R)]` and `hchar` giving prime positive
  characteristic of the residue field. This includes every mixed-characteristic DVR.
- Invertibility of ell on S: `hinv : IsUnit (ell : R)`.
- Integral regular X: `[IsIntegral X]` and `hreg : IsRegularScheme X`. The latter is the
  recorded conjunction `IsLocallyNoetherian X ∧ IsRegular X`, including Noetherianity.
- Flat finite-type structure map: `s` with `[Flat s]`, `[LocallyOfFiniteType s]`, and
  `[QuasiCompact s]`.
- Quasi-projectivity of X: `hqp`, an `IsImmersion` into projective space indexed by
  `ULift (Fin (N+1))`, with equality of the structural composite to s.
- Finite dominant extension of traits: existential `A`, its domain and DVR instances,
  `t : Spec A ⟶ Spec R`, and `IsFinite t ∧ IsDominant t`. Completeness and strict
  henselianity of T are not added as independent conclusions, since the item only asks
  for a finite extension of traits (they follow from the construction).
- Integral regular Y and its fs structure: `Y : FineSaturatedLogScheme`, together with
  `IsIntegral Y.scheme ∧ IsRegularScheme Y.scheme`. The bundle carries the existing
  EtaleLogStructure, fs charts, and local Noetherianity, without any hollow definition.
- Finite type over T and S: the two conjunctions for q and q ≫ t of locally finite type
  and quasi-compactness.
- Quasi-projectivity over T and S: the two existential natural-number projective-space
  embeddings by locally closed immersions, with their structural-map equalities.
- S-morphism f: `f ≫ s = q ≫ t`.
- Projectivity and dominance: `IsHProjective f ∧ IsDominant f`. The canonical upstream
  IsHProjective is the finite-coordinate closed-immersion factorization, not the weaker
  convention involving an arbitrary projective bundle.
- Generically finite étale: an explicitly nonempty open U with `IsFinite (f ∣_ U)`
  and `Etale (f ∣_ U)`.
- Degree: `0 < d ∧ ¬ell ∣ d` and `f.fiberDegree (genericPoint X) = d`.
  For integral Y and X, dominance and generic finite étaleness make this precisely
  the finite function-field degree [k(Y):k(X)]. FiberDegree.lean's generic-point
  comparison was read; using the canonical fibre degree avoids an arbitrary algebra
  structure on the function fields.
- Canonical trait log structure: an irreducible π in the DVR A, with a global monoid
  map b from the free monoid ℕ to Y's log sections sending n structurally to q*(π^n).
  A morphism from the associated canonical trait log structure is exactly this lift:
  the log unit condition supplies its unit part. There is no arbitrary independent
  log structure on T. Irreducibility is Mathlib's uniformizer convention.
- Log smoothness with the specified charts: at each geometric point there is an
  étale neighbourhood c.V with a lift of that point. c.P is fs, c.chart is an actual
  log chart, and `compatibility` restricts the same b to that chart. The base monomials
  are explicitly π^n, the source monomials explicitly the structural images of c.chart,
  and the comparison map has the two prescribed pullback projections. `gp_injective`
  is injectivity on group completions. `torsion_finite` and `torsion_invertible` give
  the finite torsion subgroup of the actual group cokernel and invertibility of its
  cardinality at every point. `smooth` is the existing scheme Smooth predicate.
  Thus this is the item's fixed ℕ-chart form, not the older torsion-free chart predicate.
- No purity conclusion occurs.

Dependency declarations used, with source signatures and docstrings inspected:

- Sheaf.AlgebraicGeometry.FineSaturatedLogBlowup: EtaleLogStructure,
  EtaleLogStructure.IsChart, FineSaturatedLogScheme; these reuse monoid sheaves and the
  actual associated-chart stalk pushout. The helper calls the recorded IsChart.
- Sheaf.AlgebraicGeometry.IsRegularScheme: AlgebraicGeometry.IsRegularScheme.
- Mathlib.AlgebraicGeometry.Morphisms.Smooth: AlgebraicGeometry.Smooth.
- Mathlib.AlgebraicGeometry.Morphisms.Etale: AlgebraicGeometry.Etale.
- Mathlib.AlgebraicGeometry.Properties: AlgebraicGeometry.IsIntegral.
- Mathlib.AlgebraicGeometry.Morphisms.Flat: AlgebraicGeometry.Flat.
- Mathlib.AlgebraicGeometry.Morphisms.FiniteType and QuasiCompact:
  AlgebraicGeometry.LocallyOfFiniteType and AlgebraicGeometry.QuasiCompact.
- Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion and Immersion:
  AlgebraicGeometry.IsClosedImmersion and AlgebraicGeometry.IsImmersion.
- Mathlib.AlgebraicGeometry.Scheme: AlgebraicGeometry.Spec and Spec.map.
- WeilConjectures.AlgebraicGeometry.ProjectiveSpace: ProjectiveSpace and its projection;
  WeilConjectures.AlgebraicGeometry.Morphisms.Projective: IsHProjective.
- WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree: Scheme.Hom.fiberDegree,
  with its generic-point field-degree interface.
- WeilConjectures.Mathlib.RingTheory.Henselian: IsStrictlyHenselianLocalRing;
  Mathlib.RingTheory.DiscreteValuationRing.Basic: IsDiscreteValuationRing;
  Mathlib.RingTheory.AdicCompletion.Basic: IsAdicComplete.
- Mathlib.GroupTheory.Torsion: CommGroup.torsion; the cokernel uses the range of the
  actual Grothendieck-group map. No duplicate log structures or chart pushouts were added.

The proof-route imports retain every stated proof dependency, including
Sheaf.RingTheory.CompleteLocalExcellent and HProjectiveComposition. The geometric inputs
without a recorded declaration are named in the proof docstring and are not assumed as
extra hypotheses. This item does not need to state their proofs or their statements in
order to state its own conclusion.

Edge cases checked: integrality excludes empty X and Y; d is expressly positive, so an
empty generic cover or degree zero cannot satisfy the conclusion. Degree one is allowed.
The generic-only X case is allowed; b can send the uniformizer to a unit and its associated
chart is then trivial. A trivial torsion cokernel has cardinality one and is allowed.
Positive residue characteristic different from ell follows from hinv. Charts need not
have torsion-free cokernel, so tame ramification is retained. Dimension-zero projective
spaces use one homogeneous coordinate; arbitrary u is retained in rings, schemes,
monoids and geometric-point fields. No universe equality beyond the shared scheme
universe or unexplained field extension is imposed. No statement dispute found.

Searches actually run:

- msearch.py leanfinder: "Projective alteration of prime to ell degree of a regular
  scheme over a complete strictly henselian mixed characteristic discrete valuation
  ring with a log smooth regular source": eight hits, smooth morphisms and projective
  spectrum valuative criteria, none the item.
- msearch.py loogle: `"log smooth"`: zero hits.
- msearch.py grep: `LogSmooth|logSmooth|primeToEll.*alteration` in AlgebraicGeometry:
  zero hits.
- rg in the full upstream WeilConjectures tree for this item's id: no hits.
- rg in upstream WeilConjectures and side lean/Sheaf for PrimeToEll, primeToEll,
  trait alteration, LogAlteration and Prime Alteration: only the more general
  alteration-topology/uniformization and plurinodal statements, not this theorem.
- Read LogSmoothLogRegular.lean and its InjectiveFSLogChart in full: its cokernel
  is required torsion-free, so it cannot represent the item's invertible torsion.
  Reused the owning log structures and monoid algebra; supplied only this item's
  fixed-uniformizer chart helper rather than redefining general log smoothness.
- rg for TraitUniformizerLogChart, uniformizerLogChartGroupMap and
  exists_trait_primeToEll_log_alteration across side sources, upstream sources and
  dag/lean_names_upstream.json: no pre-existing declarations.

Validation: a scratch copy retaining every public statement import and omitting only
proof-route imports compiled cleanly twice (sandbox and library modes, 4.9 and 5.2 s)
through scompile.py. This caught and repaired an abbreviated CommRingCat.ofHom reference.
The full delivered module is still subject to the required complete-module compilation;
compile.log records its result. No build, direct git command, shared-source edit, launcher
edit, or sub-agent was used.

## Tool failure

The complete delivered module was compiled twice through scompile.py after the diagnostic
repair, and the prescribed `deliver2.py Q06 lem-per-trait-prime-to-ell-log-alteration --no-push`
was run. Both full-module calls returned code 75 with `INFRASTRUCTURE RETRY (stale live olean)`
for Sheaf.RingTheory.CompleteLocalExcellent. The dry run returned code 1 with the same
missing published object file and `COMPILE FAILED on the server, nothing pushed`.
The source exists and was read with `scompile.py --source`; the compiled published live
artifact does not exist. The wrapper explicitly says this is not the delivery's fault
and to retry after the next published live build. The required proof-route import is
retained. The scratch diagnostic is not submitted as the module and is not used to claim
full delivery validation. No push command was run because the dry run did not pass.
The module and node record are prepared for the next ordinary dry-run retry.

## Recovery retry, 2026-10-19

Read the retained packet and ran the prescribed dry run first. It again failed with
`INFRASTRUCTURE RETRY (stale live olean)` for the missing published
`Sheaf.RingTheory.CompleteLocalExcellent.olean`. A diagnostic compilation excluding
proof-route imports passed in sandbox and library modes (4.1 and 4.6 seconds), but
that cannot validate a stage-2 delivery: stages/2-statements.md section 3 rule 7 and
coord/brief-stage2.md section 3 require those imports. All original proof-route
imports were restored. The live source was re-read with
`scompile.py --source Sheaf.RingTheory.CompleteLocalExcellent`; it exists and
states the recorded theorem. A second prescribed dry run with all imports restored
failed with the same missing published object file (0.7 seconds), before preflight.
No delivery push occurred. The retained module and node remain ready for retry when
the published live build supplies the required artifact.

## Second reading by Q06

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
