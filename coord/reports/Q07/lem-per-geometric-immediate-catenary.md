## Worker report

`Sheaf.AlgebraicGeometry.GeometricImmediateCatenary` states
`AlgebraicGeometry.Scheme.geometricImmediate_iff_zariskiImmediate_of_universallyCatenary`.
Its sole proof is `sorry`. No definitions, helper theorems, or new nodes are introduced.
The node's statement and NJ's independently reviewed proof plan are preserved. NJ's
stage-1 split has `reviewed`, but the current node has no `lean` or `reviewed_lean`:
this delivery supplies the stage-2 statement and does not split the node again.

I read ILO, Travaux de Gabber, Expose XIV, Definitions 2.1.1--2.1.2, Proposition 2.1.3,
and Proposition 2.1.4 with its proof (printed pp. 209--211; PDF pages 215--217).
Immediately after Definition 2.1.1 the source identifies a morphism of strict
localizations with a geometric point of the target strict localization over the source
geometric point. The statement uses this equivalent presentation and retains the lift.

Hypotheses, individually:

- `X : Scheme.{u}` is an arbitrary scheme.
- `[IsNoetherian X]` means a finite affine cover by spectra of Noetherian rings, by
  Mathlib's `isNoetherian_iff_of_finite_iSup_eq_top`.
- `hcat : ∀ U : X.affineOpens, IsUniversallyCatenary Γ(X, U)` requires universal
  catenarity on EVERY affine open, using the bounded saturated-chain definition from
  `def-exc-excellent-ring`. Its Noetherian conjunct already follows from Noetherianity
  of X and does not change the hypothesis.
- `y x : X`, `hne : y ≠ x`, and `hyx : y ⤳ x` give the distinct points and x in the
  closure of y. No separatedness, regularity, base field, or coefficient is assumed.

Clauses, individually:

- `∀ z : X, y ⤳ z → z ⤳ x → z = y ∨ z = x` states absence of an intermediate point.
  The specialization and distinctness hypotheses are explicit outer binders.
- The FIRST equivalence gives the dimension-one reformulation in condition (1).
  The actual reduced closure Z is
  `(IdealSheafData.vanishingIdeal (Closeds.closure ({y} : Set X))).subscheme`.
  Its witness `zx` maps to x under `Z`'s closed immersion, and
  `ringKrullDim (Z.presheaf.stalk zx) = 1` means dimension one of O_{Z,x}.
  There is exactly one such point zx: the immersion is injective, its image is closure
  of y, and `hyx` puts x in that image. The existential therefore introduces neither
  an additional assumption nor an arbitrary local-ring model.
- The SECOND equivalence states condition (1) iff condition (2). The existential
  algebraically closed field Ωx and `barX : Spec (.of Ωx) ⟶ X` give a geometric point
  with image x. The existential algebraically closed field Ωy and
  `a : Spec (.of Ωy) ⟶ strictHenselizationScheme barX` give a geometric specialization
  in the presentation of ILO Definition 2.1.1. Its image under the canonical structural
  map is y. `topologicalKrullDim (closure {a (IsLocalRing.closedPoint Ωy)}) = 1`
  gives the dimension of the reduced closure: reduction preserves the underlying
  topological space and dimension. This is the closure of the actual lifted point,
  rather than a component of the whole strict localization.
- The FINAL conjunct ranges over EVERY specified geometric lift `a` above y, with
  target geometric point above x and closure dimension one. For every affine open U
  and every p/q representing y/x through `U.2.fromSpec`, it asserts
  `p.asIdeal < q.asIdeal` and excludes every prime strictly between them. This gives
  saturation, with orientation p ⊊ q, on any affine neighbourhood of x. Such a
  neighbourhood also contains y, since opens are stable under generalization.
- Both geometric fields have object universe u, as in the recorded geometric-point
  and strict-henselization interfaces. The relevant residue fields and their algebraic
  closures exist in u, so the existential quantification excludes no scheme or point.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`.
- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`; scheme Noetherianity is
  `AlgebraicGeometry.IsNoetherian` from `Mathlib.AlgebraicGeometry.Noetherian`.
- `Sheaf.RingTheory.ExcellentRing`: `IsUniversallyCatenary`, `IsCatenaryRing`,
  `IsPrimeChain`, `IsSaturatedPrimeChain`, and the excellence predicates.
- `Mathlib.RingTheory.KrullDimension.Basic`: `ringKrullDim`.
- `Mathlib.FieldTheory.IsAlgClosed.Basic`: `IsAlgClosed`. Geometric points are inline
  `Spec (.of Ω) ⟶ X`, as required by the recorded geometric-point node. I also read
  `Scheme.SpecToEquivOfField` in `Mathlib.AlgebraicGeometry.ResidueField`.
- `Sheaf.AlgebraicGeometry.StrictHenselization`: `Scheme.strictHenselizationScheme`
  and its coordinate-ring construction `Scheme.strictHenselizationRing`.
- `WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMap`:
  `Scheme.strictHenselizationStructuralMap`. The recorded upstream module was read
  using `scompile.py --source`; its map is the canonical common composite of the
  limit projections, characterized by `exists_strictHenselizationStructuralMap`.
- `Mathlib.Topology.KrullDimension`: `topologicalKrullDim` on the closure subspace.
- `Mathlib.AlgebraicGeometry.IdealSheaf.Basic` and `.Subscheme`:
  `Scheme.IdealSheafData.vanishingIdeal`, `.subscheme`, and `.subschemeι` are the
  existing construction of the reduced induced closure, without any private copy.

Two already landed records are added to `stmt_deps` under brief-stage2 section 5,
STMT_DEPS MAY GAIN LANDED NODES: `def-weil-pbc-strict-henselization-structural-map`
and `def-kun-topological-krull-dimension`. Their statements, Lean records and declaration
docstrings were read. No dependency record requires repair. The proof dependency
`lem-per-immediate-specialization-criterion` has no Lean record, so there is no module
to import for it; its source-based proof plan is retained in the docstring. The other
proof dependency, ring Krull dimension, is imported.

Edge cases checked before writing:

- Empty scheme and a field spectrum admit no distinct specialization satisfying the
  hypotheses; there is no silently strengthened nonemptiness assumption.
- A DVR with generic y and closed x has no intermediate point, reduced-closure local
  dimension one, and dimension-one strict-local branches.
- For A² at the origin with y generic in A², intermediate height-one points exist and
  the local dimension is two: all three conditions are false.
- For A² at the origin with y generic in a line, the reduced line has local dimension
  one and the conditions hold, despite the whole strict localization having dimension
  two. This checks against the whole-space component mistake returned to Q05.
- Nilpotents are removed only in the prescribed reduced closure. The ambient scheme
  need not be reduced or regular. Distinctness excludes reflexive specializations.
- Saturation is universal in both the geometric lift and affine chart, not merely
  existence of one chart where the prime inclusion is saturated.

Searches for an existing statement (2026-10-18):

- `msearch.py leanfinder`: “On a universally catenary Noetherian scheme a geometric
  specialization has one-dimensional closure in a strict localization if and only if
  there is no intermediate point in the specialization order”: 8 hits, including
  `Scheme.le_iff_specializes`, `Scheme.range_fromSpecStalk`, and
  `IsLocalRing.specializes_closedPoint`; no theorem matching the node.
- `msearch.py leansearch`: “On a Noetherian universally catenary scheme immediate
  Zariski specializations are exactly geometric specializations whose image has
  one-dimensional closure in a strict localization”: 8 hits, including
  `specializes_iff_mem_closure` and `PrimeSpectrum.le_iff_specializes`; no equivalence
  involving strict-local dimension or saturated chains.
- `msearch.py loogle`: `AlgebraicGeometry.Scheme.le_iff_specializes, ringKrullDim`:
  0 hits.
- `msearch.py grep`: `[Cc]atenary|[Ii]mmediate.*[Ss]pecial|[Ss]pecial.*[Ii]mmediate`:
  0 Mathlib hits.
- `rg` of upstream `WeilConjectures` for catenary/immediate-specialization patterns
  and the exact item id: no matching statement. `rg` of `lean/Sheaf` found the
  excellence definition and affine-cover catenarity theorem, neither this equivalence
  nor its saturation corollary. The proposed declaration name is absent from both
  libraries. Related geometric strict-local lift modules were read; no notion from
  them is redeclared.

No mathematical statement is disputed or corrected. The first compile found that the
recorded `strictHenselizationScheme` differs from upstream `strictLocalization` in the
published library. Using the recorded canonical structural-map declaration repairs
that mismatch with no transport assumption or arbitrary map.

Validation: the final module compiled cleanly through `scompile.py`, both as a sandbox
file and at its intended library module name. There were no errors or warnings.

## Second reading by Q07

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
