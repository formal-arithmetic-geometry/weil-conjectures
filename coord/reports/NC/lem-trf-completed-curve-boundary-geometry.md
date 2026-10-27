## Worker report

The module `Sheaf.AlgebraicGeometry.CompletedCurveBoundaryGeometry` states
`AlgebraicGeometry.Scheme.completed_curve_boundary_geometry`, with `sorry` as its entire
proof. It introduces no new definition, axiom, structure or helper theorem. The DAG node is
unchanged except for its `lean` record.

Hypotheses, matched to the node:

- Algebraically closed field: `(k : Type u) [Field k] [IsAlgClosed k]`.
- Integral proper finite-type k-scheme: `(Z : Scheme.{u}) [IsIntegral Z]`,
  `(p : Z ⟶ Spec (.of k)) [IsProper p]`. Mathlib properness includes
  `LocallyOfFiniteType p`; its universal closedness implies `QuasiCompact p`, so both
  clauses of finite type follow without redundant instance binders. The first compile
  detected the redundant locally-finite-type instance, which was removed.
- Dimension one: `hdim : topologicalKrullDim Z = 1`.
- Finite marked set partitioned into regular and nodal closed points: `Sreg Snode : Closeds Z`,
  with `hfinite` for their union, `hclosed` placing their union in `closedPoints Z`, and
  `hdisjoint : Disjoint Sreg Snode`. The set called S in the node is their union. Using
  bundled closed subsets adds no restriction because every finite set of closed points,
  and each subset of it, is closed.
- Smoothness of Z minus S: `hsmooth : Smooth
  (Scheme.Opens.ι (X := Z) (Sreg ⊔ Snode).compl ≫ p)` uses the actual open immersion.
- Regular marked completions: `hreg` gives an isomorphism from the maximal-ideal adic
  completion of each marked stalk to `MvPowerSeries (Fin 1) k`.
- Nodal marked completions: `hnode` gives an isomorphism to
  `MvPowerSeries (Fin 2) k ⧸ Ideal.span {X 0 * X 1}`.
- Both completion hypotheses explicitly preserve scalars: the scalar a is sent through
  `ΓSpecIso.inv`, `p.appTop`, the germ map, and `AdicCompletion.of`, and its image is the
  constant power series (modulo uv for nodes). Thus these are k-algebra isomorphisms,
  not just ring isomorphisms. Ring equivalences between these local rings preserve maximal
  ideals and all their powers, hence preserve the complete local topologies automatically.
  The Fin 1 power-series ring is exactly the one-variable formal power-series model of the
  recorded power-series definition.

Conclusions, matched clause by clause:

- N and nu are the canonical `Z.normalization` and `Z.fromNormalization` of the recorded
  normalization definition, in its function field. There is no arbitrary choice of a
  normal scheme or a morphism called normalization.
- Finiteness is `IsFinite Z.fromNormalization`.
- Integrality is `IsIntegral Z.normalization`.
- Properness and smoothness are `IsProper (Z.fromNormalization ≫ p)` and
  `Smooth (Z.fromNormalization ≫ p)`.
- Connected curve is `IsConnectedCurve (Z.fromNormalization ≫ p)`, including the recorded
  separatedness, finite type, nonempty connectedness and dimension exactly one.
- Exact nonsmooth locus: `∀ z : Z, z ∉ p.smoothLocus ↔ z ∈ Snode`.
- Isomorphism off the nodes: `IsIso (Z.fromNormalization ∣_ Snode.compl)`.
  Since the partition is disjoint, this open includes every point of Sreg.
- The effective divisor is an actual finitely supported natural-valued coefficient
  function `E : closedPoints Z.normalization →₀ ℕ`. Its coefficient at x equals one if
  nu(x) is in Sreg union Snode, and zero otherwise. This is the effective part of the
  existing integer-valued divisor group, with no repeated points or hidden multiplicities.
- Its ideal is `B = Divisor.idealSheaf E`, the existing product of reduced point ideals
  raised to the specified coefficients. The independent equality
  `B = ((IdealSheafData.vanishingIdeal (Sreg ⊔ Snode)).comap
  Z.fromNormalization).radical` identifies it with the reduced scheme inverse image of S.
- Effective Cartier is `B.IsInvertible`, the canonical effective-Cartier ideal predicate.
- Exact support is `(B.support : Set Z.normalization) =
  Z.fromNormalization ⁻¹' (Sreg ⊔ Snode : Closeds Z)`; the next conjunct says it is finite.
  Together with B being the product of reduced closed-point ideals, this also says all its
  support points are closed.
- At each support point x, every affine neighborhood U has
  `Ideal.map (Z.normalization.presheaf.germ U x hx).hom (B.ideal U) =
  IsLocalRing.maximalIdeal (Z.normalization.presheaf.stalk x)`.
  This image is precisely the stalk ideal, since the germ map is localization and the
  ideal is quasi-coherent. Quantifying over neighborhoods is a coordinate presentation
  of the asserted stalk equality, not a stronger assertion about sections.
- The associated line is exactly `Modules.dual B.toModules`, and its invertibility is
  stated using the recorded `Modules.IsInvertible`.
- The canonical divisor section is the actual inclusion `B.toModulesι`, viewed as a section
  of the dual via `SheafOfModules.homObjSectionsEquiv`, then as a map from the unit via
  `unitHomEquiv.symm`. The final conjunct makes its restriction by `overFunctor` to
  `B.support.compl` an isomorphism. Its inverse is the canonical trivialization: when the
  ideal is O, the inclusion corresponds to 1, and the inverse evaluates a homomorphism at
  1. This specifies the canonical trivialization, not mere existence of an arbitrary one.
- There is no ambient curve, ambient embedding, LCI structure or adjunction line among the
  parameters.

Dependency declarations used (public statement imports):

- `Mathlib.FieldTheory.IsAlgClosed.Basic`: `IsAlgClosed`, the algebraically closed clause
  of `def-weil-algebraic-closure`'s Mathlib match.
- `Mathlib.AlgebraicGeometry.Properties`: `AlgebraicGeometry.IsIntegral` (available through
  normalization), for `def-pc-integral-scheme`.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `IsProper`; finite type is its
  `LocallyOfFiniteType` parent together with inferred `QuasiCompact`, as recorded by
  `def-weil-proper-morphism` and `def-weil-finite-type-morphism`.
- `Mathlib.Topology.KrullDimension`: `topologicalKrullDim`.
- `Mathlib.Topology.JacobsonSpace`: `closedPoints`, available through Curve.Divisor.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `Smooth`, `Scheme.Hom.smoothLocus`.
- `WeilConjectures.Mathlib.AlgebraicGeometry.Normalization`: `Scheme.normalization`,
  `Scheme.fromNormalization`, exactly `def-sc-normalization`.
- `WeilConjectures.AlgebraicGeometry.Curve`: `IsConnectedCurve`, extending `IsCurve`,
  exactly the connected-curve clause of `def-sc-curves`.
- `WeilConjectures.AlgebraicGeometry.EffectiveCartier`: `Modules.dual`,
  `IdealSheafData.toModules`, `IdealSheafData.toModulesι`, and the effective Cartier
  ideal/dual-line interpretation of `def-pc-divisor-line-bundle`.
- `Mathlib.RingTheory.AdicCompletion.Algebra`: `AdicCompletion`, `AdicCompletion.of`.
- `Mathlib.RingTheory.MvPowerSeries.Basic`: `MvPowerSeries`, `MvPowerSeries.X`,
  `MvPowerSeries.C`.
- `Mathlib.AlgebraicGeometry.Morphisms.Finite`: `IsFinite`.
- `WeilConjectures.AlgebraicGeometry.Curve.Divisor`: `Scheme.Divisor`, which is listed
  in `def-sc-divisor`'s lean.declarations; its effective coefficient model and the canonical
  ideal construction are in `Curve.DivisorIdealSheaf`, `Divisor.idealSheaf`. The statement
  needs the divisor, not the separate function-field-section construction
  `Divisor.moduleOfSmoothConnectedCurve`; hence it uses the recorded divisor declaration
  directly, without importing or duplicating the older Sheaf divisor-module implementation.

The plain proof imports cover every already-stated proof dependency: Mathlib Noetherian
and QuasiFinite (finite-type Noetherianity and finite fibres),
`PowerSeriesFieldCohenRegularComplete.power_series_field_cohen_regular_complete` in its
`MvPowerSeries` namespace, `AdicCompletion.isRegularLocalRing_iff`,
`IsRegularLocalRing.isDomain`, `IsRegular.of_smooth`, `smooth_of_isRegular`,
`Scheme.normalization_properties`, `IsRegularScheme`,
`regular_normal_and_normal_decomposition`, the point-Cartier declarations in Curve.ClosedPoint,
and `Scheme.Modules.IsInvertible`. Definitions used only in the proof (regular schemes
and invertible modules) retain their recorded modules as proof imports. Normalization
properties' current source signature differs in packaging from the older node record, but
its actual conclusions give all the uses made here; no dependency repair is needed.

Edge cases checked:

- S empty: both closed sets may be bottom. E is zero, B is the unit ideal, the boundary
  complement is all N, and the final canonical trivialization is global.
- Snode empty but Sreg nonempty: normalization is an isomorphism globally; marked smooth
  points still appear once in the boundary. Marked points are not assumed singular.
- Sreg empty: only node-completion assumptions remain. A self-node on an integral curve
  is allowed: only the completion, not the original local ring, has zero divisors.
- Characteristic two is allowed; no division by two, orientation or differential sign
  condition enters the statement.
- The empty scheme and dimension-zero schemes are excluded by the node itself, through
  integrality and `hdim = 1`, not by an additional hypothesis. The boundary is permitted
  to be empty. No generic point is marked because hclosed and dimension one exclude it.
- One common arbitrary universe u is used for k and Z, as required by scheme morphisms to
  Spec k; no test-object universe or extra dimension restriction is imposed.

Searches performed before writing:

- msearch LeanFinder: "An integral proper curve with regular or nodal completed local
  rings has smooth normalization and a reduced Cartier boundary divisor". Eight hits,
  including relative-normalization integrality instances; no completed-curve geometry and
  boundary theorem.
- msearch Loogle: `AlgebraicGeometry.Scheme.normalization,
  AlgebraicGeometry.Scheme.IdealSheafData.vanishingIdeal`. Zero hits; the search service
  reports the project normalization identifier unknown (it indexes Mathlib).
- msearch grep: `normalization|vanishingIdeal`, subdirectory `AlgebraicGeometry`.
  Twenty-five hits, including Mathlib normalization and vanishing ideals; these give
  reusable constructions but no matching theorem.
- msearch LeanSearch: "The normalization of a proper integral curve with nodal completions
  is smooth and the reduced inverse image of finitely many closed points is an effective
  Cartier divisor". Eight hits, all relative-normalization infrastructure, no theorem match.
- rg in `lean/WeilConjectures` and `lean/Sheaf`, and the upstream name index, for
  `completed_curve_boundary_geometry|CompletedCurveBoundaryGeometry|completed-curve-boundary`:
  no hits. Search for the node id in `lean/WeilConjectures`: no hits.
- Concept searches for normalization, nodal completions, Cartier ideals, divisor ideals,
  stalk ideals, and module duals located the existing normalization-adjunction theorem,
  NodalNormalizationQuotient, Curve.DivisorIdealSheaf, EffectiveCartier and Modules.Dual.
  The adjunction theorem has extra ambient-curve and adjunction data and does not state
  this node; its explicit scalar-compatibility formula is reused as an API pattern.

Read the source places in literature/stacks-project/curves.tex
(lemma-closed-subscheme-nodal-curve, especially its final completion argument) and
varieties.tex (lemma-normalize-noetherian-dim-1), and the full recorded dependency
statements/interfaces. No statement fault or STATEMENT-DISPUTED issue was found.

Validation: scompile.py on this module, final compile successful against current server
sources, 11.1 seconds, 60-second per-file limit. The wrapper's local attempt encountered
`OSError(28, 'No space left on device')`; its normal server confirmation succeeded with
exit code zero. The only postponed proof is the named main theorem. No auto-implicit
variables, diagnostic commands, file-local notation, private definitions or local instances.

## Second reading by NC

Author's second pass, not a claim of an independent agent review; this dispatcher brief
assigns the independent review to the maintainer and prohibits starting another agent.
I reopened the node and module and matched the hypotheses and every clause above. The
closed-set partition preserves exactly finite closed marked sets; neither it nor the
completion hypotheses mention an ambient curve. I checked the scalar formulas use the
structure morphism p, the canonical normalization is used everywhere, and the smooth-locus
and normalization-isomorphism clauses concern Snode rather than all of S. I checked E
counts all inverse-image closed points once, B is both its canonical divisor ideal and
the radical pullback, and the final restricted map is induced by B's actual inclusion,
so its inverse is evaluation at 1. The affine ideal-image formula expresses stalk ideals,
not maximal ideals of section rings. No clause was removed or added. During compilation
I replaced a failed dotted-open-inclusion elaboration by explicit `Scheme.Opens.ι` and
removed redundant finite-type instance parameters already implied by properness; the
mathematical statement is unchanged. All proofs remain `sorry` as requested.
