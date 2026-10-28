## What changed

The hypotheses, universes and mathematical conclusion of
`AlgebraicGeometry.ProEtale.strict_kummer_pure_kernel_normalization` are unchanged.
Its conclusion now names a real proposition definition using a coefficient
record. Its actual fields are the original parameters; expanding the record and
the Normalized definition gives the old concrete conclusion by definitional
equality. A profiled sorry-only check spent 35.9 seconds
checking that concrete statement. Naming it separates this cost from the proof.
The generic `KummerPureKernelNormalization` definition remains verbatim.
The theorem proof compares distinguished multiplication triangles, lifts their third
component using full faithfulness of shifted single objects, and proves tower
naturality by cancelling a monic root inclusion. This determines the sign and the
unit equation together.
The finite underlying isomorphisms then lift to p-adic-linear isomorphisms.
The new `PureEvaluationTriangle` and `KernelTriangleData` definitions record
exactly the multiplication-triangle and signed-kernel propositions and keep
their concrete instances folded. They contain no
chosen data or holes. A proved generic application lemma keeps the original proposition folded during
concrete specialization; expanding it over the concrete sheaf categories had
caused the kernel to normalize large inherited category structures repeatedly.

Eleven new modules isolate the actual ingredients. `KummerComparedKernelTriangle`
proves the signed Kummer triangle, identifies its finite kernel by the actual
residue root map, and proves the actual power-ell transition equation. Its proved supporting
modules, `KummerComparedBoundaryFormula`, `KummerSignedTriangleTransport`, and
`KummerComparedKernelLevel`, isolate
the Ext formula and the construction at one level. The latter first constructs
the signed triangle in an arbitrary abelian category and then specializes it,
keeping dependent exactness proofs behind a proved categorical interface. The concrete sheaf
constructions are accessed through these interfaces so each file stays within
the compile limit.
`DiagonalFiniteUnderlyingIsoLift` proves that an additive sheaf isomorphism to a
finite residue module lifts to p-adic scalars, using integer approximation of a
p-adic scalar modulo the annihilating power. `DiagonalPureEvaluationTriangle`
records the remaining multiplication-triangle computation for an arbitrary
integral sheaf and a supplied pure reduction comparison. The original proposition definition is moved verbatim to
`KummerPureKernelNormalizationData`, which the new statement module publicly imports and the assigned module re-exports.
Its public name, signature, attributes and body are unchanged. The generic
normalization criterion and its coefficient-record wrapper are proved in that
module. `KummerNormalizationComponents` proves the three record properties for
the actual coefficients, and the original module applies the criterion to them. This separates the profiled generic and concrete
kernel-checking costs. All other new imports in the item are proof imports.
The assigned module publicly imports `KummerPureKernelNormalizationStatement`.
No existing public import was removed. No source-library file or unit record
was changed.

## Proved and sorry left

The original hole in
`AlgebraicGeometry.ProEtale.strict_kummer_pure_kernel_normalization` is closed by a
complete Lean proof from the triangle and coefficient-lifting ingredients. This is a decomposition, not a
net proof of the original obligation: one original hole is replaced by one
strictly smaller hole, so the net hole reduction is zero.

The following new public theorems have complete proofs and no holes:

- `AlgebraicGeometry.ProEtale.kummer_compared_boundary_formula`;
- `AlgebraicGeometry.ProEtale.kummer_compared_kernel_level`;
- `AlgebraicGeometry.ProEtale.proEtale_signed_kummer_triangle`;
- `AlgebraicGeometry.ProEtale.kummer_compared_kernel_triangle`;
- `AlgebraicGeometry.ProEtale.kummer_kernel_transition`;
- `AlgebraicGeometry.ProEtale.pure_kernel_triangle_comparison`;
- `AlgebraicGeometry.ProEtale.diagonal_finite_underlying_iso_lift`;
- `AlgebraicGeometry.ProEtale.kummer_finite_kernel_lift`;
- `AlgebraicGeometry.ProEtale.kummer_normalization_of_triangles`;
- `AlgebraicGeometry.ProEtale.kummer_normalization_of_coefficients`;
- `AlgebraicGeometry.ProEtale.strict_kummer_kernel_triangles`;
- `AlgebraicGeometry.ProEtale.strict_kummer_evaluation_triangles`;
- `AlgebraicGeometry.ProEtale.strict_kummer_coefficient_lift`.

The only new hole, and the only hole in this delivery, is
`AlgebraicGeometry.ProEtale.diagonal_pure_evaluation_triangle`, node
`lem-sfb-diagonal-pure-evaluation-triangle`. Its statement contains no Kummer
sequence, roots identification, Tate line, finite scalar lift, or Kummer Ext
normalization. It is the multiplication/cofiber computation, including the
(ell,1) transition, from steps (2) and (3) of the source. Its docstring gives the
flat-resolution proof, including the integral/p-adic quotient comparison and
normalization by the supplied evaluated unit. It does not assert the existence
of a pure comparison. All definitions are real constructions and contain no
holes. No definition selects data from an unproved existence theorem; existential
elimination is confined to theorem proofs.

Validation: the final dependency chain compiled in import order without
warnings. `KummerPureKernelNormalizationData` took 6.3 s, the concrete statement
17.9 s, the components 28.5 s, the assigned theorem 33.5 s, and the unchanged
direct importer `StrictKummerUnitNormalization` 36.8 s. The unchanged importer
copy was removed from the sandbox after this check. Earlier checks compiled
the other new modules individually within 60 s. No definition contains a hole;
the packet contains exactly the one named theorem hole reported above.

## No longer needed

No pre-existing Lean import was removed: the original two public imports are
retained for public compatibility. Redundant new proof imports of
`DiagonalPureEvaluationTriangle` and `PureKernelTriangleComparison` were removed
after the new public statement import exposed both interfaces. No module is withdrawn. The item now directly uses only
the concrete component node and the proved generic normalization criterion,
which uses Mathlib full faithfulness and sequence natural-transformation APIs.

The following former direct proof dependencies are replaced as follows:

- `lem-pc-kflat-resolution` and `lem-pur-constant-two-term-resolution` belong to
  the remaining generic multiplication-triangle computation; the item no longer
  carries their calculation itself.
- `lem-amb-kummer-any-base`, `lem-sp-cartier-reduction-site-comparison`,
  `def-pur-roots-of-unity-sheaf`, `def-sfb-geo-cartier-interface`, and
  `def-sfb-cartier-reduction-data` are replaced as direct proof ingredients by
  the proved Kummer triangle. The latter uses the already proved residue root
  isomorphism and forgetting comparison, and the existing actual Kummer complex
  and its exactness. Their statement or transitive uses are retained.
- `lem-weil-pbc-site-module-sheaf-constant-ring-equivalence` is unnecessary for
  the scalar lift: every additive map between the annihilated p-adic modules is
  linear, proved directly from `PadicInt.appr_spec`.
- `lem-sfb-divisible-extension-derived-reduction` is unnecessary: comparison of
  the two distinguished multiplication triangles fixes the boundary equation
  directly.
- `lem-sfb-diagonal-evaluation-unit` and
  `def-sfb-kummer-strict-adjunct-data` remain statement dependencies and are used
  through the new ingredient interfaces rather than as separate proof steps.

These are changes to this item's route, not claims that any retained upstream
module is globally unused. No declaration in `lean/WeilConjectures/` is removed
or given a new hole.

## Where the brief, the DAG or earlier work was wrong

No false statement or assigned repair was found. The queue assigns the original
one-hole proof item, and there is no rework row or item build-error file in the
shared snapshot. The previous plan left three genuinely different computations
inside the same obligation: the derived multiplication triangle, the signed
Kummer triangle, and scalar lifting. This delivery proves the latter two and
writes their combination in Lean. It keeps the blueprint unit route, including
the common (ell,1) transition and the specified unit normalization.

A read-only traversal also found a pre-existing two-node DAG cycle below the
original item: `lem-pc-ring-hom-extension-differential` and
`lem-pc-ring-hom-extension-differential-adjacent` cite each other. The same
cycle is present in the shared baseline. No dependency path returns to any
changed node of this delivery; the unrelated baseline nodes are not edited.

The new statements were checked on n=0, ell=2, the zero sheaf, and the empty
scheme. No sign argument divides by two. The lower multiplication-triangle
statement is for any M admitting the supplied b; it adds no divisibility
hypothesis and asserts no existence of b. The finite lifting statement uses a
fixed finite annihilator, so it makes no assertion about arbitrary additive
maps between unbounded p-adic modules.

## New nodes

`lem-sfb-diagonal-pure-evaluation-triangle` records the remaining generic derived
multiplication triangle and its boundary transition, in
`Sheaf.Paper.DiagonalPureEvaluationTriangle`. It serves steps (2) and (3) of
`det-prop-diagonal-tower-system` and is strictly one part of the argument.

`lem-sfb-kummer-compared-kernel-triangle` records the proved signed Kummer
triangle and actual root transition, in `Sheaf.Paper.KummerComparedKernelTriangle`.
It serves the Kummer kernel of step (3) and the sign of step (4).

`lem-sfb-diagonal-finite-underlying-iso-lift` records the proved finite p-adic
scalar lift in `Sheaf.Paper.DiagonalFiniteUnderlyingIsoLift`. It serves the
coefficient action in step (3) and finite-forgetting normalization in step (4).
The same module proves the ordinary `kummer_finite_kernel_lift` packaging lemma,
separating its profiled kernel checking from the derived concrete application.

`lem-sfb-kummer-compared-boundary-formula` records the proved expansion of the
compared Kummer Ext class into the actual short-exact-sequence boundary, in
`Sheaf.Paper.KummerComparedBoundaryFormula`. It is the positive boundary formula
of step (4).

`lem-sfb-kummer-compared-kernel-level` records the proved root-map isomorphism,
normalized inclusion and signed triangle at one level, in
`Sheaf.Paper.KummerComparedKernelLevel`. It supplies the pointwise part of the
tower theorem. These two additional modules separate self-contained, proved
parts after explicit typed intermediates and generic categorical APIs alone did
not bring the original combined file under the compile limit.

The blueprint search found no independent blueprint assertion for the two new
supporting facts; the Kummer search found the enclosing diagonal-system result
and general Kummer assertions, which are cited through existing nodes. The
p-adic and multiplication-triangle searches found no blueprint node with these
statements. Mathlib searches are recorded from the actual search log. The definition-home relocation is documented in
`coord/changes/a7-kummer-normalization-definition-home.md`; its old and new
definitions are identical. The definitionally equal concrete conclusion is
documented in `coord/changes/a7-kummer-normalization-concrete-statement.md`. Only the assigned module, its node, new modules and
their own nodes are changed.

`lem-sfb-kummer-signed-triangle-transport` records the fully proved transport and
sign calculation for arbitrary endpoint isomorphisms of the actual Kummer sequence,
in `Sheaf.Paper.KummerSignedTriangleTransport`. Profiling separated the concrete
sequence transport from its finite-root specialization. This additional proved
module keeps each check below the file limit; it adds no hole.

`lem-sfb-kummer-kernel-transition` records the fully proved compatibility of
normalized inclusions with the actual roots tower, in
`Sheaf.Paper.KummerKernelTransition`. It is independent of derived categories.
This separates the ordinary root-transition calculation from the distinguished
triangle statements after profiling showed their combined kernel checking still
exceeded the limit. It adds no hole.

`lem-sfb-pure-kernel-triangle-comparison` records the fully proved generic
comparison argument in `Sheaf.Paper.PureKernelTriangleComparison`. It lifts the
third component of a triangle comparison and proves naturality by monic
cancellation. Moving this argument to an abstract abelian category exposed an
implicit reassociation that concrete sheaf composition had accepted by expensive
definitional equality. The reassociation is now explicit. It adds no hole.

`lem-sfb-kummer-normalization-from-triangles` records the proved generic
normalization criterion in `Sheaf.Paper.KummerPureKernelNormalizationData`.
It combines the triangle-comparison equations with the coefficient lift, and
contains the verbatim relocated proposition definition. It adds no hole. The
assigned module re-exports this module through its public statement import,
preserving the original generic public name for its consumer.

`def-sfb-kummer-pure-kernel-normalization-statement` records the real named
concrete conclusion in `Sheaf.Paper.KummerPureKernelNormalizationStatement`.
Its explicit coefficient record uses the former parameters, and expanding the
record and Normalized property gives the old theorem conclusion by definitional
equality. It adds no assertion or chosen data.
It separates the measured statement-checking cost from the proved concrete
application. Its change record is
`coord/changes/a7-kummer-normalization-concrete-statement.md`.

`lem-sfb-kummer-normalization-components` records the fully proved concrete
record properties in `Sheaf.Paper.KummerNormalizationComponents`. These are
specializations of the existing Kummer triangle, pure-evaluation computation,
and finite lift. The folded properties and explicit coefficient record avoid
rechecking the same concrete category structures in the final application.
This module adds no hole.

## Related modules compiled before delivery

35 related module(s) compiled against this delivery by deliver3.py: 35 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.DiagonalFiniteUnderlyingIsoLift": "6e2afffe457184ccdd14bf8ef10fa2a14ba6b6d5", "Sheaf.Paper.DiagonalPureEvaluationTriangle": "cb4c2a5b4694fb05698a84e8b2b8181b53139935", "Sheaf.Paper.KummerComparedBoundaryFormula": "4b103bfb5372d8283c946fd970fb50726e256c0f", "Sheaf.Paper.KummerComparedKernelLevel": "fcc90833496ca35f631f1d90ac21013d311aa4eb", "Sheaf.Paper.KummerComparedKernelTriangle": "fe59ae2ec4b3eb233c03b8833f07636d8976fd11", "Sheaf.Paper.KummerKernelTransition": "f3d88688b06cdda669df4b11fa0842dcd2b3cb40", "Sheaf.Paper.KummerNormalizationComponents": "5b0d0ab8fc4902490f822f41a12859c87e35bce9", "Sheaf.Paper.KummerPureKernelNormalizationData": "91d8ec7615a994f6f5e4d8ccde9640fbd28b774e", "Sheaf.Paper.KummerPureKernelNormalizationStatement": "9b233b11574ea287bbf97d1a0ccfc63913ec7015", "Sheaf.Paper.KummerSignedTriangleTransport": "92a31562ea80e5f0e552e088c75dbfd336f3fa49", "Sheaf.Paper.PureKernelTriangleComparison": "647414321fdf5b1a499ccc66cae4ceef0333cb5e", "Sheaf.Paper.StrictKummerPureKernelNormalization": "d92526baf34914e4b4ad19c80647c12e733c79fa"}, "results": {"Sheaf.Paper.CompactSupportProjectionFormula": {"hash": "9d8a08bf4a6d4025a7ffc9ce8b51e70bcc8ad44a", "status": "OK"}, "Sheaf.Paper.DiagonalTowerTracePresentations": {"hash": "05ac6e7b476b688112bf9759d18d919a2e57c202", "status": "OK"}, "Sheaf.Paper.DiagonalTraceChernTwistExistence": {"hash": "1068832bc22f42be4e9e7504166444c63aee58ec", "status": "OK"}, "Sheaf.Paper.DiagonalTraceCoefficientRestriction": {"hash": "7031e0c2b9ebd9d68b88e08e47b780a448e79f24", "status": "OK"}, "Sheaf.Paper.DiagonalTraceComparisonPartial": {"hash": "d4dc322a23b1c516f8287c6e54ca6e20c3152518", "status": "OK"}, "Sheaf.Paper.DiagonalTraceFiniteCartierChern": {"hash": "d8cfa27726282abe78df8f14bf5bc3b3c017c7a2", "status": "OK"}, "Sheaf.Paper.DiagonalTraceFiniteCartierChernStrict": {"hash": "6f21484099727cccf40ad98629bb2c77d47a4c21", "status": "OK"}, "Sheaf.Paper.DiagonalTraceGeometricModelExistence": {"hash": "b723b04d108008e9e4c224939bcba3e8eb230c28", "status": "OK"}, "Sheaf.Paper.DiagonalTraceOrdinaryScalars": {"hash": "a59e55fb063cdf40e59fa4a39a4ff7c867ef0770", "status": "OK"}, "Sheaf.Paper.DiagonalTraceScalarComparisons": {"hash": "466d4f97329b31b30e24c6343faf72433d8fbd40", "status": "OK"}, "Sheaf.Paper.DiagonalTraceSupportedFiniteBoundary": {"hash": "883c62550891ae03ed15f25bdd7fcc20b441be14", "status": "OK"}, "Sheaf.Paper.ExceptionalReconstructionComparison": {"hash": "d2808d06efb721bf1bf12ac544724e77a081cd54", "status": "OK"}, "Sheaf.Paper.FiniteTensorReductionData": {"hash": "f3269d77de1002cc3263ed0d72d945bfbf50dc9f", "status": "OK"}, "Sheaf.Paper.FiniteTensorSignedReduction": {"hash": "3f37d1ab3e0485298bf5a95dfad2fdd4fce75037", "status": "OK"}, "Sheaf.Paper.NormalizedChernFiniteBoundary": {"hash": "dad0f4410a7d56ea73aeca1a8d62f05d0496945f", "status": "OK"}, "Sheaf.Paper.RamifiedScalarSystemTranspose": {"hash": "53ac490826ec5a0fa35c7c8f9a5ca4c9b3fca77d", "status": "OK"}, "Sheaf.Paper.SmoothPurityTowerClasses": {"hash": "393effb95fd8d6927e44aafc4900c441bce933f9", "status": "OK"}, "Sheaf.Paper.StrictKummerUnitNormalization": {"hash": "f8695f7726640a4cf57d98a916c5c859524d88e3", "status": "OK"}, "Sheaf.Paper.SystemScalarProjectionData": {"hash": "6e6a70ab41d6f19ceee232ba81eb824f4b6f89c8", "status": "OK"}, "Sheaf.Paper.TowerChernIntegralNormalizations": {"hash": "3579cd9ce6a38c24b663104e632867e827a02f34", "status": "OK"}, "Sheaf.Paper.TowerChernOrdinaryScalarPullback": {"hash": "ca1b891a82f29bd183913ad0bdba9c7316d20d9c", "status": "OK"}, "Sheaf.Paper.TowerChernPullback": {"hash": "98d0a5a61de83e1352dbe1fd6a0de9ffff4bd66a", "status": "OK"}, "Sheaf.Paper.TowerChernRealizationPullback": {"hash": "e36a94c84b8488921b94186dd797a565ced6ab92", "status": "OK"}, "Sheaf.Paper.TowerChernReductionPullback": {"hash": "9921c40c9cea5f79dbc608d55ecc549cbd0d6bb5", "status": "OK"}, "Sheaf.Paper.TowerChernScalarPullback": {"hash": "5a4ddd7cfa4eb99077af73ada0950dc0148269e1", "status": "OK"}, "Sheaf.Paper.TowerChernTargetNormalization": {"hash": "75425a271aceb7886ba0c07c4df771504620e87e", "status": "OK"}, "Sheaf.Paper.TowerChernTargetNormalizationData": {"hash": "f54b46b5f7106963c5464787e0241132642fb1f5", "status": "OK"}, "Sheaf.Paper.TowerClassChern": {"hash": "b09337e71b4df16280c1cc1cbd08bf95d7551c96", "status": "OK"}, "Sheaf.Paper.TowerClassLinePullbackExistence": {"hash": "1f42e750c048e29e382ae78d757e44b09c96fb8e", "status": "OK"}, "Sheaf.Paper.TowerIntegralChernNormalization": {"hash": "d53a2983fb9151d9619c47f54525fb82ba4bd224", "status": "OK"}, "Sheaf.Paper.TowerKummerPullbackTranspose": {"hash": "07b4a1f225445296cf94a18b05d5acde89d2c983", "status": "OK"}, "Sheaf.Paper.TowerOrdinaryScalarAssociation": {"hash": "b9042ffe726e9b2560d0cbe6573a14f0e628797d", "status": "OK"}, "Sheaf.Paper.TowerScalarCounitNormalization": {"hash": "4a634635bad31cb1deb6845ed25b028d8b812dde", "status": "OK"}, "WeilConjectures": {"hash": "29212a36c63202a1e8f818f492570e5df8885134", "status": "OK"}, "WeilConjectures.DeligneLaumon.AffineLine.Concentration": {"hash": "88223ed932667f0a1edb7cef5019332aa3369e9d", "status": "OK"}}, "seconds": 400, "time": "2026-10-28T08:43:23+0800", "transitive": 34, "version": 1}
```

## Second reading by A7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
