## What changed

Proved `AlgebraicGeometry.ProEtale.isCohomologicallySmooth_of_smooth` directly in its
existing canonical comparison coordinates. The target statement and existing definitions are unchanged. The unit-specialized composition identity is split as a strictly smaller named theorem.
The proof uses ordinary etale smooth duality, transports a tensor inverse through the
monoidal site comparison, and obtains the inverse's Dctf property from dualizability
on a noetherian scheme. The canonical base-change equation follows by taking mates
of projection/exchange compatibility and specializing to the coefficient unit.
Composition uses the specified compactification tower, independence of projection
maps from compactification, the composition theorem for adjoint tensor maps, and
its associativity and unit identities. The base-change helpers are private and proved; the composition equation is the one remaining public obligation.

Validation: both modules compiled via lcompile --all; final delivery checks pending.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.ProEtale.isCohomologicallySmooth_of_smooth`
(node `thm-pur-cohomological-smoothness`). Original holes: 1. Added holes: 1. This is a decomposition, net zero holes closed.
Remaining holes in this delivery: 1, `smoothTensorCompositionEquation`, node `lem-v8-smooth-tensor-composition-equation`.

## No longer needed

The definition already expresses its tensor, base-change and composition clauses as
images of the canonical etale arrows. Thus it does not require another construction
of a restricted pro-etale adjunction or another transport of those same arrows.
The inverse is a dualizable object, so its Dctf property follows from the existing
perfect-complex theorem, rather than separate Tor and constructibility proofs for
shifted line evaluations.

Removed direct proof imports (some remain transitively required elsewhere):


- `Sheaf.Paper.PurityFiniteSetting`
- `WeilConjectures.Compactification.NagataCompactification`
- `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType`
- `Sheaf.AlgebraicGeometry.AffineSpaceAmbientAdjunction`
- `Sheaf.Paper.ProEtaleConstructibleOrigin`
- `Sheaf.AlgebraicGeometry.SmoothTensorDuality`
- `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom`
- `WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint`
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`
- `Sheaf.Paper.ComparisonTorAmplitude`
- `Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence`
- `Sheaf.AlgebraicGeometry.SmoothExceptionalBaseChange`
- `Sheaf.Paper.CohomologicalSmoothComposition`
- `Sheaf.CategoryTheory.CompositeTensorTranspose`
- `Sheaf.Paper.ExchangeProjectionSuppliedDomains`
- `Sheaf.Paper.FiniteCompactSupportConstructibility`
- `Sheaf.AlgebraicGeometry.CanonicalCompactSupportSiteComparison`
- `Sheaf.AlgebraicGeometry.CompactSupportComparisonUnit`
- `Sheaf.AlgebraicGeometry.ProjectionComparisonEtaleOrigin`
- `Sheaf.AlgebraicGeometry.SpecifiedExceptionalClassHom`
- `Sheaf.Paper.CanonicalFiniteLevelCompactSupportBaseChange`
- `Sheaf.Paper.CanonicalOriginCompactSupportComposition`
- `Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients`
- `Sheaf.Paper.DerivedPullbackTensorIso`
- `Sheaf.Paper.ProjectionFormulaCoefficientCoherence`
- `Sheaf.Paper.PurityAffineLineOrientationUniqueness`
- `Sheaf.Paper.SmoothExceptionalBaseChangeStatement`

Removed old planned proof dependencies:

- `lem-pur-compact-support-composite-transpose-domains`: the statement uses the etale
  comparison-coordinate maps, and ordinary-etale adjunctions suffice.
- `lem-pur-composite-tensor-transpose`: the existing adjoint tensor composition and
  associativity theorems provide the same two-counit calculation directly.
- `lem-pur-finite-setting-comparison-hypotheses`: noetherianness and compactness follow
  from the finite-type field hypotheses using existing instances; the coefficient
  exponent theorem is used directly.
- `lem-pur-finite-site-counit-projection-transport`,
  `lem-sf-comparison-tor-amplitude`, and `lem-sf-proetale-constructible-origin`:
  the input is already an etale representative in the existing theorem statement.
- `lem-pur-smb-extraordinary`: use ordinary-etale smooth base change and comparison.
- `thm-asd-smooth-tensor`: use the already proved ordinary-etale smooth duality theorem.
- `def-weil-exceptional-inverse-image`: the current compared definitions already use
  the ordinary-etale exceptional functor and the exact site comparison.

Removed obsolete top-level `tool_uses` approvals from the node (the surviving
`prop-asd-smooth-base-change` approval retains its original position):
`lem-kun-dimension-finite-type`, `lem-sf-proetale-constructible-origin`,
`thm-sf-ambient-adjoint-class`, `lem-sf-class-compact-support-comparison`,
`thm-weil-pbc-site-comparison`, `lem-weil-pbc-comparison-pullback`,
`lem-weil-pbc-ringed-topoi-derived-tensor-pullback`,
`lem-weil-pbc-ringed-exchange-tensor-coherence`, `fix-prop-projection-formula`,
`lem-weil-pbc-mate-pasting`, `lem-weil-pbc-comparison-direct-image-canonical-mate`,
`lem-sf-comparison-tor-amplitude`, `lem-pur-derived-pullback-tensor-iso`,
`prop-finite-compact-support-constructibility`,
`lem-pur-finite-site-counit-projection-transport`, and `thm-asd-smooth-tensor`.
These are replaced by the ordinary-etale API and private formal calculations
explained above; no global dependency withdrawal is asserted.

The imports retained for ordinary-etale smooth duality and base change still have their
own dependencies; this report claims removal only from the present proof route.
No declaration or file of the adopted source library is removed.

## Where the brief, the DAG or earlier work was wrong

The DAG's transport plan is substantially longer than required by the current
comparison-coordinate statement. The ordinary etale duality and coherence API
already supplies its canonical maps. The new route keeps the unit's smooth tensor,
invertibility, arbitrary base-change and composition assertions and does not choose
an orientation. Compact-support composition remains the explicitly constructed
comparison in the original definition, rather than an arbitrary witness of existence.

## New nodes

`lem-v8-smooth-tensor-composition-equation` records the unit-specialized composition identity used by the target proof; its natural-language proof is the mate and associativity calculation described above.

The unchanged comparison definitions are relocated into the new module to avoid an import cycle. Change record: `coord/changes/v8-smooth-composition-coordinates.md`. The existing consumer `Sheaf.Paper.ChartDiagonalSourceMate` continues to import the item and sees the same declarations through its public import.

## Second reading by V8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
