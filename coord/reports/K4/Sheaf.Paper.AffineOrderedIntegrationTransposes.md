## What changed

Filled eleven of the sixteen original theorem holes in
`Sheaf.Paper.AffineOrderedIntegrationTransposes`. Endpoint identifications use the
specified raw arrows and unique HEq transport. Ordinary source descent uses the
specified zero and successor maps, with dependent recursion and uniqueness proved
in generic private lemmas. The coordinate applicability proofs use ordinary finite
Tate-line flatness, constructibility, pullback and tensor preservation. Projection
invertibility follows from the finite compactification projection formula with
both canonical tensor symmetries. The site and frame clauses specialize the recorded comparison theorems.

All existing public declaration signatures and definition bodies are preserved.
The invertible-base coefficient argument is private and uses the structure map
already present in the coordinate statements. No new module, public declaration,
axiom, or sorry is introduced. The DAG records the explicit endpoint and finite-Tor
arguments; its remaining main proof plan is retained for the unfinished assertions.

## Proved and sorry left

Original holes closed (eleven):

- `ordinaryTrace_existsUnique`
- `sourceComparison_existsUnique`
- `source_origin`
- `projection_isIso`
- `integrationTranspose_existsUnique`
- `source_applicability`
- `ordinaryZeroTensorTrace_isIso`
- `ordinarySourceDescent_existsUnique`
- `ordinarySource_plus`
- `coordinate_site_comparison`
- `trivial_frame_integration`

Original holes remaining (five), all in node
`lem-pur-affine-ordered-integration-transposes`:

- `coefficient_plus`
- `ordinary_counit_formula`
- `pro_coordinate_projection_composition`
- `coordinate_coherence`
- `ordered_integration_transposes`

No holes added or split off. This is a partial proof delivery, not a proof of the
main ordered transpose theorem. The closed assertions may use the project's
existing stated dependencies; they do not introduce additional assumptions.

## No longer needed

Removed unused private proof imports:

- `Sheaf.Paper.CompositeIntegrationCounit`
- `Sheaf.Paper.IntegrationTransposeComposition`
- `Sheaf.SixFunctors.CompositionProjectionMate`
- `Sheaf.AlgebraicGeometry.SfEtaleAmbientAdjointProjection`
- `Sheaf.Paper.ProEtaleConstructibleOrigin`
- `Sheaf.Paper.PullbackTorAmplitude`
- `Sheaf.Paper.FiniteCoefficientTensorCtf`
- `Sheaf.Paper.FiniteSiteCounitProjectionTransport`

The ordinary input and its comparison are already supplied, so no theorem choosing
an origin is needed. Ordinary pullback and tensor preservation prove the source
bounds directly; the bounded compared projection theorem proves the precise
projection component without an ambient exceptional adjunction. The other removed
imports belong to the still unfinished counit/composition/main argument and are
not used by the proofs delivered here. Their nodes remain in that argument's DAG
plan; this delivery does not claim those modules can be withdrawn from the target
closure. No module is deleted and no unit route is bypassed.

## Where the brief, the DAG or earlier work was wrong

`coefficient_plus` is STATEMENT-DISPUTED in its unrestricted formulation: it has no
structure map or invertibility hypothesis, although its documented proof uses
locally free Tate lines. For example, take the level-two unramified coefficient ring
A = Z/ell^2 and Y = Spec(F_ell[epsilon]/epsilon^2). The ell-power roots of unity
on the strict local rings are 1 + epsilon times the residue ring, hence are killed
by ell. Extension of scalars gives nonzero A/ell-vector spaces. Their derived
tensor square over A has nonzero Tor in arbitrarily high degrees, whereas the
coefficient at d = 2 is that square shifted by four. Thus its negative cohomology
is unbounded. This counterexample argument has not been formalized in Lean. I preserved the original assertion and its hole, and
proved only the invertible-base case privately for the coordinate arguments.

The docstring plan for `pro_coordinate_projection_composition` suggests ordinary
antecedent transport, but its coefficient H is arbitrary: only M and the tensor
source have origin witnesses. A proof must preserve this domain, for example by
using the raw proper/open projection law and identifying its compositor at the
two witnessed sources. Choosing an ordinary antecedent for H would add an
unjustified hypothesis. Its original statement and hole are preserved.

The normalized ordinary-affine counit theorem uses a regrouped single Tate model
and an unbounded tower comparison; the item uses ordered tensor coefficients and
the bounded comparison. Applying it requires actual source and comparison
coherence equations, not just isomorphic endpoints. Those equations are not
asserted as new holes in this packet.

The attempted coordinate-coherence specialization exceeded the single-file compile
limit. It is not counted as proved. The delivered packet leaves that original
theorem unchanged with its existing hole; no replacement lemma or module is added.
The other eleven proofs compiled together in 41.6 seconds before removing an
unused scoped attribute block that caused a style warning.

## Second reading by K4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
