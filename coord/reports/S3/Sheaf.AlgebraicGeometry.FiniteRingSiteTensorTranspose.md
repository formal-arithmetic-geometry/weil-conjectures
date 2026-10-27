## What changed

The original transport theorem is reduced to the two canonical-map calculations in its
existing proof plan. The finite-Tor etale generation theorem supplies the full etale closure;
finite comparison supplies full faithfulness, essential image, and invertibility of the
specified compact-support comparison. Its naturality is proved from proper-mate and open
comparison naturality. The finite-coefficient unbounded proper projection formula supplies
etale projection invertibility.

FiniteRingAdjointTransport proves the counit-normalized transport of arbitrary chosen
adjunctions through equivalences, uniqueness, and preservation of every adjoint transpose.
FiniteRingTensorTransposeAssembly applies it to full image subcategories, obtains pro
projection invertibility by cancellation, and computes the two tensor-order formulas from
projection, evaluation, and braiding compatibility.

All 16 existing definitions and abbreviations were moved verbatim to
FiniteRingSiteTensorTransposeData and publicly re-exported by the original module to avoid
an import cycle. Their signatures, attributes and bodies are unchanged, as checked against
the repository by the declaration parser. No source-library module is changed. No consumer
needs adaptation. Change record: coord/changes/finite-ring-site-tensor-transport-data.md.

## Proved and sorry left

The single original hole is AlgebraicGeometry.ProEtale.finiteRingSiteTensorTranspose.
It is closed by a reduction to two strictly smaller canonical-map identities, rather than
counted as an unconditional proof. The categorical helper declarations
AlgebraicGeometry.ProEtale.finiteRingAdjointTransport,
AlgebraicGeometry.ProEtale.finiteRingAdjointTransport_transpose, and
AlgebraicGeometry.ProEtale.finiteRingTensorTransposeAssembly are proved without holes.

Two holes are added, each in its own module with proof exactly `:= by sorry`:

- AlgebraicGeometry.ProEtale.finiteRingProjectionSquare,
  node lem-pur-finite-ring-projection-square: only the canonical projection square.
- AlgebraicGeometry.ProEtale.finiteRingTensorCoherence,
  node lem-pur-finite-ring-tensor-coherence: only unit evaluation and signed braiding.

Thus: one original hole reduced, two split off; net hole change +1. The shared data module
has zero holes. Neither split assumes or concludes the whole transport theorem: the first
has no adjunction, essential-image or invertibility assertion; the second has no morphism,
compactification or projection map. Both include the zero ring and empty schemes. No data
is chosen from a mere-existence hole.

## No longer needed

Removed the original private proof imports:

- Sheaf.AlgebraicGeometry.FiniteRingEtaleCompactGenerators
- WeilConjectures.CategoryTheory.WeakTriangulatedGenerator
- WeilConjectures.CategoryTheory.CompactGeneratorsBuildObjects
- Sheaf.AlgebraicGeometry.UnboundedSiteComparison
- Sheaf.AlgebraicGeometry.ProEtaleOpenTensor
- Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZeroAdjunction
- Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZeroExact
- Sheaf.AlgebraicGeometry.UnboundedDirectImageComparison
- WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection
- WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekProjection
- WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs

Their necessary constructions remain available through the statement interface or the
actual proof imports. The node now cites the existing generation theorem instead of
repeating compact-generator and telescope glue. Direct uses of
lem-weil-pbc-finite-type-over-noetherian, lem-pur-etale-finite-ring-compact-generators,
def-pc-generators and lem-pc-compact-generators-build-objects are unnecessary here;
the generation theorem retains its own required dependencies. No global withdrawal of
those nodes or source declarations is claimed.

Removed top-level tool-use approvals for lem-weil-pbc-finite-type-over-noetherian,
thm-amb-etale-exceptional-adjoint, sk-prop-sf-existence and det-sp-unique-right-adjoint.
Direct uses of thm-amb-etale-exceptional-adjoint, sk-prop-sf-existence and
det-sp-unique-right-adjoint are unnecessary because the statement quantifies over the
chosen adjunctions: the categorical helper constructs and proves uniqueness for their
mate. The open tensor, extension-by-zero, tensor-comparison and projection-map nodes
remain needed by the split-off square/coherence arguments. No unit statement or unit
proof step is removed. No module is withdrawn or globally pruned.

## Where the brief, the DAG or earlier work was wrong

The source library already proves the finite-coefficient unbounded projection formula
without the extra Noetherian argument envisaged in step 1. The existing generation theorem
already implements the compact-generator/telescope argument, so repeating it is unnecessary.
Its closure indexes coproducts in a smaller universe and uses a different Tor-amplitude
predicate; the private helper proves the required conversion explicitly.

The new shared-data module is a structural extraction only. All mathematical statements,
including the original theorem, remain unchanged. The generation theorem is a generic
already-proved tool from the finite-comparison unit, used solely for the same generation
step; the smooth-purity unit route is retained.

## New nodes

- def-pur-finite-ring-site-tensor-transport-data attaches the 16 unchanged canonical
  definitions moved to the publicly re-exported shared module.
- lem-pur-finite-ring-adjoint-transport attaches the two proved generic adjunction lemmas.
- lem-pur-finite-ring-tensor-transpose-assembly attaches the categorical assembly proof.
- lem-pur-finite-ring-projection-square states original proof steps 6, 8 and 9 as their
  precise canonical-map equality; it has one remaining hole.
- lem-pur-finite-ring-tensor-coherence states the unit and signed-braiding part of original
  proof steps 5 and 11; it has one remaining hole.

The parent node's proof, dependencies, proof origin and Lean attachment are updated.
Reviewer correction: the parent's proof_deps now name the nodes whose declarations the
proof actually calls: def-sfb-unbounded-direct-image-mate (for
unboundedDirectImageComparisonMap_naturality) instead of lem-sfb-unbounded-direct-image-comparison,
whose module is no longer imported; and lem-etale-proper-projection-formula-finite (for
Etale.isIso_rightDerivedLowerStarProjectionMap_of_finite) instead of
lem-amb-proper-coproducts-projection, whose declaration the proof does not use.

Validation: the original theorem signature and all 16 relocated definitions were checked
against the current shared sources. The delivered dependency graph is acyclic. All six
Lean modules are checked by lcompile.py and the delivery preflight.

## Second reading by S3

(Written by the independent reviewer, 2026-10-25. The delivered section said there was no second
reading, so this replaces it.)

- Statement: the signature of finiteRingSiteTensorTranspose is byte-identical to sheaf-dag.
  The 16 definitions moved to FiniteRingSiteTensorTransposeData have signatures, attributes and
  bodies identical to the old module, checked declaration by declaration. The item re-exports
  that module with `public import`, so every name and unfolding its nine consumers see is
  unchanged.
- Assertion 1: finiteEtaleClosure_all puts every etale object into the etale closure. It uses
  finiteTorConstructible_etale_localizing_eq_top, a (u+2)→(u+1) coproduct-size transport and
  hasTorAmplitudeIn_iff_torAmplitudeIn. hcomp identifies the ambient essential image with the
  pro-etale closure: the closure is replete, and the closure equivalence of
  finiteComparisonLocalizing supplies the preimage. Full faithfulness comes from
  finiteComparisonOrdinary_fullyFaithful. b is assembled from the invertible components of
  finiteComparisonCompactSupportMap, and its naturality is proved, so b.hom.app = beta holds by rfl.
- Uniqueness of rho and the counit equation come from finiteRingAdjointTransport: a mate across
  the image equivalences, made invertible by Yoneda. Both are proved for arbitrary chosen
  adjunctions, as the statement quantifies.
- Assertion 2: the equality of the two routes is exactly finiteRingProjectionSquare (sorry). The
  etale projection map is invertible by the proper finite-coefficient projection formula through
  projectionMapOfCompactification_app_app. Invertibility on the pro-etale side follows by
  cancellation in the square.
- Assertion 3: the transpose is transported, then the square is inverted using the unit half of
  finiteRingTensorCoherence. The opposite order uses its braiding half together with braiding
  naturality.
- Holes left: finiteRingProjectionSquare and finiteRingTensorCoherence. Both are true identities
  between canonical maps, for arbitrary B, T, M, K, including the zero ring and empty schemes.
  Neither restates the item.
