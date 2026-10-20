## What changed

Replaced the original sorry in `AlgebraicGeometry.ProEtale.openProjectionSiteTransport` with a proof assembling boundedness, the canonical projection isomorphisms, and a normalized comparison square. All existing public definitions, signatures, and their bodies stay unchanged. The proof derives the four boundedness clauses from one source bound, records the inverse identities, and obtains the inverse square by cancellation from the forward square.

Added three component modules. `OpenProjectionSourcePlus` is proved: its two private lemmas establish boundedness of tensoring a shifted flat single complex and preservation by exact open extension. It uses the separately stated flatness bridge. The flatness bridge and the unbounded normalized comparison square remain separate source-backed obligations.

Validation: the packet has been compiled repeatedly with `lcompile.py --all`; the final dry run performs the required preflight. The abstract coefficient-category boundedness lemma avoids the expensive kernel conversion produced by a concrete ModuleCat proof.

## Proved and sorry left

Closed the one original hole, `AlgebraicGeometry.ProEtale.openProjectionSiteTransport`, by decomposition. Also proved the new `AlgebraicGeometry.ProEtale.openProjectionTransport_source_plus` from the flatness bridge and existing library lemmas. There are zero sorries in the item module and in `OpenProjectionSourcePlus`.

Added two holes, each a named theorem with proof exactly `by sorry` in its own module:

- `AlgebraicGeometry.ProEtale.flat_of_finiteCoefficientEtaleRealization_locallyFree`, node `lem-pur-finite-locally-free-etale-flat`;
- `AlgebraicGeometry.ProEtale.openProjectionTransport_projection_square`, node `lem-pur-open-projection-comparison-square`.

This is a decomposition, not a sorry-free proof of the original result. The remaining components are independent proper parts: the first is an ordinary abelian-category flatness bridge with no derived objects or open immersion, and the second is a morphism equality with no local freeness, shifts, boundedness, or inverse identities.

## No longer needed

Removed these original proof-only imports from the item module:

- `Sheaf.AlgebraicGeometry.OpenComparisonTensorNormalization`;
- `Sheaf.AlgebraicGeometry.OrdinaryDerivedOpenClosedAdjunctions`;
- `Sheaf.AlgebraicGeometry.ProEtaleExtensionZeroComparison`;
- `Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZeroExact`;
- `Sheaf.Paper.ComparisonPullbackExact`;
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`;
- `Sheaf.SixFunctors.OpenTensorNormalization`;
- `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`.

The completed assembly needs the canonical projection interfaces and two new component modules. The component square's proof plan still needs the ordinary normalization and extension-comparison nodes; those are not claimed globally pruned. The direct uses of `prop-weil-open-closed-recollement-adjunctions`, `lem-weil-extension-by-zero-exact`, `lem-sf-open-tensor-normalization`, and `lem-weil-pbc-ringed-topoi-derived-tensor-pullback` are unnecessary: exact derived functors and the canonical projection definitions already supply these parts. No whole module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The previous proof plan omitted the bridge between local freeness of the canonical ringed-site realization and flatness of a fixed-ring module sheaf. It also omitted the concrete coherence calculation between left-derived tensor comparisons and exact termwise restriction. The existing ordinary comparison theorem is insufficient by direct application to unbounded derived objects. These are the two remaining genuine component results; their docstrings specify complete proofs in words and cover rank zero, the zero ring, and empty opens.

A diagnostic definitions-module split was removed; all original public definitions remain in the assigned module. No definition or statement repair and no consumer adaptations remain. An earlier dry run exited 137 without printing a result; it did not push. The sandbox reference clock changed from the earlier recorded start 1792425945 to 1792437750.6465178 during provider resumes; neither clock file was edited. Work continued under the original session deadline.

## New nodes

`lem-pur-finite-locally-free-etale-flat` states the ordinary flatness bridge over the canonical constant ring sheaf, with a stalkwise local-basis proof.

`lem-pur-open-projection-source-plus` is proved from that bridge, Tor-amplitude tensor bounds, shift compatibility, and exact derived open extension.

`lem-pur-open-projection-comparison-square` states just the canonical forward square for arbitrary unbounded objects; its proof uses the unit mate normalization and compatibility of derived tensor comparisons. Its expanded canonical composites avoid an import cycle with the item module. The original node's proof and dependencies now describe the actual assembly. No change record is needed: existing signatures, definitions, and visibility are unchanged.

## Second reading by G5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
