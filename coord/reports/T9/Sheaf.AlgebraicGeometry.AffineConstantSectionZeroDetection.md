## What changed

Proved `AlgebraicGeometry.Etale.affine_constant_section_zero_detection` in
`Sheaf.AlgebraicGeometry.AffineConstantSectionZeroDetection`, with all existing
public signatures and definitions unchanged. The additive equivalence has exactly
the specified projection and zero-section pullback homomorphisms. Both base-change
squares and the unit-detection clause are proved.

Private, proved helpers identify the chosen terminal etale object's underlying
scheme with the base, evaluate the existing canonical constant-sheaf/continuous-map
isomorphism, and deduce precomposition for the actual section pullback from
`constant_pullback_unit_continuousMap` and naturality. No arbitrary section model
or unproved data is chosen. Mathlib's fibre irreducibility and
`LocallyConstant.apply_eq_of_isPreconnected` give the fibrewise equality, for an
arbitrary coefficient type. The existing affine-space projection and zero-section
base-change identities give naturality.

Updated the item's DAG proof, proof dependencies and proof origin to this argument.
Removed the unused public import of
`Sheaf.Paper.ConstantSheafSectionsLocallyConstant`; the change record is
`coord/changes/T9-affine-constant-section-proof-imports.md`. No consumer module
imports the item according to `tools/downstream.py` and the source search.

Validation: the final pruned module compiled through `lcompile.py` in 7.3 seconds
with no warnings. A separate 8.1-second compile with `#print axioms` confirmed only
`propext`, `Classical.choice` and `Quot.sound`. The proof
uses no nonemptiness, connectedness of the base, positive dimension, or coefficient
finiteness assumptions; hence the empty-base, disconnected-base, zero-dimensional,
trivial-group, infinite-group and zero-ring cases retain the exact stated scope.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Etale.affine_constant_section_zero_detection`
(node `lem-pur-affine-constant-section-zero-detection`).

Holes closed: 1. Holes added: 0. Sorries left in the item: 0.
No new modules, nodes or unproved helper theorems are introduced.

## No longer needed

Removed the import `Sheaf.Paper.ConstantSheafSectionsLocallyConstant`.
The proof does not use the existential equivalence
`AlgebraicGeometry.constantSheaf_sections_locallyConstant`, so
`lem-weil-pbc-constant-sheaf-sections-locally-constant` is removed from this
node's proof dependencies and its obsolete top-level tool-use approval is removed.
Its statement-level citation is retained: it still correctly describes the
locally constant interpretation of the statement.

The proof also no longer needs `def-weil-pbc-sheafification` as a separate proof
dependency, since the already proved canonical continuous-map comparison and
pullback formula include that construction. No proof dependency is imported
merely for an alternative route. All other declared proof dependencies remain:
`lem-weil-pbc-constant-pullback-unit-continuous-map`,
`lem-pur-affine-projection-connected-fibres`, and `def-sbc-affine-space`.
No module is withdrawn, and no adopted source-library declaration is removed.

## Where the brief, the DAG or earlier work was wrong

The DAG's comparison between two locally constant-section models is unnecessary:
the pullback formula already uses a canonical, proved continuous-map sheaf
isomorphism. Evaluating that same isomorphism avoids an additional uniqueness
argument and also directly matches the coefficient universe `u + 1` of the item.
The separately stated locally constant-section theorem uses universe `u`.
This is a shorter implementation of the same fibrewise clopen argument, not a
change of statement or of the unit route. The current blueprint's vector-bundle
orientation proof Step 1 was read and its connected-fibre zero-section argument
is preserved.

One elaboration detail needed explicit treatment: `⊤_ T.Etale` is a chosen
terminal object, not definitionally `Scheme.Etale.mk (𝟙 T)`. The private
`terminalSchemeIso` is their unique isomorphism after forgetting to schemes;
the pullback-square equation verifies its naturality in the calculation.

## Second reading by T9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
