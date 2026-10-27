# Completed pullback tensor evaluation descent

Item: `Sheaf.Paper.CompletedPullbackTensorComparison`, group F1.

The existing public signatures, definitions, and public imports are identical. Only
proof imports, theorem proofs, ordering of private helpers, and local attributes inside
`section CoherentEvaluation` change. The added local irreducibility and implicit
reducibility settings keep large comparison constructions sealed during elaboration;
they end with that section and change no exported attribute or instance.

The evaluation proof descends one new K-flat representative square by naturality.
Three existing complete arguments are implemented in the new helper module to avoid
repeated elaboration in the large parent. One existing exact-composite proof is exposed
there as a fully proved theorem and attached to its new node. The quotient-unit and
K-flat pullback implementations remain proved private helpers. No new hole is introduced
by those extractions. The sole added hole is the separately recorded representative
calculation, strictly narrower than the parent theorem.

Compatibility: all 41 existing declaration signatures were compared with the shared
source and match exactly. The new helper and the parent passed remote compilation;
the delivery command recompiles the packet and probes declarations/axioms. No existing
importer's interface changed, so no forced adaptations are necessary.
