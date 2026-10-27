# Ordinary line scalar tower: proof interfaces and instance search

Item: `Sheaf.Algebra.Homology.OrdinaryLineDerivedScalarComparison` (held by G5).

Proved `comparison_tower`. Private helpers express ordinary coherence on pure
tensors, computation naturality, and the pasting argument on K-flat models.
The private computation transformation omits its redundant identity factor;
`computation_app` identifies it with the unchanged public computation map.

Profiling exposed repeated searches for additive structures through abelian
instances. Following the existing pattern in `SignedLineLocalizedCoherence`,
local priority 30000 selects the existing native sheaf-module, complex, and
functor preadditive instances, zero morphisms, and preservation of zero morphisms.
The hints change only this file's instance search. They introduce no category,
operation, object, or choice, and preserve every existing declaration signature,
definition body, and public import.

Following the existing pattern in `SectionScalarComputationTransport`, selected
proof expressions are inferred once and assigned directly to the elaborator's
goal. The kernel still checks their types against the displayed statements.
This avoids generating unnecessary heterogeneous-equality conversion scaffolding;
it does not disable kernel checking or any transparency option.

Other private proof paths are streamlined: `pure_eq_ordinary` applies a generic
formula; `tensor_site_pure` transports it by congruence; `exists_lineData` extracts
its needed comparison before substituting the derived-functor equality.

Only the held module changes. No consumer source adaptation is needed.
The node's step 7 records the tower argument. No new node or hole is introduced.
