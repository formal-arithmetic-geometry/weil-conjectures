## What changed

Proved `AlgebraicGeometry.ProEtale.exists_fixedComparisonClassAdjunction` without changing its
signature or any existing definition. The proof constructs the relative adjunction, including
its specified normalization and all naturality and compactification coherence fields. Updated
the theorem node with the concrete retained-interface implementation, while preserving its
current primary specified-compactification attachment. The node now records the implemented
proof and its actual direct dependencies. Private categorical helpers implement descent along
the equivalence between bounded-below etale complexes and their essential image. They choose
only representatives of this established equivalence; the Hom bijections themselves are explicit
composites. The ordinary exceptional adjoint is transported to the literal compactification by
the existing unbounded compactification isomorphism. The class-restricted dimension bound is
proved on etale-origin representatives, including their arbitrary pro-etale base changes.
All four private helper instances have local registrations. The section commands for private
helpers are documented in `coord/changes/finite-comparison-class-proof-scopes.md`, including
the direct consumer inventory; no consumer requires adaptation.

## Proved and sorry left

Closed one hole: `AlgebraicGeometry.ProEtale.exists_fixedComparisonClassAdjunction` (blueprint
`thm-sf-ambient-adjoint-class`). Added zero holes; zero sorries remain in the item. Every new
private helper has a complete proof. No split-off statements or modules. The proof uses the
existing library statements, with their existing proof dependencies. A fresh `deliver3.py --no-push` run on 2026-10-19 passed compilation and preflight
at commit `1d0de81867`, with no errors or warnings. The first attempt reached preflight but
its subprocess timed out after 900 seconds; the retry passed without any Lean changes.

## No longer needed

Removed proof imports:

- `WeilConjectures.SixFunctors.ProEtale.Comparison.FullyFaithful` (already publicly
  available through the existing comparison imports).
- `Sheaf.AlgebraicGeometry.EtaleExceptionalAdjoint` (its underlying ordinary adjoint
  theorem is already available through the public UpperShriek import).
- `Sheaf.AlgebraicGeometry.EtaleCompactSupportComparisons` (the existing canonical
  etale cocycle suffices; its separate proper/open normalization equation is not used).
- `Sheaf.AlgebraicGeometry.CompactifiableOverField` (the supplied compactification
  directly gives HasCompactification, so no compactification-existence theorem is needed).
- `Sheaf.AlgebraicGeometry.DerivedCategories` (no declaration from that module is used).

The legacy existence proof does not separately use the plan nodes
`lem-weil-pbc-finite-type-over-noetherian`, `lem-kun-dimension-finite-type`,
`lem-kun-relative-torsion-direct-image-dimension-bound`,
`lem-weil-pbc-module-direct-image-left-exact`, `lem-weil-pbc-module-sheaves-enough-injectives`,
`lem-sf-finite-cd-derived-upper-bound`, `lem-etale-upper-shriek-bounded-below-from-amplitude`,
`lem-weil-pbc-extension-by-zero-exact`, `def-amb-etale-compact-support`,
`def-weil-pbc-direct-image`, `def-weil-pbc-adjunction-conjugate`, or
`def-weil-pbc-adjunction-mate`: the published quasi-compact-target boundedness theorem and
normalization to a single right adjoint replace these separate steps. These direct proof
dependencies and their obsolete `tool_uses` approvals are removed from the node. The current
primary specified-compactification Hom interface also uses the published boundedness theorem and
explicit comparison chain, with uniqueness of ordinary right adjoints supplying the transport
from the normalized ordinary adjoint. The constructible-origin application is not a field of the
retained theorem and needs no separate import in this proof.

No public imports were changed. No assertion that these modules are unused by other consumers is
made. The proof does not need constructible-origin inclusion, other compactifications'
exceptional adjoints, or the separate conjugation/mate construction: all right functors are
normalized to the one chosen ordinary adjoint, exactly as the existing structure requires.
Comparisons descend from the already specified etale comparisons, and their Hom compatibility
follows directly from the cocycle.

## Where the brief, the DAG or earlier work was wrong

The current primary Lean attachment of `thm-sf-ambient-adjoint-class` names
`SpecifiedExceptionalClassHom`, which publicly reexports the legacy theorem in this item. The
supplied module remains the owner of the actual existential theorem proved here. Its definitions
and its published statement have been retained literally. No statement dispute or definition
repair was needed. The published FullCD theorem has an unused invertible-exponent hypothesis,
absent from the underlying proper-base-change vanishing lemma. The proof repeats its short
comparison transport without adding that hypothesis. Final preflight validation is recorded by
the delivery tool.

## Second reading by G2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
