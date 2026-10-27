## What changed

Proved WeilConjectures.PurIntegralSupportComparison.beta_characterization from unique
normalization. Reduced normalized_existsUnique to two independent geometric construction
steps, ordinary_existsUnique and derived_existsUnique, with complete Lean assembly.
The assembly first substitutes equality of ordinary records, then equality of the derived
records over that same ordinary record. The five existing coordinate/normalization record
declarations move verbatim to PurIntegralSupportComparisonData to prevent an import cycle;
the item re-exports them. The two construction modules are private proof imports.
Change record: coord/changes/Q4-integral-support-comparison-decomposition.md.

## Proved and sorry left

Original holes: 2. Closed in the item: normalized_existsUnique (decomposition into the
two steps below) and beta_characterization (proof from normalized_existsUnique).
No sorry remains in the item or the data module. Added holes: 2, exactly:

- WeilConjectures.PurIntegralSupportComparison.ordinary_existsUnique in
  Sheaf.Paper.PurIntegralSupportOrdinaryComparison,
  node lem-pur-integral-support-ordinary-comparison.
- WeilConjectures.PurIntegralSupportComparison.derived_existsUnique in
  Sheaf.Paper.PurIntegralSupportDerivedComparison,
  node lem-pur-integral-support-derived-comparison.

This is a decomposition, not a claim that the geometric existence proof is finished.
Hole count is unchanged overall: two upper holes closed and two strictly smaller holes
added. Every new hole has its source and argument in its theorem docstring and DAG node.
The ordinary theorem contains no derived comparison. The derived theorem assumes a fixed
ordinary record and asserts only its extension; it does not construct ordinary data.
All four modules compile through the server compiler; delivery preflight is the final
validation. No full-library build is run by this worker.

## No longer needed

None. No existing mathematical dependency, node or module is pruned. The three original
public imports remain. The data node owns the relocated records; the original node keeps
normalized_existsUnique, normalized, beta and beta_characterization. Neither new theorem
imports the original item, so there is no circular proof. The unit route is unchanged.

## Where the brief, the DAG or earlier work was wrong

The original node has an empty proof and proof_deps despite its existence theorem needing
ordinary geometric comparisons and derived universal properties. The revised proof records
that missing separation. Searches found general Mathlib adjoint-uniqueness, localization
extensionality and right-derived-uniqueness APIs, but no ready-made geometric package.
No statement is disputed or weakened. The two new obligations are the ordinary and derived
paragraphs of the original theorem's proof, not renamed copies of the whole theorem.
The source read was the latest blueprint integral-adjunction Hom display, together with
Zheng Construction 4.1, Lemma 4.10 and Construction 5.15 (printed pp. 21, 23–24, 35).
The new nodes label the coordinate/normalization glue as an agent-written specialization.
Empty schemes, identity maps and zero modules do not require exclusions: the sectionwise
identities and universal comparison arguments remain valid. In particular the derived
step does not assume the existence of B; it is quantified over a given B. Uniqueness is
actual record equality, not merely an endpoint isomorphism. The original consumers
PurIntegralRepresentingPair (B9), ReconstructedPairRefinementCoherence (unclaimed) and
PurRepresentingPairFiniteScalar (newly visible at preflight, unclaimed) retain
identical declarations via public re-export; no forced adaptations are included.

## New nodes

def-pur-integral-support-comparison-data owns the five existing coordinate and normalization
record declarations in the new data module. It contains no proof obligation and does not
assert existence. It is separated to avoid a cycle between definitions and their existence.

lem-pur-integral-support-ordinary-comparison states unique section-normalized ordinary
push/pull/extension comparison, before any derived functors.

lem-pur-integral-support-derived-comparison states unique complex and derived comparison
over a fixed ordinary record. Its proof is the exact-localization and right-derived-unit
part of the existing argument. Neither node depends on the item node itself.

## Second reading by Q4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
