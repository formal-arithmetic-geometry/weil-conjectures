## What changed

Closed the sorry in strictLocalComplexSectionRestriction_derivedMate by a reduction.
Added proof-only import StrictLocalDerivedExchangeGlobalSections. The proof factors
the underived chain map into neighbourhood restriction and global exchange, applies
the global exchange calculation, and uses naturality of homologyFunctorFactors.inv.
All existing signatures and public imports stay identical.

Added StrictLocalDerivedExchangeLeray for the derived-category exchange/Leray identity
before taking homology or restricting neighbourhood sections. Added the proved module
StrictLocalDerivedExchangeGlobalSections which derives its homology consequence by
naturality of exact sections, cancellation of the target homology comparison, and
functoriality of homology. Updated the parent node's proof route accordingly.

## Proved and sorry left

Closed: AlgebraicGeometry.Etale.strictLocalComplexSectionRestriction_derivedMate
(node lem-weil-pbc-strict-local-derived-mate-sections-factorization).

Proved new: AlgebraicGeometry.Etale.strictLocalDerivedExchange_globalSections
(node lem-weil-pbc-strict-local-derived-exchange-global-sections).

Added one sorry: AlgebraicGeometry.Etale.strictLocalDerivedExchange_leray
(node lem-weil-pbc-strict-local-derived-exchange-leray). No sorry remains in the
assigned module. This is a decomposition, not a net hole reduction (one closed,
one added). The remaining identity has no degree n or neighbourhood index i and
states the part of the argument before homology and neighbourhood restriction.

## No longer needed

No imports removed and no whole modules pruned. The following old parent proof_deps
are no longer direct prerequisites of its proof:
- def-weil-pbc-strict-local-injective-source-comparison;
- def-weil-pbc-strict-local-mate-projection-data;
- def-weil-pbc-underived-exchange;
- lem-weil-pbc-injective-sections-pullback-comparison;
- prop-weil-pbc-derived-inverse-image-adjunction.

They remain needed by the new intermediate nodes or by public signatures. The proof uses the definition of
strictLocalUnderivedMateSections but not strictLocalUnderivedMateSections_eq; it
also does not use sourceLocalizedSectionsIso_germ or
injectiveSections_strictLocal_comparison. Those declarations are not proof
prerequisites of this factorization; their modules supply definitions in its
signature and remain imported. The parent retains the underived map definition
and neighbourhood restriction node; other original dependencies are used by the
new intermediate nodes rather than directly by the parent.

## Where the brief, the DAG or earlier work was wrong

The original proof plan requires nontrivial glue between the generic derived mate
factorization and the exact-sections/Leray target comparison; no cited declaration
already states this glue. That is the remaining new statement, with the parent's
source and its steps recorded. No acyclicity of p^*M or invertibility of its sections
unit is asserted. All statements include zero complexes and require no restriction
on integer degree. The unit sk-prop-h2 records no realized nodes, and no unit step
was changed.

Initially the shared green build lacked StrictLocalUnderivedSectionsMate.olean;
it arrived during work, and compilation continued without rebuilding the dependency.
A broad rewrite exceeded the file limit; the explicit calc proof compiles well
within the limit. No library or tools files were changed by hand.

Searches: LeanFinder returned generic localization/adjunction lemmas; Loogle did not
recognize the project-specific factorization; msearch grep had no hits, while direct
rg located PlusAdjunction and DerivedComparison. Their statements were read and do
not include the global sections/Leray computation. LeanSearch was unavailable.

## New nodes

lem-weil-pbc-strict-local-derived-exchange-leray isolates the derived-category exchange
and Leray identity before homology or neighbourhood restriction. Its statement does
not repackage the assigned statement: no degree or neighbourhood index occurs, and
it concerns the localized global-section complexes before homology.

lem-weil-pbc-strict-local-derived-exchange-global-sections is its proved homology
consequence, using exact sections naturality and the target comparison definition.
No change record is needed: existing statements and definitions are unchanged.

## Second reading by M3

1. Compared the assigned module with the repository version. Its existing theorem
signature is now byte-for-byte identical, and its docstring and public import are
unchanged. Only its proof and a plain proof import change. The two new modules
introduce the two declarations recorded in their nodes; no definitions, target
statements or forced adaptations change. Verdict: pass.

2. Compiled all three modules in import order through lcompile.py. Compiled scratch
copies with #print axioms for all three declarations: only propext,
Classical.choice, Quot.sound and sorryAx occur. The only delivered sorry is the
named strictLocalDerivedExchange_leray theorem, with its source, full proof
outline and matching node. No forbidden declaration or hollow definition occurs.
Verdict: pass as a decomposition, not a completed axiom-free proof of the item.

3. Read both new statements and their proofs/outline. The residual derived-category
identity is the exchange and Leray step alone: it has neither neighbourhood
restriction nor homology, and the parent performs both remaining operations by
actual compiled proofs. The exact-sections homology consequence is proved. The
source unit is inverted only on the bounded-below injective representative; the
pulled-back sections unit is retained. Zero complexes make both composites zero;
all degree arguments apply uniformly for negative and positive integers, and q is
transported functorially, with no assumption that the pulled-back complex is
injective. This is a strictly smaller part of the argument, not a renamed parent.
Searched again with LeanFinder for derived-composition/unit compatibility, Loogle
for rightDerivedFunctorUnit, and grep for unit_leray, unitLeray and mate/global
sections. Read PlusAdjunction, DerivedComparison and EtaleKInjectiveUnitLeray.
The latter's public theorem requires K-injectivity on both complexes and does not
apply to the pulled-back complex here; its useful general Leray calculation is
private. Generic Mathlib comparison lemmas do not already state this combined
exchange identity. No residual hole can be closed by a direct existing theorem.
Verdict: pass.

4. Checked the chain-map factorization, exact-sections comparison cancellation,
and naturality of homologyFunctorFactors.inv from the top downward. All imports
supply signature data or the proof; the new theorem dependencies are plain imports.
The report now enumerates every old parent proof_dep removed from its direct route.
Those prerequisites remain used below or in signatures, so no whole module is
pruned. sk-prop-h2 has empty realized entries, and no unit statement, step or route
changes. Verdict: pass.

5. Parsed all node JSON files; their lean.statement fields agree verbatim with the
Lean signatures. The parent records the chain-map factorization and homology
naturality, the global-sections node records the homology reduction, and the Leray
node records the remaining derived exchange/unit calculation. The new nodes have
source, proof, dependency, search, provenance, blueprint, unit/chapter and Lean
records. Existing node changes are confined to the allowed proof fields.
Verdict: pass.

Changes in second reading: restored exact signature whitespace; removed the unused
local U in the parent proof; wrapped one long proof line; completed the explicit
list of removed direct parent dependencies and recorded these review checks.
One old hole is closed and one new hole is added (net zero); the new homology
consequence is proved without adding another hole.
