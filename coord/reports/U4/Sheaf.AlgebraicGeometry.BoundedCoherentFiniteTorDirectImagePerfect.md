## What changed

Replaced the only sorry in
`Sheaf.AlgebraicGeometry.BoundedCoherentFiniteTorDirectImagePerfect` by a complete
Lean proof following the four steps of the node's plan. All existing signatures and
public imports are unchanged. No other Lean module is adapted.

The proof applies `directImage_isBounded_coherent`,
`isPseudoCoherent_of_bounded_coherent`,
`hasFiniteTorDimension_schemeDerivedDirectImage_of_bounded_coherent_support`, and
`isPerfect_of_isPseudoCoherent_of_hasFiniteTorDimension`. The finite-Tor lemma
requires a common localization morphism universe. Fully proved private helpers
transport isomorphisms of complex images, finite generation, coherence, proper
support, and finite Tor dimension. The proof applies the finite-Tor lemma in the
standard source/target localizations, then uses the K-injective direct-image
factorization and uniqueness of localization to return to the supplied target
localization. Its original localization family on target opens is preserved.
The cohomological bounds are enlarged to `[min a b, b]`, so no `a ≤ b` hypothesis
is added, including for an empty original interval.

Updated the item's DAG proof step 3 and its proof dependencies to record this
transport and `def-pc-ringed-spaces-derived-direct-image`. No unit route changes:
the unit's realization arrays are empty and all four original dependencies remain.

Searches: Lean Finder returned only derived-category T-structure results; Loogle
confirmed `HasDerivedCategory.standard`; the configured grep search found no
perfect/finite-Tor direct-image theorem. Local rg found no shorter theorem in
WeilConjectures or Sheaf, and located Mathlib's `Localization.uniq` and
`Localization.compUniqFunctor` for the required transport. No new modules or
unproved declarations were needed.

Checked the source statement and four-step argument against
[Stacks Tag 08EV](https://stacks.math.columbia.edu/tag/08EV).
Local compilation with lcompile.py succeeds without warnings. The unchanged
statement allows independent `wX` and `wS`; they have not been identified.

## Proved and sorry left

Closed one hole:
`AlgebraicGeometry.Scheme.isPerfect_schemeDerivedDirectImage_of_bounded_coherent_finiteTor`
(node `lem-pc-bounded-coherent-finite-tor-proper-pushforward-perfect`).

No sorry remains in the delivered module, and no holes are added. This is a proof
from existing statements, not a decomposition into new unproved statements.
The four imported argument lemmas still contain their existing sorries in the
read-only library; their proofs are not part of this item. The six new private
helpers are fully proved.

## No longer needed

None. All four original proof imports and dependencies are used. The
ringed-space factorization is already publicly available through
`SchemeDerivedDirectImage`, so it needs no additional import. A temporary direct
import of Mathlib's localization predicate was removed as redundant; it was
not present in the original module. No existing node or module is pruned.

## Where the brief, the DAG or earlier work was wrong

The planned finite-Tor input has a single derived-category morphism universe
`w₁`, whereas the item has independent `wX` and `wS`. Direct application fails
to synthesize a target localization at `wX`, and would produce finite Tor
dimension in the wrong target localization. The fully proved transport fixes
this interface mismatch without changing any statement or dependency module.
The same input additionally requires ordered bounds; enlarging the interval
as above supplies them without excluding the zero-complex/empty-interval case.

The item's node `source.document` still names `more-morphisms.tex` even though
Tag 08EV is in `perfect.tex`, as its proof steps already record. This inherited
metadata error is reported here; that field is outside stage-3 proof edits.
The literature source files are absent in this local clone, so the Stacks tag
was read on its official website. The unit record itself was read from the DAG.

## Second reading by U4

1. **Interfaces: PASS.** Read the complete module and diff against the repository.
   The existing theorem signature is byte for byte unchanged, as are all imports,
   universes, visibility, and existing definitions. Only its proof/docstring and
   six fully proved private proof helpers were added. There are no adaptations,
   interface changes, or change records.
2. **Proof and axioms: PASS.** Independently compiled the delivered module through
   lcompile.py without errors or warnings (7.9 seconds). A scratch copy with
   `#print axioms` for all seven declarations compiled (7.6 seconds). Each private
   helper uses only `propext`, `Classical.choice`, and `Quot.sound`; the main theorem
   additionally uses `sorryAx` from existing imported open statements. No sorry or
   forbidden declaration occurs in the delivered module. The chosen complex is
   supplied by Mathlib essential surjectivity; the direct-image comparison is a
   proved natural isomorphism. No data definition or arbitrary witness from an
   unproved existence statement is introduced.
3. **Split statements: PASS (none).** No new holes or public statements are split
   off. Read the six private helpers: localization uniqueness transports exactly
   the required isomorphisms; finite generating families push along an isomorphism;
   kernels are unchanged by postcomposition with an isomorphism; stalk isomorphisms
   preserve support; the absolute Tor predicates keep their actual K-flat and
   tensor witnesses. Checked independent localization universes, zero objects,
   identity morphisms, and unordered/empty bounded intervals. The min-bound argument
   supplies an ordered interval without strengthening the hypotheses.
4. **Route and pruning: PASS.** Read all four imported argument statements and the
   definitions of relative Tor dimension, tensor vanishing, and derived direct
   image. The four-step reduction agrees with
   [Stacks Tag 08EV](https://stacks.math.columbia.edu/tag/08EV).
   Independent searches used localization/isomorphism wording: Lean Finder returned
   generic exact-functor localization results; Loogle did not resolve the specific
   comparison identifier; local Mathlib rg verified its generating-section tools.
   Local library rg found only private coherence-transport helpers elsewhere and
   no shorter applicable scheme theorem. All four original proof dependencies and
   imports are used; every public import supplies statement vocabulary. No original
   dependency is omitted from `No longer needed`. Read
   `dag/units/sk-thm-picard-duality.json`: realization arrays are empty and this
   delivery retains the original argument and every original dependency.
5. **DAG agreement: PASS.** Diffed the sole delivered node. Only `proof`,
   `proof_deps`, and `proof_origin` change. Step 3 accurately describes the standard
   localization transport and the K-injective computation; the added dependency
   `def-pc-ringed-spaces-derived-direct-image` is exactly the factorization used.
   The dependency list is the union of step uses. No new nodes are required for
   these private, fully proved proof helpers; no node statement changes.

Second-reading changes: appended this independent review and its verification
results. No Lean or DAG repair was needed. One original hole is closed, zero holes
are added, and no modules are pruned. This does not claim the imported open lemmas
or the full axiom closure have been proved.
