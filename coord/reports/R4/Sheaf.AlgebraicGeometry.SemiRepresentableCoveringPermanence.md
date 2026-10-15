## What changed

Proved `AlgebraicGeometry.Scheme.semiRepresentableCovering_comp_baseChange` in
`lean/Sheaf/AlgebraicGeometry/SemiRepresentableCoveringPermanence.lean`, preserving its exact
signature and all existing imports and docstrings. Added a private abbreviation for the sieve
already used in `IsSemiRepresentableCovering` and a proved private membership lemma:
`componentSieve_mem_iff`. It identifies membership with factorization of the corresponding
one-component morphism through the given morphism of formal coproducts.

Composition now follows from `GrothendieckTopology.transitive`, `pullback_stable` and
`superset_covering`. For base change, the sieve obtained by pulling back the original covering
sieve is contained in the projection's component sieve: each member lifts using
`pullback.lift`, and `pullback.lift_fst` gives the required factorization. This avoids inspecting
or reindexing the chosen formal-coproduct pullback. The existing node's `proof`, `proof_deps`,
and `proof_origin` describe this argument. No signatures, definitions of the library, or
other modules were changed.

Source read: [Stacks Project, Tag 01G4](https://stacks.math.columbia.edu/tag/01G4), parts (1)
and (2) and their proof. The route remains the site's composition and base-change axioms;
the pullback argument is expressed through its universal property. The unit record
`dag/units/sk-prop-h2.json` has no realized statement or step carried by this item; no unit
route is bypassed.

Searches actually run: LeanFinder for composition and base change of coverings of formal
coproducts (generic covering-sieve bind results, no exact result); Loogle for
`Sieve.ofArrows` (unknown identifier, no result); the search wrapper's grep for formal
coproduct coverings (no result); and direct `rg` searches of both library roots and Mathlib.
The relevant Mathlib definitions and theorem signatures were read directly.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.Scheme.semiRepresentableCovering_comp_baseChange`.
Both conjuncts have complete proofs. The private helper `componentSieve_mem_iff` is also
proved. No `sorry` remains in the item, and no new hole was added: 1 closed, 0 added,
0 split off. This is a proof, not a decomposition.

The file compiles cleanly through `lcompile.py`. An additional single-file axiom probe prints
only `propext`, `Classical.choice`, and `Quot.sound` for the public theorem. The proof covers
arbitrary index types, including empty ones, and uses no nonemptiness or finiteness
assumption. The required `deliver3.py R4
Sheaf.AlgebraicGeometry.SemiRepresentableCoveringPermanence --no-push` printed
`OK (dry run)`: the delivery compiles and passes preflight except for the independent
second reading, which belongs to the next worker. Nothing was pushed.

## No longer needed

No existing import was removed: the sole public import is required by the unchanged
statement. No new proof import was needed. Removed these planned dependencies from this
node's `proof_deps`:

- `lem-weil-pbc-etale-covering-composition`: replaced by the small etale topology's
  transitivity and pullback axioms directly.
- `lem-weil-pbc-etale-covering-base-change`: replaced by the topology's pullback axiom
  and the categorical pullback universal property directly.

Both are Mathlib leaves with no project Lean module attached, so there is no additional
module to withdraw. The semi-representable-object, etale-site, and finite-limits nodes
remain needed. No other planned node or module is pruned by this delivery.

## Where the brief, the DAG or earlier work was wrong

No false statement or interface defect was found. The old DAG proof was valid but its
explicit joint-surjectivity and pullback-reindexing steps were unnecessary for the actual
covering-sieve definition. The original docstring is retained as its source proof sketch;
the revised node and proof-body comment describe the implemented argument. The local
literature directory contains citation tables but no Stacks source, so Tag 01G4 was read
from the official Stacks page linked above. No new nodes or forced adaptations.

## Second reading by R4

Independent second reader, 2026-10-16. Read the delivered module and its repository diff,
the existing node and its diff, the three retained dependency records and their Lean
implementations, and `dag/units/sk-prop-h2.json`. Read
[Stacks Project, Tag 01G4](https://stacks.math.columbia.edu/tag/01G4),
Lemma `lemma-covering-permanence`, clauses (1) and (2) and their proof.

1. **Interfaces: pass.** The only existing declaration is
   `AlgebraicGeometry.Scheme.semiRepresentableCovering_comp_baseChange`.
   Its signature is byte for byte identical to the repository's, including the arbitrary
   scheme `X`, universes, formal coproducts `K`, `L`, and covering hypothesis `ha`.
   The first conjunct quantifies over every `M` and covering `b`; its conclusion covers
   `a ≫ b`. The second quantifies over every `L'` and arbitrary `c`, and covers the first
   projection of `pullback c a`. These are exactly the two source clauses, specialized to
   the small etale site. Pullback existence is supplied by the existing Mathlib instance,
   whose construction uses matching index pairs and component pullbacks as the node says.
   No existing definition, signature, visibility, or import changed. Both added helpers
   are private; the abbreviation repeats the actual covering sieve definition.

2. **Proof and axioms: pass.** Independently compiled the delivered file with `lcompile.py`
   without errors or warnings. Compared the scratch axiom probe with this file and compiled
   it separately: the public theorem uses exactly `propext`, `Classical.choice`, and
   `Quot.sound`, with no `sorryAx`. Scanned for `sorry`, `axiom`, `unsafe`, `opaque`,
   `implemented_by`, `extern`, and explicit `sorryAx`: none occur. The private abbreviation
   constructs a sieve directly. Witnesses obtained from sieve membership are eliminated
   inside proofs; there is no data selected from an unproved existence theorem. The
   categorical pullback comes from the existing proved limit construction.

3. **Helpers and residual statements: pass.** No statement was split off and no hole was
   added. Checked both directions of `componentSieve_mem_iff`: generated-sieve membership
   supplies an index, a component map and its factorization; equality of one-component
   morphisms supplies precisely that index equality and factorization in reverse.
   The equality transports agree with `FormalCoproduct.hom_ext_iff`. Empty source indices
   make both sides false for a given arrow, and singleton indices give the usual
   factorization condition. Empty target index sets make the corresponding covering
   obligations vacuous. The proof never chooses an index without a membership witness,
   and also permits bottom covering sieves over empty etale objects. No nonemptiness,
   finiteness, or surjectivity of index maps was assumed.

4. **Route and pruning: pass.** Composition uses transitivity with `hb n`, pulls back
   `ha (t.f PUnit.unit)`, and proves the required sieve inclusion by associativity and
   the two factorizations. Base change pulls back `ha (c.f j)` and explicitly constructs
   `pullback.lift (FormalCoproduct.Hom.fromIncl j h) t hc`; `pullback.lift_fst` proves its
   projection equation. Read Mathlib's `bind_covering` and `bindOfArrows`: these still
   require relating their indexed composite sieve to this component sieve, so they do
   not remove the argument already given. Independent LeanFinder search for composing
   indexed covering families returned generic topology axioms and bind results; Loogle
   with fully qualified `CategoryTheory.GrothendieckTopology, "bind"` returned those bind
   results. The earlier unqualified Loogle query failed identifier resolution and was
   not treated as evidence of absence. Wrapper grep and direct searches of Mathlib,
   upstream, and both project roots found no direct permanence theorem to reuse.
   The sole public import is needed for the public statement; there are no proof-only
   public imports to demote. `## No longer needed` lists exactly the old `proof_deps`
   absent from the new proof: the composition and base-change Mathlib leaves. Neither
   has a project module to remove. The unit's `realized.statement` and sole
   `realized.steps` entry are empty; no realized unit statement or step is bypassed.

5. **DAG agreement: pass.** Only `proof`, `proof_deps`, and `proof_origin` differ from
   the repository node. The union of the proof steps' `uses` equals `proof_deps`.
   Step 1 describes the membership helper; step 2 describes topology transitivity and
   the inclusion actually proved; step 3 describes the pullback lift actually used.
   The retained semi-representable definition supplies the component sieves, the etale
   site supplies the topology axioms, and the finite-limits leaf supplies pullbacks.
   The node's statement, sources, unit, chapter, Lean statement record, and other fields
   are unchanged. There are no new nodes or change records to review.

**Changes by the second reader:** appended this independent review and its search and
verification evidence. No change to the correct Lean proof or DAG was necessary. Confirmed
one original hole closed (`AlgebraicGeometry.Scheme.semiRepresentableCovering_comp_baseChange`),
zero holes added, and zero statements split off. This is a completed proof, not a decomposition.

Delivery-tool observation for the maintainer: the first second-reader dry run spent more
than seven minutes repeatedly waiting on `cache/library-builder.lock`. On interruption,
the traceback showed six recursive `_load` retries through `delivery_cache.py:66`, where
an advancing `origin/sheaf-dag` restarts indexing. Restarted the required tool using its
supported `WEIL_DELIVERY_CACHE_DISABLE=1` option, which selects the ordinary source
scanners and retains compilation, axiom probing, and preflight. No tool was edited and
no shared lock was removed.
