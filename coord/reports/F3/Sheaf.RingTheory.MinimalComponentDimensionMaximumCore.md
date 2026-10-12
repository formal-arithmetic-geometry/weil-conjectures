## What changed

Proved both declarations in `Sheaf.RingTheory.MinimalComponentDimensionMaximumCore`
without changing their signatures or visibility. Added the proof-only import
`Mathlib.RingTheory.Spectrum.Prime.RingHom` for prime quotient correspondence.
Added the proof-only `import all
Sheaf.RingTheory.FiniteTypeDomainDimensionLocalRingChains` to use its existing
private saturation-to-maximality theorem. All original imports remain needed.

The proof follows [Stacks Tag 00P1](https://stacks.math.columbia.edu/tag/00P1):
compute the coheight of p as the dimension of S/p, identify it with r using the
existing finite type domain dimension/transcendence-degree theorem, and apply the
common maximal-chain length theorem in each domain S/q. Fully proved private
helpers establish the height/coheight sum by joining longest chains, and transfer
coheight through the quotient correspondence. The duplicate local `AlgebraicGeometry.saturated_isMaxChain_of_nonempty`
helper was removed in this repair. The proof now directly uses the existing
private `saturated_isMaxChain_of_nonempty` theorem from
`Sheaf.RingTheory.FiniteTypeDomainDimensionLocalRingChains` through `import all`.

For attainment, a longest chain below p has length d and a minimal head q;
lifting that chain to S/q proves that the image of p has height d. The same
dimension sum therefore equals d+r. The bound proof even works for every prime
q below p, while keeping its original minimality hypothesis.

Updated the two existing DAG proof records to describe the actual Lean argument.
Added the existing local-ring-chains node to both proof dependencies to record
the direct use of its private helper. No unit statement or realized
proof step is bypassed. No new public declarations, definitions or nodes.

## Proved and sorry left

Closed both original holes (2 closed, 0 added):

- `AlgebraicGeometry.minimal_component_dimension_maximum_bound`
  (`lem-weil-pbc-minimal-component-dimension-maximum-bound`).
- `AlgebraicGeometry.minimal_component_dimension_maximum_attained`
  (`lem-weil-pbc-minimal-component-dimension-maximum-attained`).

No `sorry` remains in the delivered module. Every private helper is proved.
No lower holes were split off. The module compiles cleanly through `lcompile.py`.
`#print axioms` on both declarations reports `propext`, `Classical.choice`,
`Quot.sound`, and inherited `sorryAx` from the existing dependency theory.
These are proofs from the existing stated dependencies, rather than a claim that
their entire transitive import closure is already sorry-free.

## No longer needed

None. No original imports, nodes or modules are pruned. Both original domain
dimension modules and the Mathlib localization/height leaf are used.

## Where the brief, the DAG or earlier work was wrong

The returned delivery duplicated a private helper already proved in the library.
The repair removes that duplicate and imports the existing theorem. No changes
to the dependency module or its visibility are required. No mathematical error found. The planned residue-field identification is supplied
by Mathlib's `IsFractionRing (S / p) p.ResidueField` instance. The shared compiled
library already proves the stated domain lemmas, so their statements suffice.
The repository's local `literature/stacks-project/algebra.tex` is absent on this
machine; verified the cited proofs at Stacks Tags 00P1 and 00OS online. The chain
argument handles d=0 and zero-length chains without separate assumptions.

## Second reading by F3

1. PASS: compared the delivered module with the repository using `diff`, then
   checked both existing theorem signatures byte for byte. Hypotheses,
   conclusions, universes, namespace and public visibility are unchanged. There
   are no definition changes or forced adaptations, and no change record is needed.
2. PASS: independently compiled the module through `lcompile.py` (exit 0, no
   warnings). No forbidden declaration form or `sorry` occurs in its Lean source.
   A scratch copy with `#print axioms` checked both public theorems and all five
   private helpers. Only the three permitted axioms occur, plus inherited
   `sorryAx` in the domain dimension and transcendence-degree dependencies.
   The pure order argument and both quotient-correspondence helpers have no
   `sorryAx`. No arbitrary existential witness is used to define public data.
3. PASS: no statements or holes were split off. Read all five proved helpers;
   the upper-set condition required to preserve coheight is proved explicitly.
   Checked the zero-height and zero-coheight cases: singleton chains still smash
   correctly, and prepending a smaller prime contradicts the height bound even
   when d=0. The chosen head is a prime of S, minimal among all primes of S.
   An independent Loogle search for `Order.height, Order.coheight` and a source
   search in Mathlib and both library roots found no replacement for the pure
   common-chain-length identity. Mathlib's supremum identity alone is weaker.
4. PASS: the proof uses existing domain results and Mathlib quotient/localization
   correspondence before introducing proved private glue. Read
   `dag/units/sk-thm-p1.json`, including its `realized` entries: this item is below
   its realized statement and steps, and none is replaced or bypassed. Each old
   proof dependency is still used, so `No longer needed: None` is complete.
   The four public Mathlib imports supply signature notions; the added imports
   are proof-only. The `import all` reuses the already proved private saturation
   helper rather than duplicating it. Verified the chain route against
   [Stacks Tag 00P1](https://stacks.math.columbia.edu/tag/00P1) and the common-length
   result [Tag 00OS](https://stacks.math.columbia.edu/tag/00OS).
5. PASS: diffed both node files. Only `proof`, `proof_deps` and `proof_origin`
   change, and the union of each proof's `uses` is exactly its `proof_deps`.
   The records describe the actual height/coheight argument and the reused
   chain helper. There are no new nodes requiring additional metadata.

Second reading changed only this report, adding the independent review and
verification evidence. No Lean or DAG repair was needed. Final accounting:
2 original holes closed, 0 holes added, 0 split off, no modules pruned.
