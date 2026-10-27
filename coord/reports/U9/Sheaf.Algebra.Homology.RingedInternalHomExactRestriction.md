## What changed

The proof of `CategoryTheory.ringedInternalHom_restriction` now descends coherent ordinary
Hom-complex comparisons along localization. Its signature and the prescribed composition
transport are unchanged. New module `RingedHomRestrictionComparison` constructs the canonical
augmentation from ordinary to derived Hom, proves normalized descent and uniqueness using
K-injective representatives, and identifies the componentwise coherence equation with equality
of transported natural isomorphisms. The item obtains the comparisons for both overFunctor and
overMap from this descent and obtains their coherence from normalization and uniqueness.
Local irreducibility of the existing resolution/product definitions keeps the assembly at
the comparison API; the restriction proof respects transparency. Typed local wrappers for
slice restriction, relocalization, and their canonical comparison align forgetting the
commutative coefficients before/after localization without changing any functor.

Two genuine remaining arguments are separated into their own modules: ordinary Hom-complex
restriction with coherence, and preservation of the representative normalization equation by
composition. Each is strictly a part of the argument. This delivery is a decomposition, not a
claim to have eliminated the underlying mathematical work. No existing declaration signature,
definition, attribute, or public import was changed. No adopted source-library module was edited.

## Proved and sorry left

Closed in the item: `CategoryTheory.ringedInternalHom_restriction`.

New proved infrastructure: `CategoryTheory.RingedHomRestriction.compatible_iff`,
`CategoryTheory.RingedHomRestriction.comparison_exists`, and
`CategoryTheory.RingedHomRestriction.comparison_unique`.

The already proved `CategoryTheory.ringedInternalHom_exact` is preserved verbatim.

Added holes, each in a new module and with a source and full proof in words:

- `CategoryTheory.RingedHomRestriction.ordinary_comparisons`
  (`lem-ringed-hom-restriction-ordinary`).
- `CategoryTheory.RingedHomRestriction.composite_normalized`
  (`lem-ringed-hom-restriction-composition-normalization`).

Thus the current item's one hole is closed and two holes are split off. There is no sorry in a definition or private lemma.

## No longer needed

For the restriction proof, the generic calculus node
`lem-weil-pbc-ringed-internal-hom-exact-restriction` and its Lean attachment
`Sheaf.Algebra.Homology.RingedInternalHomExactUniverses` are not used. That attachment provides
exactness rather than the required coherent restriction declaration, and its import chain
returns to this item. The parent restriction node's obsolete tool-use approval for this generic
calculus is withdrawn. The definition nodes `def-pur-localized-ringed-site` and
`def-weil-pbc-ringed-derived-restriction` remain statement dependencies; their former appearance
as separate proof dependencies is replaced by the precise ordinary comparison and normalized
composition steps.

No existing Lean module is withdrawn. No existing public import is removed. The already proved
tensor-Hom argument retains its own imports and route. The localization and K-injective lemmas
are generic tools: `lem-pur-rhom-well-defined`, `lem-pur-kinjective-restrict-localized`, and
`lem-sp-site-relocalization-kinjective-independent-ring` supply quasi-isomorphism inversion
and preservation of K-injectives, without replacing any unit-level step. The ordinary
calculation uses the sheaf-factor naturality of `lem-sc-internal-hom-over-naturality`.

## Where the brief, the DAG or earlier work was wrong

The old restriction-node proof said to apply a generic ringed-Hom calculus theorem including
coherent restriction. Its Lean attachment currently contains an exactness statement and cannot
supply the restriction comparison; importing its current module would also create a cycle.
The delivered proof makes the source's actual representative argument explicit instead.

The shared item changed during this session: its exactness body and helper modules briefly
disappeared and then returned. The delivery preserves the restored live exactness proof and
its imports; exactness is not counted as a hole closed by this delivery.

Identity arrows, empty sites, zero complexes/rings, nonmonomorphisms of the site, and
unbounded inputs impose no additional assumptions on the new statements. Normalized descent
uses localizations and arbitrary K-injective targets, not bounded resolutions.

## New nodes

`lem-ringed-hom-restriction-comparison-descent` records the proved normalized descent and
uniqueness infrastructure, together with the elementary compatibility equivalence.

`lem-ringed-hom-restriction-ordinary` records the remaining product-of-sheaf-Homs calculation,
including its differential, naturality, and ordinary successive-restriction coherence.

`lem-ringed-hom-restriction-composition-normalization` records the remaining pasting calculation
for the representative equations of specified comparisons; it does not assert existence or
coherence of an independently specified direct comparison.

The complete restriction assembly passed an isolated server compile in 19.0 seconds. The
actual item passed in 55.1 seconds. The temporary probe is removed from the delivery.

## Second reading by U9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
