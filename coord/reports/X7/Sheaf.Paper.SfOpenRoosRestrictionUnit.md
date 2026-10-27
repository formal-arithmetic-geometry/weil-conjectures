## What changed

Proved `WeilConjectures.SfOpenRoos.restriction_unit` in
`Sheaf.Paper.SfOpenRoosRestrictionUnit`, preserving its statement and all existing
public definitions and instances. Added proved private helpers for degreewise
product extensionality, augmentation coordinates, Roos descent, and chain/derived
unit compatibility. Reused the existing proved subterminal module local-calculus
unit theorem through a private proof import. Subterminality follows directly by
monomorphism cancellation.

The final comparison laws are assembled in arbitrary abelian categories before
specialization to module sheaves. Two private predicates express exactly the
existing chain-map and compatibility theorems as inputs to this assembly. This
avoids unpacking the large comparison proposition with concrete sheaf instances.
Private limit-instance helpers, scoped below the public assertion, and local
irreducibility attributes avoid repeated expansion of chosen limits and derived
constructions. A complete diagnostic version compiled in 42.3 seconds; removed
its diagnostic option and unused-variable warnings before the delivery check.
Updated the item's proof steps and dependency list to this argument.

## Proved and sorry left

Closed the single original hole in
`WeilConjectures.SfOpenRoos.restriction_unit`. Added no holes and no split-off
statements. No `sorry` remains in the delivered module. The existing extension
comparison and geometry theorem are used as stated dependencies; their proofs
are outside this packet.

## No longer needed

Removed the private proof imports `Sheaf.SixFunctors.OpenTensorNormalization`
and `Sheaf.CategoryTheory.StrictRoosComparison`. The proof does not directly use
`lem-sf-open-tensor-normalization`, `lem-weil-strict-roos-comparison`,
`lem-cbc-exact-product-functor-strict-limit`, `def-pur-localized-ringed-site`,
`def-pur-sheaf-inverse-limit`, or `lem-weil-pbc-site-constant-restriction`.
The canonical adjunction unit uses the proved subterminal local-calculus lemma, the clopen coefficient comparison
supplies the coefficient clause, and the existing extension comparison supplies
the shared models. Restriction uses the more specific chain-map and compatibility
theorems; its descent is a direct full-faithfulness argument.

These removals concern this node's direct proof dependencies. The extension
comparison and other retained imports may still need these nodes transitively;
no module or declaration is withdrawn. An exploratory import of
`Sheaf.Paper.ExactProductFunctorRoosDescent` was also omitted from the final proof.
Omitted the exploratory proof import
`Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization`
and direct dependency `lem-weil-proetale-weakly-etale-localization`: monomorphism
cancellation proves subterminality directly.

## Where the brief, the DAG or earlier work was wrong

No false statement or definition was found. The plan's generic strict-limit
application would choose its own Roos models, whereas this assertion requires
both directions to share the extension comparison's models. Applying the
chain-map theorem to those given models and descending its natural isomorphism
proves the exact requested compatibility. Unit, projection and localization
calculations work for the empty open, identity open, zero towers and all integer
degrees; no boundedness or tensor hypothesis was added.

## Second reading by X7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
