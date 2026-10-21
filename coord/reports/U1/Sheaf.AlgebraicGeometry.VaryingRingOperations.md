## What changed

Proved the four remaining obligations in `Sheaf.AlgebraicGeometry.VaryingRingOperations`.
The ordinary pullback comparison uses an explicit right coextension to coefficient
evaluation and iterated mates. Open extension uses the open-site adjunction and
coefficientwise exactness. Derived direct-image evaluation uses the existing strict
singleton left extension, transported by `strictSystemSequenceEquivalence`, together
with normalized derived-extension comparison and preservation of flat-term K-flat
complexes by ringed-topos pullback. Exact localization of the normalized ordinary
open mate proves the open-extension comparison.

All auxiliary constructions and lemmas are private and fully proved. Public
signatures, definitions, attributes and public imports are unchanged. New imports
are proof-only; the two attached proof plans now describe the actual argument.
There are no changes to consumers or the adopted source library. The change record
`coord/changes/U1-varying-ring-proof-scopes.md` documents the local proof scopes and
the definitionally identical cached private normalization statement. All helper
instances are private and local.

Repair of returned head `23729633d1a` (reviewer C-23729): restored both node
copies' `lean_audit` fields to the current repository values. All metadata outside
the permitted stage-3 fields is preserved from the current repository. The proof
changes from the reviewed packet remain. Rebasing also retains the current
`StrictTowerOpenExtension` public import and the two current proof imports for
filtered colimits and concrete coefficients. The first rebase compile exposed one
lemma previously supplied through the larger import:
`mateEquiv_whiskerTop_whiskerBottom`. A direct proof import of
`WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates` supplies it. The delivery
tool constructs its
commit on the freshly fetched `sheaf-dag`.

Repair validation: the full rebased module compiled on the project server without
warnings in 51.2 seconds. Both node copies differ from the current repository only
in `proof`, `proof_deps`, and `proof_origin`; each dependency list equals the union
of its proof steps' uses. The Lean file has zero `sorry`s and no line over 100 columns.

Prior validation: the four proofs pass the complete file check. To remove repeated
carrier elaboration, `moduleEvalP_existsUnique` is now exported as an alias of a
fully proved private specialization. A temporary Lean theorem checked it against
the original complete signature, and an environment check verified that its public
type contains no private constants (both checks pass without warnings, 20.8 seconds).
All 47 original public non-theorem bodies and all public imports remain verbatim;
all other original public theorem headers remain verbatim. The delivery compiles
the complete file with its axiom probe.

## Proved and sorry left

Closed four original holes:

- `AlgebraicGeometry.ProEtale.VaryingRing.moduleEvalG_exists`
  (`lem-sp-varying-ring-module-eval-g-existence`).
- `AlgebraicGeometry.ProEtale.VaryingRing.extension_exact`
  (`def-sp-varying-ring-operations`).
- `AlgebraicGeometry.ProEtale.VaryingRing.evalPMate_isIso`
  (`def-sp-varying-ring-operations`).
- `AlgebraicGeometry.ProEtale.VaryingRing.evalJInv_isIso`
  (`def-sp-varying-ring-operations`).

No holes remain in the item. No holes were added or split off. The existing
`moduleEvalG_unique` proof is retained.

## No longer needed

The old `StrictTowerProperOpenCalculus` import is unnecessary: all single-ring
operations used here come from `StrictConstantTowerOperations` and
`StrictTowerOpenExtension`. Preserve the current repository's narrower public
import of `StrictTowerOpenExtension`. Remove
`lem-cbc-strict-tower-proper-open-calculus` from this node's proof dependencies;
the proof steps instead cite `def-cbc-strict-constant-tower-operations` for exact
pullback and `def-cbc-strict-tower-open-extension` for open extension. This is local
pruning only; the calculus module remains used elsewhere. No module is withdrawn. The proof
uses the existing single-ring extension and the strict singleton-extension theorem,
so their dependencies remain needed. It needs no assertion that evaluating an
arbitrary K-injective system produces a K-injective module, and no extra flatness
hypothesis on the coefficient transition maps. No unit route is bypassed.

## Where the brief, the DAG or earlier work was wrong

The returned packet carried stale audit metadata: the two `lean_audit` differences
were outside stage-3 ownership. Both are repaired by preserving current metadata.

The old proof descriptions for the three operations obligations did not supply
the normalized comparison proofs. The updated plans spell out the finite left
extension and exact-localization arguments. No statement or mathematical definition
was changed. In particular the comparisons are the prescribed adjunction mates,
not arbitrary isomorphisms with the same endpoints. All choices used to construct
adjoints or derived functors are governed by their universal properties.

## Second reading by U1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
