## What changed

Proved `AlgebraicGeometry.Scheme.finite_fp_proEtale_pushforward_exact` in
`lean/Sheaf/AlgebraicGeometry/FiniteFpProEtalePushforwardExact.lean`, preserving its
complete signature, universes, visibility, and existing docstring.

Three proved private helpers implement the existing argument: finite finitely presented
schemes over w-contractible affine bases are weakly contractible; each target site object
has a covering family with weakly contractible pullbacks; and abelian direct image preserves
epimorphisms. The main proof combines this with finite-limit preservation and Mathlib's
abelian exactness criterion. Module pushforward has definitionally the same underlying
abelian direct image; faithful exact forgetful functors transfer finite limits and epis,
then the same criterion gives finite colimits. The ring map is the original adjunct of c.

Added the proof-only import `Mathlib.Algebra.Homology.ShortComplex.ExactFunctor`.
Updated the existing node's proof and proof dependencies to match the implementation.
No definition, public import, statement, or consumer changed; no change record is needed.

Read the source proof at `literature/stacks-project/proetale.tex`, lines 4762--4784,
the item node, its declared dependency statements and Lean signatures, and its unit record
`dag/units/sk-thm-dl-a1-upper.json`. The unit route is unchanged. Empty sources, zero fibre
rings, identity maps, arbitrary coefficient sheaves, and noninvertible c require no extra
hypotheses in the proof. Choices of covers occur only inside proofs, never in definitions.

Validation: the complete module, after import pruning, compiled through the prescribed
`lcompile.py` with no errors or warnings (13.9 seconds). No limits were increased.
The searches recorded in `searches.jsonl` found no pre-existing finite pro-etale direct-image
exactness theorem; direct library searches supplied the abelian exactness and forgetful APIs.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.Scheme.finite_fp_proEtale_pushforward_exact`
(node `lem-zl-finite-fp-proetale-pushforward-exact`).

Proved 1 of 1 original sorries; added 0 holes; split off 0 statements.
There are no remaining sorries in any delivered Lean file. The three private helpers are
fully proved. Imported declarations are used as stated, under the stage-3 contract.

## No longer needed

Removed imports:

- `Mathlib.AlgebraicGeometry.Morphisms.Basic`: the finite-morphism and site imports already
  provide the geometric facts actually used.
- `Sheaf.RingTheory.IndEtaleStability`: use the existing proved
  `RingHom.IndEtale.weaklyEtale` directly; the large stability package is unnecessary.

Removed proof dependencies:

- `lem-weil-pbc-weakly-etale-source-locality`: `ProEt.ofOpenImmersion` constructs the needed
  open subobjects directly, without the general source-locality statement.
- `lem-weil-pbc-lfp-affine-opens-finite-presentation`: base change followed by the existing
  `LocallyOfFinitePresentation.SpecMap_iff` gives the required ring presentation directly.
- `lem-weil-pbc-ind-etale-stability`: direct ind-etale weak etaleness suffices. Its obsolete
  top-level tool-use approval is also removed from the node.
- `def-weil-proetale-module-direct-image`: its constant-coefficient specialization is unused;
  the theorem uses Mathlib's general `SheafOfModules.pushforward` already in its signature.
  Its containing inverse-image module remains necessary for the actual statement.

No entire module is withdrawn. These are dependency-edge removals for this item; other
parents may still require the corresponding nodes and modules.

## Where the brief, the DAG or earlier work was wrong

No false statement or interface repair was found. The planned preliminary affine cover of
Y and explicit tensor-product associativity are unnecessary: take affine opens of each
object V, then use finite and locally finitely presented base-change instances for its
pullback over Spec D. This realizes the same source proof and keeps its w-contractible
finite-algebra and evaluation dependencies. No new nodes or forced adaptations.

## Second reading by K9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
