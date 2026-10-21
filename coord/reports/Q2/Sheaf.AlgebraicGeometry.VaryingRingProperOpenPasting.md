## What changed

Proved `AlgebraicGeometry.ProEtale.VaryingRing.alpha_identities`, and reproved the
complementary clause of
`AlgebraicGeometry.ProEtale.VaryingRing.modulePi_components` without importing
`Sheaf.AlgebraicGeometry.VaryingRingModulePiComplementZero`.

Three proved private helpers perform the argument. `module_isZero_of_eval` applies
componentwise exactness to the zero-arrow short complex; this detects zero ordinary
systems without comparing scalar actions by definitional reduction.
`module_disjoint_direct` uses `moduleEvalG` and `moduleEvalP` to transport the already
proved constant-ring `StrictTower.module_disjoint_direct` to each ordinary level.
`module_disjoint_extension` transposes twice under the ordinary adjunctions. The
complementary projection has zero target and is therefore zero. The image-component
proof and all existing signatures are preserved.

The calculus proof import is now `import all`, to use its proved private
constant-ring disjoint-direct-image lemma. This remains a proof-only import.
The DAG's fourth step now records this argument; the obsolete complementary-node
citations in the sixth and seventh steps and proof_deps are removed. Its eleventh
step records the identity proof via invertibility and the existing pasting laws. No unit route
is bypassed. No source-library declaration is changed.

Validation: the complete item compiles cleanly with lcompile.py (11.0 seconds). The earlier expensive
comparison of section-module homs was replaced by the abstract zero-arrow exactness
argument, avoiding reduction of the evaluation scalar transports.

## Proved and sorry left

Textual holes closed in the item: 1 of 4:
`AlgebraicGeometry.ProEtale.VaryingRing.alpha_identities`. Holes added: 0.
No new theorem with `sorry` and no new DAG node is introduced.

Both identity normalizations are proved from the existing ordinary and derived
pasting statements, not from a renamed identity theorem. The identity squares are
cartesian, so their canonical lifts are isomorphisms. Pullback along an isomorphism
is an equivalence; its ordinary adjunction unit and the clopen open-to-direct map
are invertible. Thus moduleAlpha and its exact localization are invertible.

The proof establishes the actual compositor unit laws rather than assuming them:
it checks the direct-image unit against the pro-etale base-change site's identity
and composition isomorphisms, transposes to the inverse-image unit, and localizes.
For the open-extension compositor, it transposes this ordinary unit law and uses
the right-derived adjunction unit factorization on Qh to identify the localized
ordinary identity with the specified derived jId. Pasting an identity square with
itself, using those unit laws and naturality, and cancelling the invertible alpha
components gives both displayed identities. Every new private helper is proved.

The complementary clause of `modulePi_components` no longer depends on the sorry
`AlgebraicGeometry.ProEtale.VaryingRing.modulePi_complement_zero`, attached to
`new-lem-sp-varying-ring-module-pi-complement-zero`. That whole module has no other
Lean importer and its only parent node is updated in this packet.

All three retained sorries belong to `lem-sp-varying-ring-proper-open-pasting`:

- `AlgebraicGeometry.ProEtale.VaryingRing.moduleAlpha_vertical`.
- `AlgebraicGeometry.ProEtale.VaryingRing.moduleAlpha_horizontal`.
- `AlgebraicGeometry.ProEtale.VaryingRing.gamma_evaluation`.

The existing derived pasting and mate proofs are preserved. The helper proofs use
the already stated ordinary evaluation and componentwise exactness interfaces;
there is no assertion that arbitrary derived morphisms are detected by evaluations.

## No longer needed

The proof and its DAG no longer need
`new-lem-sp-varying-ring-module-pi-complement-zero` or its module
`Sheaf.AlgebraicGeometry.VaryingRingModulePiComplementZero`. The source module and
its Lean attachment are preserved; removing its sole import and parent dependency
prunes it from the required work. There is no withdrawal or deletion.

Removed direct proof imports:

- `Sheaf.AlgebraicGeometry.VaryingRingModulePiComplementZero`.
- `Mathlib.CategoryTheory.Adjunction.Mates`.
- `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`.
- `Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization`.
- `Sheaf.CategoryTheory.ConstantLeftModuleInverseImage`.
- `Sheaf.CategoryTheory.LocalizedModuleExactForSystems`.
- `Sheaf.CategoryTheory.RingedSiteModules`.
- `Sheaf.Paper.SemilinearDerivedSections`.
- `WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf`.

Except for the complementary-projection module, these import removals only eliminate
redundant direct imports: their public interfaces already occur through the retained
imports. Their DAG nodes remain needed by the untouched proof plan and are not claimed
as pruned nodes. The constant-ring calculus and ordinary-derived section calculus
remain dependencies.

The conservative command check requests a change record for the added local
proof sections and attributes. See
`coord/changes/varying-ring-proper-open-pasting-proof-scope.md`. No public
interface or consumer changes.

## Where the brief, the DAG or earlier work was wrong

The previously split complementary-projection theorem is unnecessary. Ordinary
system evaluation, the proved constant-ring disjoint-direct-image lemma, and two
ordinary adjunction transposes already prove the vanishing of its target. No false
statement or target-interface change was found. The three remaining
holes are unchanged; no hole is replaced by a renamed copy or a new assumption.

## Second reading by Q2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
