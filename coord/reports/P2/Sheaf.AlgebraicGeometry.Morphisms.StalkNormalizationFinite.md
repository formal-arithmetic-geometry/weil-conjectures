## What changed

Replaced the sole sorry in `Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationFinite`
with a complete Lean proof from the affine integral-closure lemma. For nonempty C, the existing
`smooth_connected_generic_geometry_core` supplies integrality and normal stalks, and Mathlib
supplies Noetherianity. The proof identifies every normalization chart with a finite algebra,
constructs global finiteness, and pulls it back to the local total space. The empty C case is
an isomorphism into an empty scheme. The original declaration signature and public imports
are identical. A declaration-scoped unused-variable linter setting retains the original
hypotheses that this stronger finiteness argument does not use.

Added two modules, each with one public theorem:
`FiniteEtaleOpenIntegralClosure` is proved: it derives normality of the affine base ring from
normal stalks, embeds sections into the generic algebra, decomposes that finite etale algebra
into its residue fields, applies Mathlib `IsIntegralClosure.finite` to each field, and injects
the desired integral closure into the resulting finite product. `FiniteEtaleOpenGenericAlgebra`
contains the remaining geometric statement, with a complete source-based proof in its
docstring. No definition, axiom, target signature, or module held by another group was changed.

The source read for the shorter finiteness argument is Stacks 032L,
`lemma-Noetherian-normal-domain-finite-separable-extension`; the generic geometry uses
02GL, `lemma-etale-over-field`, and 081I, flat base change of scheme-theoretic images.
The existing DAG already records 032L as
`lem-weil-pbc-noetherian-normal-separable-integral-closure-finite`; no duplicate leaf was added.
Searches ran through msearch (LeanFinder, Loogle and grep; LeanSearch returned HTTP 500).
Blueprint and DAG searches found no existing declaration of the generic section embedding
or of the affine open-cover integral-closure conclusion.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Scheme.GaloisCover.stalk_normalization_finite`
(node `lem-sbc-stalk-normalization-finite`). Its proof body contains no sorry.
Also proved the new theorem
`AlgebraicGeometry.Scheme.finiteEtale_open_integralClosure_finite`
(node `lem-sbc-finite-etale-open-integral-closure`), including the empty affine-open case.

Exactly one new hole remains:
`AlgebraicGeometry.Scheme.exists_finiteEtale_open_generic_algebra`
(node `lem-sbc-finite-etale-open-generic-algebra`), whose proof is exactly `:= by sorry`.
Its conclusion is an injective map of section algebras into a finite etale generic algebra;
it says nothing about normalization or its finiteness, and requires neither normality,
Noetherianity, smoothness, a group action, nor a boundary point. The independent integral
closure argument is written and checked in Lean. This is a decomposition: one original hole
closed and one lower hole added, net zero for these declarations. Existing dependencies of
`smooth_connected_generic_geometry_core` may still carry sorryAx. This delivery does not claim
an axiom-free proof of the project targets. Existential generic-algebra witnesses are used
only inside a proposition proof; no definition chooses data from an unproved existence theorem.

All three sandbox modules compile with lcompile. Mathematical edge cases checked: C empty;
V empty (proved separately); U empty (zero section and generic algebra); empty finite cover;
nonempty covers with multiple generic field factors; the identity cover; positive characteristic
with degree divisible by the characteristic (separability suffices, degree invertibility is not
used). Normality is essential only when invoking 032L for the affine base ring, and is explicitly
established before that invocation.

## No longer needed

Removed these proof-only imports and their corresponding direct proof dependencies:

- `Sheaf.AlgebraicGeometry.Morphisms.GenericFibreActionExtension`,
  node `lem-sbc-generic-fibre-action-extension`.
- `Sheaf.RingTheory.FlatLocalDepthFormula`,
  node `lem-weil-pbc-flat-local-depth-formula`.
- `Sheaf.RingTheory.NormalLocalDepthTwo`,
  node `lem-weil-pbc-normal-local-depth-two`.

The finiteness sublemma no longer needs their action-extension, normal-depth-two,
and flat-depth-formula dependency branches. It also does not need separate tame normalization,
ramification-index, DVR, coherent depth-two extension, or normalization/localization comparison
modules. Those inputs were mentioned in the old prose plan without corresponding direct
imports. No original public import was removed. The new generic-algebra module imports only the
statement interfaces; its unused Normalization import was removed, and the stronger
Etale.Field import is proof-only in the integral-closure module. Global pruning of a removed branch depends on whether
other target-reachable modules also import it; this report asserts removal from this item's route.

## Where the brief, the DAG or earlier work was wrong

The old proof plan conflated finiteness with the stronger tame/depth-two extension properties.
Finiteness itself already follows from normal Noetherianity and generic separability, by 032L.
The three old stated dependencies do not assert finite normalization, nor do they supply the
missing tame or coherent extension theorems named in the old prose. The shorter route avoids
that gap and identifies the actual Mathlib normalization directly on its affine charts.

This is below the spreading unit: only the local finiteness sublemma changes. The trait
etaleness test, purity argument, depth-two etaleness computation, limit reduction, and maximal
open argument of `sk-prop-input-spreading` remain the responsibility of their existing nodes.
No unit statement or realized step is replaced. The recorded ancestor utility cannot follow
`created.item` here because an earlier record names a Lean module rather than a DAG id;
the existing item's explicit `blueprint.from.node` supplies the ancestor for the new nodes.

## New nodes

`lem-sbc-finite-etale-open-generic-algebra`, in
`dag/nodes/sec-smooth-base-change/lem-sbc-finite-etale-open-generic-algebra.json`, records the
remaining geometric restriction-and-injectivity argument. Its module is
`Sheaf.AlgebraicGeometry.Morphisms.FiniteEtaleOpenGenericAlgebra`. This is strictly a part
of the finiteness argument, with no integral-closure assertion. Its proof uses the existing,
Lean-closed flat scheme-theoretic dominance node as a tool.

`lem-sbc-finite-etale-open-integral-closure`, in
`dag/nodes/sec-smooth-base-change/lem-sbc-finite-etale-open-integral-closure.json`, records
the proved affine algebra argument. Its module is
`Sheaf.AlgebraicGeometry.Morphisms.FiniteEtaleOpenIntegralClosure`. Its proof dependencies
are the generic embedding and the existing Mathlib leaf for 032L. The original finiteness
node is updated only in `proof`, `proof_deps`, and `proof_origin` to match the compiled route.
No change record is needed because no existing statement, definition, or public import changes.

## Second reading by P2

1. **Visible changes and signatures.** Compared each delivered module with the repository
   version. The existing theorem signature is byte-for-byte unchanged; the two additional
   modules contain the declarations recorded by their new DAG nodes. Verdict: pass.
2. **Proof checks.** Compiled all three modules with `lcompile.py --all`; no errors or warnings.
   The only remaining `sorry` is the explicitly named generic-algebra theorem, with its
   source-based docstring and matching node. No forbidden declarations or hollow definitions
   occur. Verdict: pass, with one documented split-off hole.
3. **Statements and novelty.** Checked the new theorem statements against their docstrings,
   edge cases, and repository searches. The generic-algebra result is a strictly smaller
   embedding claim; the integral-closure result is the finite algebra consequence. Neither
   duplicates an existing declaration, and both retain the exact needed hypotheses. Verdict:
   pass.
4. **Pruning and route.** The proof uses the shorter normal-Noetherian integral-closure route.
   The three obsolete proof-only imports and their dependency branches are listed above;
   public imports and the unit's realized route remain intact. Verdict: pass.
5. **DAG agreement.** Read the three node files and matched each `proof`, `proof_deps`,
   `proof_origin`, Lean module, declaration, and split status to the code. The original node
   records only the changed proof route. Verdict: pass.

I changed only the proof bodies/imports described above, added the two split-off modules and
nodes, and added this second-reading record. No target statement, existing public declaration,
or definition was changed.
