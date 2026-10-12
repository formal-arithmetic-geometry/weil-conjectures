## What changed

Replaced `AlgebraicGeometry.formalSystems_properSupport_serre` with a complete Lean
assembly of Stacks 0CYV. Its signature and all public imports stay unchanged.
The first Serre property uses a proved support-union argument with stalkwise exactness
and the later-kernel quotient; closedness, subsets and finite unions give properness.
The second uses annihilation of later kernels and quotients, and the actual product-ideal
subscheme for extensions. Both include the zero object, using the empty scheme.
Private helpers transport the canonical level lemmas to the zero morphisms induced by
an arbitrary abelian structure, using `Subsingleton (HasZeroMorphisms _)`.

Added the proof-only import `Sheaf.AlgebraicGeometry.IdealModuleProductExactCalculus`
and direct imports of the module stalk functor and exactness. The generic annihilator
calculus is isolated as one new module/node, strictly the annihilator step of the argument:
it mentions no base, properness, formal systems, coherence or Serre classes.

## Proved and sorry left

Closed the original hole `AlgebraicGeometry.formalSystems_properSupport_serre`
(node `lem-weil-pbc-formal-systems-proper-support-serre`); no sorry remains in that module.
All private support, zero-object, union, transport and Serre-criterion helpers are proved.

Added one hole: `AlgebraicGeometry.Scheme.idealModuleProduct_exact_calculus`
(node `lem-weil-pbc-ideal-module-product-exact-calculus`). Its proof is exactly `by sorry`.
This is a decomposition: one upper hole closed, one lower hole added, net zero holes.
Existing imported holes, including formal abelianity, the short-exact level lemma and
constant support, remain existing dependencies and were not duplicated or changed.

## No longer needed

Removed direct proof imports `Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProduct`
and `Sheaf.Topology.PresheafModuleStalkFunctor`. Their definition-level uses remain
available transitively; this is direct-import pruning, not a claim that these modules
leave the targets' import closure.

The original proof-dependency edges to `def-weil-pbc-module-stalk`,
`def-weil-pbc-closed-subset-proper-over-base`, `def-weil-finite-type-morphism`,
`def-weil-closed-immersion`, `def-sbc-closed-immersion-ideal-sheaf`,
`lem-weil-pbc-proper-fp-permanence`, `def-weil-pbc-coherent-formal-module`,
`def-pur-sheaf-tensor-product`, and `def-sbc-ideal-sheaf-powers` are no longer direct
proof steps of the main theorem. Definition dependencies stay in `stmt_deps`, and
the tensor/product definitions needed for annihilator calculus are recorded in its
new node. No blueprint unit statement or realized step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The mathematical plan is sound, including its warning that formal monomorphisms need
not be levelwise monomorphisms. The level lemma is stated with canonical zero morphisms,
whereas the Serre theorem quantifies over any abelian structure. Direct application
fails with a mismatch between `instHasZeroMorphismsFullSubcategory` and
`Preadditive.preadditiveHasZeroMorphisms`. Private transport helpers fix this without
changing any existing signature. The original named instance binder also triggers an
unused-variable linter despite its implicit use in the statement; that linter is disabled
only for this unchanged theorem.

The static checker also flags the file-local zero-object opening/noncomputable scope
and command-local options as an interface change. A change record documents their
locality and the unchanged consumer interface; the tools were not modified.

The Stacks source file is absent from this clone; the existing cited source was read
at https://stacks.math.columbia.edu/tag/0CYV. No new mathematical source was invented.
LeanFinder and Loogle searches found abstract Serre criteria and ring-module annihilator
lemmas, not this sheaf/formal-system theorem. LeanSearch returned HTTP 500 and is recorded
as unavailable. Repository `rg` confirmed no existing generic ideal-product exact calculus.

## New nodes

`lem-weil-pbc-ideal-module-product-exact-calculus`, in
`Sheaf.AlgebraicGeometry.IdealModuleProductExactCalculus`, states annihilation under
monomorphisms and epimorphisms and product annihilation in a complex exact at its middle.
It is step 5 of the original node, sourced to the proof of Stacks 0CYV (2), with complete
sectionwise local-lifting proof in the docstring and node. No Noetherian hypothesis is
needed. Edge cases checked: zero modules and ideals, empty scheme, split sequences;
no injectivity at a formal level is presumed, and exactness is retained for extensions.
All three search kinds are recorded, with the unavailable LeanSearch distinguished.
The static checker treats file-local scope commands as an interface change;
`coord/changes/formalSystems-properSupport-proof-scope.md` records those commands,
the unchanged public signature and the unaffected consumer. No forced adaptations
are required.

## Second reading by C1

1. **Interface comparison:** compared the delivered formal-systems module with the
repository version. The public theorem statement is byte-for-byte unchanged; the only
other module is the new, explicitly split-off calculus. No target statement or existing
declaration was weakened or given extra hypotheses.

2. **Proof checks:** compiled both delivered modules with `lcompile.py --all`. The main
theorem and all private helpers contain no `sorry`; the only remaining `sorry` is the
named theorem `AlgebraicGeometry.Scheme.idealModuleProduct_exact_calculus`, whose node,
source, and proof docstring are present. No forbidden commands or hollow definitions
occur. The expected `sorryAx` is therefore confined to that explicitly open split.

3. **Statement and node review:** checked the new calculus against its Lean type and
the Stacks annihilator argument, including zero ideals/modules, empty schemes, split
sequences, and exactness without a monomorphism assumption on the first arrow. The
statement is strictly the generic lower-level result used by the main proof, not a
restatement of the target. Its DAG `proof`, `proof_deps`, `proof_origin`, searches,
Lean record, and `status: split` agree with the code.

4. **Pruning and route:** verified that the proof uses the support-stalk, local-lifting,
short-exact-level, properness, and product-ideal steps recorded in the updated node.
The removed direct imports and obsolete proof-dependency edges are listed under
`## No longer needed`; the unit statement and realized route remain intact.

5. **Delivery checks:** the dry-run delivery succeeds after this report update; the
only static classification is CODEX because a new node/module and proof-scope record
are delivered. No forced adaptations are required, and no change to a consumer's
interface is needed.
