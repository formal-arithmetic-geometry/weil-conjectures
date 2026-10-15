## What changed

Only `lean/Sheaf/Paper/GeometricFieldProEtaleEvaluation.lean` and its existing DAG node
`lem-weil-pbc-geometric-field-proetale-evaluation` change. All existing signatures,
visibility, definitions and public imports are unchanged. There are no adaptations or
new public declarations. Five original theorem bodies are completed using proved private
helpers and existing Mathlib/source-library APIs.

Exactness follows directly from the weakly-etale section theorem and evaluation of
sheafification at an object whose covering sieves contain the identity. This proves
preservation of colimits without the pending profinite-site classification. Module
colimits then follow from the proved source-library forgetful-functor instance.

Extension compatibility follows from the original restriction-equivalence theorem,
canonical composition of site pullbacks, and cancellation of equivalences. Coherence
and identity follow directly from the conjugate-unit equation, naturality and the
canonical pullback maps. Finite-operation compatibility follows from left exactness
of the specified set-valued inverse image and naturality.

The node keeps steps 1-4 as the plan for the remaining original hole and replaces
steps 5-8 with these implemented arguments. No proper-base-change unit step is bypassed.

## Proved and sorry left

Closed original holes (all names are in `AlgebraicGeometry.ProEtale`):

- `geometric_field_proetale_evaluation_exact`.
- `geometric_field_proetale_evaluation_extension`.
- `geometric_field_proetale_evaluation_coherence`.
- `geometric_field_proetale_evaluation_identity`.
- `geometric_field_proetale_evaluation_operations`.

One original hole remains unchanged:
`AlgebraicGeometry.ProEtale.geometric_field_proetale_evaluation`, node
`lem-weil-pbc-geometric-field-proetale-evaluation`. It still needs the profinite
classification/dense-subsite comparison and transport to module sheaves, as described
in steps 1-4 of its docstring and node. No new holes or split-off modules are added.
This is five holes closed, zero added; extension is a reduction to the existing original
site-equivalence theorem, rather than an independent axiom-free proof.

Single-file compilation passes. Explicit `#print axioms` checks show exactly
`propext`, `Classical.choice`, and `Quot.sound` for exactness, coherence, identity and
operations. Extension additionally depends on the remaining original theorem's `sorry`.
The temporary axiom-print commands were removed from the delivered file.

## No longer needed

Removed these eleven proof imports:

- `Mathlib.AlgebraicGeometry.Scheme`.
- `Sheaf.RingTheory.IndPrincipalZariski`.
- `WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.Affine`.
- `Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory`.
- `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`.
- `Sheaf.CategoryTheory.RingedSiteModules`.
- `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs`.
- `Sheaf.CategoryTheory.SiteInverseImageTensor`.
- `WeilConjectures.RingTheory.Spectrum.Prime.LocallyConstant`.
- `Sheaf.RingTheory.WeaklyEtaleField`.
- `Sheaf.AlgebraicGeometry.ProEtaleRingInverseImage`.

These direct imports are unnecessary for the delivered proofs; some remain available
through the unchanged public dependencies. Their removal does not assert that their
modules have become unreachable from every target.

Removed proof-dependency edge
`lem-weil-pbc-site-abelian-sheaf-epi-locally-surjective`: the sheafification-unit argument
uses Mathlib's image/equalizer covering sieves directly, so no proof of the separate
abelian epi criterion is needed for this item. No modules are withdrawn.

The implemented exactness proof does not need classification of ind-etale algebras,
finite etale field-algebra decomposition, profinite limits, the spectrum of locally
constant functions, or the dense-subsite theorem. Coherence, identity and operation
compatibility also do not need those results. These dependencies remain in the node
because the original site-equivalence hole still needs its plan; they are not claimed
as globally pruned. The extension proof needs the already specified test-base-change
isomorphism, not a new locally constant scalar-extension tensor calculation.

## Where the brief, the DAG or earlier work was wrong

No statement is disputed or changed. The plan overestimates the dependencies needed
for the five secondary assertions: the existing weakly-etale section theorem suffices
for splitting covers, pullback composition already supplies relative test-base-change,
and coherence is formal once the specified adjunction comparisons are used.

The source modules `WeilConjectures.SixFunctors.ProEtale.AlgClosedFieldSite` and
`WeilConjectures.SixFunctors.ProEtale.AlgClosedFieldSiteColimits` contain the relevant
covering/sheafification arguments. Their transitive generic pro-etale star API conflicts
with the finite-coefficient star API already imported by this item's public dependencies.
The delivery therefore uses their short arguments locally with their lower-level proved
APIs; it does not modify either star interface or any other group's module.

## Second reading by D3

1. **Signatures and accidental changes.** Compared the sandbox module and node with the
repository versions. Existing public declarations, definitions, and theorem signatures
are unchanged; the only source changes are proof bodies, proof-only imports, and the
corresponding node proof text/dependencies. No target statement or definition changed.
Verdict: pass.

2. **Compilation and axioms.** Compiled the module alone and all sandbox modules with
`lcompile.py`; both pass without errors. The only remaining `sorry` is the named original
`geometric_field_proetale_evaluation`. The five completed theorems contain no local
`sorry`, axiom, unsafe, opaque, extern, or implemented-by declaration. Their generated
proofs use only the permitted logical axioms, with the extension theorem transitively
depending on the documented original target hole. Verdict: pass.

3. **Statements and split-off work.** Searched the repository and recorded search results
for the helper APIs. No new public statement or split-off node was added. The five closed
theorems retain their original statements exactly and the remaining target hole retains
its original node and documented route. Verdict: pass.

4. **Shortest route and pruning.** Checked the proofs from the target downward. The
sheafification-unit argument, equivalence cancellation, conjugate-unit equations, and
naturality close the five secondary holes without relying on the unfinished profinite
classification. The removed proof-only imports and the removed local-surjectivity proof
dependency are listed above; the original target's dependencies remain because its hole
and steps 1--4 remain open. The unit route is preserved. Verdict: pass.

5. **DAG agreement.** Checked the changed node's proof steps, `proof_deps`, and
`proof_origin` against the delivered code. Steps 1--4 remain the route for the open
target; steps 5--8 describe the implemented helpers and completed theorems. No new node
requires a record. Verdict: pass.

**Changes made during this second reading:** no mathematical or interface repair was
needed. I added this audit only; the delivered source and node remain as reviewed.
