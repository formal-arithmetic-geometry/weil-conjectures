## What changed

Proved `SheafOfModules.IndFiniteFree.ind_finite_free_scalar_model` with its signature and every existing definition unchanged. Private proved helpers construct the normalized ordinary extension/tensor comparison at independent universes, transfer finite-limit preservation from finite free stages through exact colimits, build the termwise chain comparison, and construct coefficient maps by the normalized ordinary adjunction. Fully faithful precomposition with derived localization supplies the coefficient map on derived categories and its counit square.

Added private proof imports `WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification` for the sheafification comparison and `Mathlib.CategoryTheory.Monoidal.Limits.Preserves` for tensor preservation of colimits.

The preflight requests a change record for the new scoped `variable` commands of private helpers. `coord/changes/ind-finite-free-scalar-model-private-proof-scopes.md` documents them and the unchanged public API; the downstream check found zero current importers and no consumer adaptations.

The node proof now records finite-biproduct exactness and the direct counit-naturality argument. No source-library module, existing public definition, or consumer is changed.

## Proved and sorry left

Closed the single hole in `SheafOfModules.IndFiniteFree.ind_finite_free_scalar_model` (node `lem-sfb-ind-finite-free-scalar-model`). Holes added: zero. Holes left in the delivered module: zero. Every private helper is proved. The theorem uses the existing exact-functor-derived-functor and ordinary-adjunction interfaces; no new assumed result is introduced.

Validation: server compilation and the declaration/axiom probe passed (50.0 seconds; 14 declarations probed; no holes or forbidden axioms reported). The unused-variable warning has been addressed without changing the signature, and the subsequent compilation and axiom probe passed before server preflight requested the proof-scope change record. The delivery command repeats compilation and preflight before pushing. Existing public signatures and definition bodies are unchanged.

## No longer needed

Removed proof imports:

- `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed` / `lem-pc-sheaf-modules-tensor-closed`: finite-free exactness uses finite biproducts and tensor colimit preservation directly; the tensor structures are already in the public coefficient-universe API.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.ExtensionTensorComparison` / `lem-weil-pbc-extension-tensor-comparison`: its same-universe comparison is proved privately at the independent universes required here, following its sheafification proof.
- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients` / `lem-pc-kflat-resolution`: invertibility of the universal counit follows from exactness. Its naturality proves the displayed formula for every quasi-isomorphism, so no existence or choice of a K-flat resolution is used.

These dependencies are removed from this node's proof and obsolete tool approvals. Their modules and declarations remain available for other consumers. No modules are withdrawn.

## Where the brief, the DAG or earlier work was wrong

The planned extension comparison was stated only with site and coefficient universes equal, whereas the assigned theorem retains independent universes. Its proof generalizes without changing public interfaces. The original plan also requested a K-flat resolution although the conclusion quantifies over an already supplied quasi-isomorphism: exactness and counit naturality suffice. The unit route is unchanged.

## Second reading by U9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
