## What changed

Proved `AlgebraicGeometry.exists_perfect_rhom_dual` without changing its signature or
public imports. The proof defines the dual to be the actual shared RHom object,
constructs its local bounded finite free models, proves perfection and pseudo-coherence
from those models, and uses the existing pseudo-coherent-to-quasi-coherent theorem to
bundle it in the full subcategory. The equality of underlying objects is `rfl`.

Added two modules and their DAG nodes:

- `Sheaf.AlgebraicGeometry.StrictlyPerfectFiniteFreeRefinement` states the remaining
  affine finite free refinement of a specified strictly perfect local representative.
- `Sheaf.AlgebraicGeometry.FiniteFreeDerivedDualModel` proves the local finite free
  dual computation. Its witness is the existing, explicitly constructed ordinary
  Hom complex with the unit module in degree zero. The proof constructs the inverse
  of the sole nonzero product projection, proves bounds `[-b,-a]` and finite freeness,
  identifies the restricted actual derived unit using the exact-functor comparison,
  and applies the existing strictly perfect RHom computation.

Updated the original node's proof, proof dependencies and proof origin to match the
Lean proof. All work is in the sandbox; no target, definition, existing signature or
other group's module was changed. No agents were started and nothing was pushed.

Read the sources [Stacks 08DQ](https://stacks.math.columbia.edu/tag/08DQ),
[08E5](https://stacks.math.columbia.edu/tag/08E5),
[08C4](https://stacks.math.columbia.edu/tag/08C4),
[08CM](https://stacks.math.columbia.edu/tag/08CM) and
[00NX](https://stacks.math.columbia.edu/tag/00NX) on the official Stacks site, since
this checkout does not contain the literature's `.tex` files.

## Proved and sorry left

Closed the original hole in `AlgebraicGeometry.exists_perfect_rhom_dual`
(node `lem-pc-perfect-rhom-tensor-comparison-dual`): 1 of 1 original holes closed.
There is no `sorry` in the item's module.

Also proved the new public theorem
`AlgebraicGeometry.Scheme.exists_bounded_finiteFree_derived_dual_model`
(node `lem-pc-finite-free-derived-dual-model`) and all its private helpers:
`isIso_dependent_projection`, `homComplex_dual_term_iso`,
`restricted_derived_unit_iso` and `homComplex_dual_bounded_finiteFree`.
The dual-model theorem uses the already-stated strictly perfect RHom computation,
whose proof remains a separate project item.

Exactly one hole is added and left in the delivery:
`AlgebraicGeometry.Scheme.exists_finiteFree_refinement_of_isStrictlyPerfect`
(node `lem-pc-strictly-perfect-finite-free-refinement`). Its theorem has proof exactly
`by sorry`, a complete proof in words, and its own new module. It only refines one
specified local representative, with no RHom, dual, global perfection conclusion or
quasi-coherence conclusion. It is strictly part of the original argument.

This is a decomposition: one original hole closed, one new hole added, net zero
holes before accounting for dependency imports. It is not a claim that all imported
lemmas or the target's full dependency closure are sorry-free.

The complete three-file sandbox compiles with no errors or warnings, with each file
within the single-file time limit. No local derived monoidal structure or additional
`HasDerivedCategory` hypothesis was assumed. The remaining statement was checked on
the empty scheme (there is no point to instantiate), zero complex, empty degree
interval, and rank-zero terms. Its bounds and ranks are local and need not be uniform
on a non-quasi-compact scheme. The proved dual computation covers these same degree
and rank edge cases; its bounds follow from the integer inequalities in Lean.

## No longer needed

Removed the direct proof import
`Sheaf.AlgebraicGeometry.StrictlyPerfectDerivedInternalHom` from the item's module;
it is used and imported by the new, proved `FiniteFreeDerivedDualModel` module.
This is a relocation, not global pruning. The other original proof import,
`Sheaf.Paper.DerivedInternalHomRestrictOpen`, is used directly.

No original proof-dependency node or module can be pruned globally: both original
computational dependencies remain needed. The proof does not need
`PerfectFiniteFreeResidueModel`, `PerfectPseudoCoherentLocallyFiniteTor`,
`RHomSupportedQuasiCoherent`, or the original comparison's evaluation/biduality
modules. None was imported. In particular it avoids a circular use of the
perfect tensor-Hom comparison. Public imports of the existing module are unchanged.

## Where the brief, the DAG or earlier work was wrong

No false statement or unit-route error was found. The original node's one prose step
combined local finite free refinement, the ordinary dual calculation, local-to-global
perfection and quasi-coherence without interfaces for the first two. They are now
separate statements, and the dual calculation has been proved in Lean.

Two tempting existing interfaces cannot simply be applied here:
`exists_finiteFreeResidueModel` needs derived categories on residue-field spectra and
prescribes fibre ranks, while
`perfect_isPseudoCoherent_and_hasLocallyFiniteTorDimension` additionally requires
derived categories of the open schemes. These instances are not binders of the
assigned theorem, and its arbitrary morphism universe must be preserved. The new
refinement uses just the global and localized-site derived categories already given.
The existing pseudo-coherent-to-quasi-coherent theorem has exactly those binders and
is used without alteration.

The first attempt to elaborate the explicit dual calculation unfolded geometric
aliases excessively and hit the time limit. Keeping the pure Hom-complex calculation
in generic private helpers in the same file resolves this; no module was split to
avoid the limit, and no definition of the library was changed.

## New nodes

`lem-pc-strictly-perfect-finite-free-refinement` is the sole remaining hole. Its module
is `Sheaf.AlgebraicGeometry.StrictlyPerfectFiniteFreeRefinement`. Its proof restricts
the given termwise splittings to an affine, identifies their images with finite
projective modules, applies the existing standard free cover to finitely many terms,
intersects principal neighbourhoods of the specified point, and transports the given
derived representative isomorphism through exact nested restriction. Its dependencies
include the existing affine tilde-Gamma equivalence and standard free cover. These
are generic algebraic tools; no unit statement or realized step was bypassed.

`lem-pc-finite-free-derived-dual-model` records the proved public theorem in
`Sheaf.AlgebraicGeometry.FiniteFreeDerivedDualModel`. The ordinary dual's bounds,
finite free terms, actual tensor-unit comparison and assembly are proved; the
ordinary-to-derived comparison uses the existing `lem-pc-rhom-strict-perfect-hom`.
The statement is local to one affine and one bounded finite free complex, and has
no global perfectness or quasi-coherence assertion.

For both nodes, LeanSearch was tried and returned Internal Server Error; LeanFinder
and repository/Mathlib grep were completed and are recorded. Existing similar nodes
were read rather than duplicated: the residue-rank local model needs extra instances,
and the strictly perfect Hom lemma does not itself supply a bounded finite free dual
or the comparison with the restriction of the actual global tensor unit.
No change record is needed because no existing statement or definition changed.

## Second reading by X3

1. **Unchanged interface — PASS.** Compared every delivered module with the repository.
   The only existing module is PerfectRHomTensorComparisonDual; its complete theorem
   signature is byte-for-byte identical, and its public imports are unchanged. No target,
   definition or existing declaration was altered. Both other modules are new.
2. **Kernel proofs and holes — PASS.** Compiled all three modules through lcompile.py
   in dependency order (22.6, 6.9 and 10.1 seconds), without errors or warnings. Compiled
   scratch copies with `#print axioms` for all three public theorems and all four private
   helpers. Their axiom sets contain only propext, Classical.choice, Quot.sound and,
   where imported unfinished statements are used, sorryAx. The dependent-projection
   helper uses no axioms; the termwise dual and bounds/freeness helpers have no sorryAx.
   There is exactly one textual hole, the named refinement theorem's whole proof.
   No forbidden declaration or hollow definition was added. D is explicitly the existing
   Hom complex, and the global dual is explicitly the shared RHom object; choosing
   projection and isomorphism proofs inside theorem proofs adds no arbitrary public data.
3. **Split statements and search — PASS.** Read both new statements, their nodes and
   natural-language proofs, against [Stacks 08DQ](https://stacks.math.columbia.edu/tag/08DQ),
   [08C4](https://stacks.math.columbia.edu/tag/08C4),
   [08CM](https://stacks.math.columbia.edu/tag/08CM) and
   [00NX](https://stacks.math.columbia.edu/tag/00NX). The remaining refinement is true:
   on an affine, split finite free sheaves are sheaves of finite projective modules;
   finitely many principal trivializations can be intersected around the given point.
   Zero terms, rank zero, reversed/empty degree bounds, the empty scheme and lack of
   global quasi-compactness cause no extra hypothesis. It does not restate the original
   dual theorem. Independently searched LeanFinder for local freeness of a direct summand,
   Mathlib grep for projective/free lemmas, and repository grep for local finite free
   complex models. No exact existing interface was found. Loogle could not resolve the
   upstream homObj name, so that search supplies no negative evidence. Read the residue
   model and perfect-to-pseudo-coherent alternatives: each requires additional derived
   category instances absent from the existing signature. The sheaf/site comparisons
   needed to formalize the refinement are substantial; its hole cannot be closed by a
   short application of these alternatives.
4. **Top-down route and pruning — PASS.** Read the proof starting with the original
   target hole and followed every local model and isomorphism. Checked variance in the
   first RHom argument, the actual global tensor unit comparison, reflected bounds
   [-b,-a], and the construction of both perfect and pseudo-coherent witnesses.
   Direct proof imports match the argument; public imports of the new modules are used
   by their statements. Both original dependency nodes remain used (the strictly perfect
   RHom computation now through the proved dual-model module), so no global pruning is
   claimed. The report lists this relocation. The unit record has empty statement/step
   realization lists; no listed realization or unit-level step is removed, and this is
   a local refinement of the original dual-computation argument.
5. **DAG agreement — PASS.** Checked each new node's statement against its Lean
   signature, its source, creation/provenance and search records, and its proof steps
   against the code or the remaining refinement argument. The existing node differs
   only in proof, proof_deps and proof_origin. The old RHom dependency is retained
   transitively in the dual-model node, and the new direct dependencies describe the
   actual local-model, restriction and quasi-coherence proof.

Second-reading changes: fixed `anaffine` to `an affine` in the refinement theorem's
proof docstring and added this review. No proof, signature, import, definition or DAG
change was necessary. One original hole is closed and one lower hole remains added:
this delivery is a decomposition with net zero holes before dependency accounting.
