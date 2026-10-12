## What changed

`Sheaf.AlgebraicGeometry.ReducedProductLocalization.reduced_product_localization`
now has a complete proof along the original localization/reduction/product route.
Tensor congruence, `cancelBaseChange`, and `commRight` identify the base-changed
algebra. `Ideal.map_radical_of_surjective` transports its reduction, while
`IsLocalization.map_radical` and `tensorQuotientEquiv` commute reduction with
localization. Tensoring the supplied splitting and applying `piRight` completes
the proof, including the empty product.

Removed the earlier worker's two unnecessary case modules and their new nodes.
Narrowed the public tensor-product import from `Maps` to `Basic`, which provides
the tensor structures occurring in the unchanged signature. The added imports
`Localization.BaseChange`, `Localization.Ideal`, `TensorProduct.Quotient`, and
`TensorProduct.Pi` are plain imports because only the proof needs them.
The public `Ideal.Quotient.Operations` import is necessary for the quotient
algebra instances in the statement. No definition or declaration signature changes.

## Proved and sorry left

Closed the one original hole: `reduced_product_localization`
(node `lem-weil-pbc-reduced-product-localization`). Added zero holes.
No `sorry` remains in the delivery. This is a complete proof, not a decomposition.
The earlier proposed holes `reduced_product_localization_zero` and
`reduced_product_localization_pos` were removed together with their modules;
they are not delivered as either proved statements or outstanding work.

The final module compiles without warnings through `lcompile.py`.
A scratch copy with `#print axioms reduced_product_localization` compiles and
prints exactly `[propext, Classical.choice, Quot.sound]`.

## No longer needed

The proposed modules `Sheaf.AlgebraicGeometry.ReducedProductLocalizationZero`
and `Sheaf.AlgebraicGeometry.ReducedProductLocalizationPos`, and their proposed
nodes `lem-weil-pbc-reduced-product-localization-zero` and
`lem-weil-pbc-reduced-product-localization-pos`, are removed from this sandbox
and are not delivered. They were never part of the repository's dependency
baseline. The original node has empty `proof_deps`, so there are no old DAG
proof dependencies to prune and no existing Sheaf modules made unreachable.

The public import `Mathlib.RingTheory.TensorProduct.Maps` is replaced by
`Mathlib.RingTheory.TensorProduct.Basic`; the proof obtains `Maps` privately
through its proof imports. The original quotient and localization statement
imports remain necessary.

## Where the brief, the DAG or earlier work was wrong

The first worker's zero/positive case split did not supply any of the substantive
localization argument. The positive case merely retained the whole argument
under a positivity hypothesis. Both new JSON statements also incorrectly
restated the unrestricted parent statement instead of their actual signatures,
and their docstrings did not give complete standalone proofs.
The finite-product Mathlib equivalence already handles empty products, so an
extra case split is unnecessary. The original DAG route is valid and is now
fully implemented; there is no established error in the unit or chapter route.

## Second reading by C3

1. Compared the sandbox module against the repository with `diff` and an exact
   textual comparison of the theorem signature. Verdict: every existing
   declaration signature is byte for byte unchanged. Only this module, its
   original node's proof fields, the import change record, and this report are delivered. No definition
   changed; the public-import narrowing has its own change record.
2. Compiled the original proposed set, then the repaired final module through
   `lcompile.py`. The final module has no warnings, errors, `sorry`, prohibited
   declarations, or hollow definitions. The independent scratch axiom check
   prints only `propext`, `Classical.choice`, and `Quot.sound`. Verdict: pass.
3. Read both proposed split-off statements and their nodes. Rejected the
   redundant case split and removed both statements/nodes. Searched with
   Lean Finder for reduction of localization as base change of a nilradical
   quotient, Loogle for `Algebra.TensorProduct.cancelBaseChange`, and `rg` in
   Mathlib and both library roots for nilradical/base-change/product results.
   Mathlib supplies every required step; no new statements are needed.
   Checked the empty finite product, the one-factor case, zero rings, and
   localization at zero or a nilpotent: the proof uses neither nontriviality
   nor positive cardinality nor a nonzero localization parameter. Verdict: pass.
4. Read the original node and `dag/units/sk-prop-sf-cbc.json`. Its `realized`
   statement and step lists are empty; this node is an auxiliary localization
   tool, and the original unit/chapter route is retained. The final proof takes
   the direct Mathlib route with no Sheaf proof dependencies. Statement imports
   are public; the added proof imports are private. `No longer needed` lists
   all removed proposed nodes/modules and the narrowed import. Verdict: pass.
5. Updated the original node's `proof`, `proof_deps`, and `proof_origin` to the
   exact tensor/base-change, reduction, and finite-product composition in Lean.
   All other node fields are retained from the repository. There are no new
   nodes or unrecorded open declarations. Verdict: pass.

Second reading changed: replaced the unproductive case split with a complete
Mathlib proof, removed both split-off modules/nodes, narrowed the statement
import, corrected the DAG proof metadata, and rewrote the report.

## Change records

`coord/changes/reduced_product_localization_imports.md` records the narrowed
public import. The sole direct importer, `RefineFiniteDomainSplitting`, already
publicly imports `TensorProduct.Maps` and compiles unchanged against this
delivery in a separate scratch validation set. No adaptations are delivered.
