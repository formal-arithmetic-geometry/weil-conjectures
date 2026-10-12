## What changed

Closed `exists_spread_generic_product_embedding` by a compiling reduction into two
strictly smaller parts of its original argument. The theorem's signature and docstring
are unchanged. Its proof composes the base algebra, proves Noetherianity of the model,
obtains a uniform embedding after localizing the model, descends a multiple of that
localization denominator, and applies the embedding statement to the descended model.

Added two modules, `Sheaf.AlgebraicGeometry.GenericProductLocalization` and
`Sheaf.AlgebraicGeometry.DescendModelLocalization`, each containing one named theorem.
The first has no finite étale base cover conclusion; the second has no finite algebra,
generic splitting, coordinate fields, or embedding hypotheses or conclusion. Neither is
a renamed target statement. All new imports of the original module are proof-only.
Updated the original node's proof, proof dependencies and proof origin to match the Lean.

## Proved and sorry left

Closed: `exists_spread_generic_product_embedding` (one original hole).
Added: `exists_generic_product_localization`, node
`lem-weil-pbc-generic-product-localization`, and `exists_descend_model_localization`, node
`lem-weil-pbc-descend-model-localization`. Each has exactly `:= by sorry` with the source
and the complete argument in its docstring. This is a decomposition, not a complete proof
from sorry-free dependencies: one hole closed and two strictly smaller holes added.

All three modules compile through `lcompile.py`. No signatures or definitions were changed.

## No longer needed

None of the original imports or proof steps is pruned.
The new GenericProductLocalization module omits the unused Etale.Basic,
Morphisms.UnderlyingMap and Spec imports, and imports Finiteness.Defs and
Noetherian.Defs, Ideal.Quotient.Operations and Localization.Away.Basic
directly for its signature. DescendModelLocalization omits the
unused TensorProduct.Basic and Nilpotent.Lemmas imports. The original node had no named
proof dependencies. The two new dependencies partition its four existing steps; the unit
record has no realized steps or statement attached to this node, and its route is retained.
The preliminary unused base-only lemma was removed from the sandbox before this delivery.

## Where the brief, the DAG or earlier work was wrong

The node's proof steps have empty `uses` lists; there are no stated dependency declarations
for those steps to apply. This delivery supplies two new statements to represent the
localization and descent portions of that argument. Searches in both library roots and
Mathlib found no existing theorem supplying either complete part. LeanFinder found
localization injectivity and étale localization ingredients; Loogle found the localization
interface and integral denominator-clearing lemmas. LeanSearch returned HTTP 500, recorded
as unavailable. The actual queries and results are in each new node and the search log.
Blueprint searches for torsion localization, integral denominators, product idempotents,
and finite étale models found no matching blueprint nodes. The source blueprint file is
not installed in this clone's literature directory; the argument here follows the source
place recorded in the existing node and its complete docstring.

Edge cases checked: an empty product has zero generic ring, so the torsion kernel is all
of the finite reduced algebra and localization kills it; the coordinate assertions are
vacuous. For a unit denominator the localization is unchanged. A zero multiple s in the
first theorem cannot admit the assumed fraction field K', so this universally quantified
case is vacuous. In the descent theorem the constant coefficient of a least-degree monic
equation for nonzero t is nonzero, and is divisible by t after mapping to A0. Its numerator
and c0 are nonzero, so their product defines a nonempty principal localization. Finiteness
puts the resulting model in Type u by a small finite-module presentation. The small model
is specified by its localization universal property; no definition chooses arbitrary data
from an unproved mere-existence theorem.

## New nodes

`lem-weil-pbc-generic-product-localization`: realizes the existing node's steps 1--2,
killing the finite torsion kernel and clearing the coordinate idempotent denominators
on the model ring. The conclusion is uniform under subsequent localization at a multiple
of the selected denominator, which is necessary for the descent step.

`lem-weil-pbc-descend-model-localization`: realizes steps 3--4, descending a specified
nonzero model denominator to a principal open of A and transporting the resulting finite
étale cover to Type u. This theorem is independent of B and the generic product data.
No change records or forced adaptations were needed.

## Second reading by B3

1. Compared the original module with the repository using diff and the delivery
   declaration parser. The existing theorem signature is unchanged byte for byte;
   its docstring, visibility and original public imports are unchanged. No definitions
   or target statements change, and there are no change records or adaptations.
2. Compiled all three delivered modules in import order through lcompile.py. The only
   direct holes are the two public named split theorems, each with its complete proof
   docstring and node. No definition, axiom, unsafe, opaque, implemented_by or extern
   is introduced. The axiom check is recorded below.
3. Read both split statements against their hypotheses. They are strictly distinct
   parts: generic localization versus descent of an arbitrary model denominator.
   Checked the empty product, unit denominators and zero multiples; a zero localized
   denominator cannot satisfy the required fraction-field hypothesis. For descent,
   nonzero t has a monic equation with nonzero constant coefficient, which is in (t);
   clearing its c0 denominator gives the required nonempty principal base open.
   Finiteness provides the small model. No definition chooses an arbitrary witness
   from a holed existence theorem. Independent LeanFinder, Loogle and grep searches
   used torsion kernels, annihilators, minpoly and small representations rather than
   the first reader's queries. The existing Module.exists_annihilator_of_subsingleton_
   localizedModule supplies only one ingredient and is itself still open; minpoly
   and small-representation results also do not close either complete split statement.
   Neither split can be closed in a few minutes from these ingredients.
4. The proof really composes the base algebra and proves the model Noetherian before
   combining the two split theorems. It does not merely apply a renamed copy of the
   original result. The original proof_deps list was empty, so no old dependency is
   omitted from No longer needed. Read dag/units/sk-prop-sf-cbc.json: realized.statement
   and realized.steps are empty, and the original four-step localization/descent
   argument is retained below the unit level. This remains a decomposition with
   closure net -1 (one original hole closed, two new holes added), not a sorry-free proof.
5. Existing node changes are exactly proof, proof_deps and proof_origin; the dependency
   union agrees with the two Lean applications. Both new nodes have the required
   source, searches, split status, creation, blueprint, chapter, unit and Lean records.
   Their recorded signatures match the Lean. Corrected copied proof text that still
   referred to B, product fields or A0/S0 absent from the corresponding new statement.

Changes made in this reading: removed unused imports from both new modules, replacing
transitive imports in GenericProductLocalization with the direct signature imports;
removed unused namespace openings; corrected both new nodes' proof plans and the
GenericProductLocalization node's reversed algebra direction; removed that new node's
unused scheme and etale statement dependencies. No existing signature or proof changed.

Axiom verification: a scratch module compiled through lcompile.py with #print axioms
for all three declarations reported exactly propext, Classical.choice, Quot.sound and
sorryAx for each. The two new theorem holes account for sorryAx. The scratch file was
removed before the delivery. All three final modules compile without warnings.
