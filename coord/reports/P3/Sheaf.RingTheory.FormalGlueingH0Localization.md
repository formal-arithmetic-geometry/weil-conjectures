## What changed

Reduced `FormalGlueing.exists_unique_bijective_h0_localization`, without changing its
signature, to one strictly smaller numerator-lifting statement in the new module
`Sheaf.RingTheory.FormalGlueingH0ChartPowerLift`.

The item's complete Lean proof extracts the compatibility equations, proves that a
section with zero chart coordinate is killed by one localization denominator, and
uses the new power-lifting statement to establish the remaining localization axiom.
`IsLocalizedModule.linearEquiv` constructs the bijective map and
`IsLocalizedModule.ext` proves uniqueness. The two private helpers are fully proved.
The finite product denominator argument for injectivity is supplied by Mathlib's
`IsLocalizedModule.prodMap` and `IsLocalizedModule.pi` instances.

Added a proof import of `Mathlib.RingTheory.TensorProduct.IsBaseChangePi` and the new
chart-power-lift module. Removed the item's direct imports of the canonical-maps
and data modules. Its public imports and all existing signatures are unchanged.
The parent's DAG proof and proof dependencies now describe the actual reduction.
No definition, interface, target, or other existing module was changed.

Validation: both sandbox modules compile cleanly through `lcompile.py --all`, with
no warnings. The source was checked at Stacks tags
[05EL](https://stacks.math.columbia.edu/tag/05EL),
[05EQ](https://stacks.math.columbia.edu/tag/05EQ),
[05EP](https://stacks.math.columbia.edu/tag/05EP), and
[05ER](https://stacks.math.columbia.edu/tag/05ER).
The new lemma's proof explicitly supplies the denominator calculation omitted in
05EQ. Edge cases checked: an empty chart index set supplies no `i`; if `f i = 0`
then its localization ring and every module over it are zero; zero rings and zero
modules are included; if `f i` is a unit, the argument permits exponent zero.
No arbitrary data is chosen from the new existence statement: it is used only
inside a proof of the localization axioms. The equivalence is Mathlib's universal
localization equivalence, whose object is uniquely determined.

## Proved and sorry left

Closed the sole original hole:
`FormalGlueing.exists_unique_bijective_h0_localization`
(node `lem-weil-pbc-formal-glueing-H0-localization`).

Added one hole:
`FormalGlueing.h0_chart_power_lift`
(node `lem-weil-pbc-formal-glueing-H0-chart-power-lift`).
There are no holes left in the item's module. This is a decomposition (one hole
closed, one added), not a claim that the entire chart-isomorphism argument is now
sorry-free. The numerator-lifting statement contains only the surjectivity part;
the original injectivity, map construction, normalization, and uniqueness are
proved here. Existing upstream holes in formal-glueing data and canonical maps
remain unchanged.

## No longer needed

Removed direct proof import `Sheaf.Paper.FormalGlueingCanonicalMaps` from the item.
That module is still the planned proof dependency of the new power-lift lemma,
which imports it, so it is not claimed to leave the targets' import closure.
Removed direct proof import `Sheaf.RingTheory.FormalGlueingData` from the item;
the same definitions remain available through the public H0 import.

Node `lem-weil-pbc-localization-module-exact` is no longer needed in this proof
route. Kernel localization exactness has been replaced by the explicit
compatibility equations and finite product localization universal property.
The new numerator-lift proof also clears denominators directly, so it does not
need that exactness node. This was a planned node dependency, not an imported
module in the original item: no existing library module is claimed globally
unreachable solely from this delivery.

Node `def-weil-module-base-change` is also no longer a direct proof dependency
of the parent: its proof does not use scalar-extension operations. Scalar extension
remains part of the glueing-data definitions and of the new numerator-lift argument,
so this does not claim to prune its module from the targets' import closure.

The canonical-maps node is no longer a direct proof dependency of the parent,
but remains needed by the new numerator-lifting node. All unit-level statements
and realized proof steps in `dag/units/sk-thm-p1.json` are preserved.

## Where the brief, the DAG or earlier work was wrong

The original node's page-length finite equalizer/inverse-tuple plan was not
already expressed by its imported theorem declarations: the data and
canonical-maps modules provide structural maps and their properties, not
compatible numerator lifts. The new node isolates exactly that missing
surjectivity construction. Nothing in the existing statement is disputed.

`IsScalarTower R (Localization.Away (f i)) (piece (f i) (X.M i))` was not synthesized
from the existing restricted-scalar chart interface. The proof supplies this
local proposition instance using Mathlib's restriction-of-scalars scalar formula
and `mul_smul`; no interface change or forced adaptation was necessary.

The repository's literature source files are not present on this machine, so
source verification used the official Stacks tag pages. LeanSearch returned
Internal Server Error on two attempts; this is recorded as unavailable, not a
claim of absence. LeanFinder, Loogle, Mathlib grep, repository grep, and the
blueprint duplicate search completed without a matching chart-power-lift lemma.

## New nodes

`lem-weil-pbc-formal-glueing-H0-chart-power-lift` states that every chart element
has a power multiple in the image of the compatible-section projection. Its
new module contains one public theorem with `:= by sorry`, a source, and a full
proof in words. The node inherits the parent's chapter and unit and points to
the same finite-etale-lifting blueprint ancestor. Its construction and
compatibility steps reuse the parent's inverse-tuple calculation; its final
step clears finitely many denominators and errors. There are no change records.

## Second reading by P3

1. **Interface preservation: pass.** Read both delivered modules and compared the
   parent against the repository with `diff`. The existing public theorem signature
   is byte-for-byte identical, as are its universe and variable declarations and
   public imports. Only its proof, private proved helpers, proof imports, and proof
   explanation change. The other module is new; no definition or target changes.
   The parent node changes only `proof`, `proof_deps`, and `proof_origin`.
2. **Proof and trust: pass as a decomposition.** Independently compiled both files
   in import order with `lcompile.py --all`: no errors or warnings. Compiled scratch
   copies with `#print axioms` for both helpers, the parent theorem, and the new
   theorem. Each lists only `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`;
   the helpers inherit existing data-construction holes, and the parent additionally
   depends on the reported new lifting hole. No forbidden declaration or hollow
   definition is introduced. The sole new `sorry` is the entire proof of the named
   public `FormalGlueing.h0_chart_power_lift`. No data construction selects an
   arbitrary witness from it: its witnesses are consumed only in a proposition proof.
3. **Split statement: pass.** Read the actual `square` and `cocycle` fields and the
   canonical-map statements. Checked the inverse localized tuple, self-overlap
   identity, common numerator, and clearing of finitely many compatibility errors
   in the docstring against Stacks 05EL, 05EQ, 05EP, and 05ER. The statement isolates
   denominator-surjectivity; it does not include injectivity, uniqueness, or the
   construction of a localized equivalence, which are genuinely proved in the parent.
   For an empty index set there is no `i`; a zero parameter gives a zero chart;
   zero rings/modules cause no exception; a unit parameter permits exponent zero.
   Repeated searches with different wording using LeanFinder, Loogle, Mathlib grep,
   and repository `rg` found general finite-denominator and kernel-localization
   tools, but no theorem constructing this compatible tuple. In particular,
   `IsLocalizedModule.exist_integer_multiples_of_finite` clears an existing finite
   localized family; it does not establish its square/cocycle compatibility. Closing
   the new hole requires that remaining coherence argument, not a short application
   of a search result. The new lemma has its full proof in words and its own node.
4. **Route and pruning: pass after report correction.** The parent uses Mathlib's
   finite-product localization instances, `isLocalizedModule_id`, `linearEquiv`,
   and `ext`, with the new hole only at surjectivity. The added Mathlib proof import
   supplies precisely the product/Pi instances; the new lemma retains the canonical
   maps import for its stated remaining proof. Public imports are required by
   signatures. Checked every removed old dependency: exactness, canonical maps,
   and module base change. Added the omitted module-base-change entry to
   `No longer needed`. None is claimed globally unreachable; there is no module
   pruned from the targets' closure. The unit `sk-thm-p1` and its `realized` routes
   are untouched, and this reduction is below the unit level.
5. **DAG agreement: pass.** The parent's four steps describe the compatibility,
   common-annihilator, power-lift, and localization-universal-property proof actually
   written. Both nodes' `proof_deps` equal the union of the step `uses` lists. The
   new node has the required source, searches, origin, creation record, blueprint
   ancestry, chapter/unit, and verbatim Lean signature. It is used only in the
   parent's denominator-surjectivity field.

Second reading changed only this report: completed the removed-dependency inventory
and recorded the independent review and axiom checks. The Lean proofs and node files
needed no repair. One original hole closed and one strictly smaller hole added;
net zero holes, one decomposition, no globally pruned module.
