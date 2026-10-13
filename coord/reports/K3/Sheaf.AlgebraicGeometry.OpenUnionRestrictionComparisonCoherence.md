## What changed

Proved `AlgebraicGeometry.Scheme.open_union_restriction_comparison_coherence`
without changing its signature or visibility. Constructed the shared `qI` explicitly
from the supplied `qIY` and the canonical intersection composition isomorphism.
For each overlap, descend the comparison between the two ambient restriction
routes first through restriction to the union and then through restriction to
its inverse-image open. Evaluate those descent identities and cancel the mapped
composition isomorphism to prove both required equations.

Added the proved module
`Sheaf.AlgebraicGeometry.DerivedOpenRestrictionIsoDescent`, containing
`AlgebraicGeometry.Scheme.derived_open_restriction_iso_descent`. Its proof applies the existing proved
`AlgebraicGeometry.schemeDerivedOpenRestriction_isLocalization` and Mathlib's
`Localization.fullyFaithfulWhiskeringLeft`, then lifts the supplied isomorphism
with `preimageIso` and proves its exact image with `map_preimage`. Thus no resolution
hypotheses or new unproved intermediate results are needed. Both modules retain the module
system header and use ordinary proof-only imports for proof dependencies.

Updated the original node's proof, proof dependencies and proof origin to this
shorter route. Added a matching node for the proved descent theorem. No existing
statement, definition, public import or target was changed.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Scheme.open_union_restriction_comparison_coherence`
(node `lem-sc-open-union-restriction-comparison-coherence`).

Also proved the new auxiliary theorem
`AlgebraicGeometry.Scheme.derived_open_restriction_iso_descent`
(node `lem-sc-derived-open-restriction-iso-descent`).

No `sorry` remains in either delivered module. No holes were added and no
statements were split off with `sorry`. Existing dependencies retain their own
proof status; they are used as the stage-3 brief requires.

The descent theorem imposes no nonempty-open hypothesis and works for the empty
and whole opens. The main proof imposes no extra relation on W,V: empty, disjoint,
nested and equal opens use the same four descent applications and cancellation
identities. The supplied equivalences and direct comparison isomorphisms are
unchanged inputs. `qI` is an explicit composition, not an arbitrary chosen witness.

## No longer needed

Removed these direct proof imports from the main module:

- `Sheaf.Algebra.Homology.OpenExtensionRestrictionIso`
- `Mathlib.CategoryTheory.Localization.Predicate`
- `Mathlib.CategoryTheory.Localization.Adjunction`
- `Mathlib.CategoryTheory.Localization.CalculusOfFractions.OfAdjunction`

The predicate import remains in the new descent module. The exact adjunction and
extension/restriction arguments are now supplied by the existing
`Sheaf.AlgebraicGeometry.DerivedOpenRestrictionLocalization` module. These removals do not establish
that any existing dependency module is unreachable from all targets. The original
exact-adjunction and extension/restriction nodes remain needed by descent, so they
remain indirect dependencies through `lem-pc-derived-open-restriction-is-localization`.
Both `lem-sc-derived-open-restriction-adjunction-exact` and
`lem-pc-open-extension-restriction-iso` were removed from this item's direct
`proof_deps`; `def-pc-derived-open-restriction-maps` remains directly needed.

No separate underived or derived threefold restriction coherence theorem is
needed: descend the already completed ambient comparison instead. Removed the
unsubmitted previous attempt's Data and Pasting modules and their copied nodes;
none belonged to the repository. The exploratory
`DerivedNestedOpenRestrictionCoherence` module is also absent from the delivery.

## Where the brief, the DAG or earlier work was wrong

The previous attempt left the original theorem unproved and its node copies
retained the original full statement instead of describing their proposed
intermediates. Bare existence of comparison data does not specify coherent
choices, and pasting equations cannot be asserted for arbitrary choices of those
comparisons. Neither previous intermediate is used or delivered.

The original plan's underived threefold-composition calculation is unnecessary
for this existential conclusion. The completed ambient comparison descends through
two localization functors, which supplies precisely the chosen overlap comparison
needed by each equation. This preserves the unit route; the item is not a realized
unit statement or proof step (`dag/units/sk-thm-picard-duality.json`).

The generic source-library `mapDerivedCategoryAdjunction` requires resolution and
monoidal infrastructure that this statement does not supply. The existing proved
`schemeDerivedOpenRestriction_isLocalization` already derives the exact adjunction
directly with only the given derived-category instances. The second reading found
and reused it, replacing the first reader's duplicated derivation. The Stacks
source 08BT and the supplied exact-adjunction interfaces agree with this argument.

## New nodes

`lem-sc-derived-open-restriction-iso-descent`, under
`dag/nodes/sec-picard-framework/`, records the proved descent theorem. It has no
union or overlap inputs: an isomorphism after any derived open restriction descends
to an isomorphism of the two given functors. Its source is Tag 08BT,
`cohomology.tex`, `lemma-adjoint-lower-shriek-restrict`, with the reuse of the
existing localization theorem documented in its proof origin. Actual searches
were logged with LeanFinder, Loogle and grep; LeanSearch returned an internal
server error and is recorded as unavailable. Blueprint searches for nested-open
restriction and isomorphism descent returned no existing blueprint match.

No change record is required because no existing interface was changed.

## Second reading by K3

1. Compared both delivered modules with the repository. The descent module is new;
   the existing theorem's signature is byte for byte identical after restoring one
   extra space at its proof boundary. Its visibility, public import, docstring,
   assumptions, let bindings, and conclusions are unchanged. No existing definition
   or target was altered; no change record is needed. Verdict: pass.

2. Compiled both revised modules in import order with lcompile.py, without errors or
   warnings. Compiled separate scratch copies with `#print axioms` for both public
   theorems: each uses exactly `propext`, `Classical.choice`, and `Quot.sound`, with
   no `sorryAx`. Scanned the delivered Lean sources: no sorry, axiom, unsafe, opaque,
   implemented_by, extern, or kernel-check bypass. There are no new definitions;
   qI is an explicit composition and the other choices are obtained inside proofs.
   Verdict: pass.

3. There are no statements split off with sorry. Reviewed the proved auxiliary
   statement: full faithfulness of precomposition supplies exactly the asserted
   isomorphism and whiskering equality. Empty and whole opens are covered by the
   existing localization theorem; no nonemptiness or strict inclusion is required.
   The main argument also covers empty, disjoint, nested, and equal W,V, because it
   uses no relations beyond those in the original statement. Independent searches
   used LeanFinder for reflective-localization precomposition, Loogle for
   FullyFaithful.preimageIso, and grep for localization/whiskering. Repository rg
   found the existing schemeDerivedOpenRestriction_isLocalization theorem, which
   the first proof duplicated. Reused it; no exact duplicate of the descent
   theorem was found. Verdict: pass after simplifying the auxiliary proof.

4. Followed the main proof from its original hole through explicit qI, the two
   ambient comparison isomorphisms, the four descent applications, and component
   cancellation. The argument supplies coherent choices, rather than asserting
   coherence for arbitrary comparisons. The helper now takes the shorter route
   through a proved library theorem and Mathlib. Its only proof imports are the
   localization theorem and Localization.Predicate; the main module imports the
   descent helper only for its proof. The no-longer-needed section names every
   removed direct import and both removed old direct proof dependencies, which
   remain indirectly needed. No whole-module pruning is claimed. Checked
   dag/units/sk-thm-picard-duality.json: its realized statement and step lists are
   empty; this item is below the unit level and changes no unit route. Verdict: pass.

5. Checked the original node diff: only proof, proof_deps, and proof_origin change.
   Its statement and Lean record are unchanged. Checked both step-dependency unions
   against proof_deps and the referenced nodes. Updated the new descent node to
   cite lem-pc-derived-open-restriction-is-localization, matching the shorter proof.
   Its source, searches, creation, blueprint, chapter/unit, and Lean record are
   present, and its Lean statement is recorded verbatim. Verdict: pass.

Second reading changed: restored signature-boundary whitespace; replaced the
auxiliary theorem's duplicated derived-adjunction construction by the existing
proved localization theorem; removed its four superseded proof imports; updated
its docstring, node proof/dependencies/origin and this report. The main proof is
otherwise retained. One original hole closed, zero holes added, zero unproved
statements split off; the auxiliary theorem is also fully proved.
