## What changed

Completed `AlgebraicGeometry.Scheme.Modules.openRestrictionNumeratorIso_mul` without
changing its signature or its public import. Added the proof-only import
`Sheaf.AlgebraicGeometry.TensorPowerOpenRestrictionAddition`. The final module
does not directly import `Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorBilinearUniversal`.
One proved private helper gives the inverse numerator comparison on arbitrary
pure tensors. Returned-delivery repair: removed the duplicate private
`AlgebraicGeometry.Scheme.Modules.tensor_hom_ext` declaration entirely.
The same-name existing theorem in
`Sheaf.AlgebraicGeometry.Modules.RestrictionTensorComparison` is private and
therefore cannot be imported and applied from this module. Instead the main
proof directly applies the existing public Mathlib declarations
`SheafOfModules.tensorObjIsoSheafification`,
`PresheafOfModules.sheafificationAdjunction`,
`PresheafOfModules.hom_ext`, and `ModuleCat.MonoidalCategory.tensor_ext`.
No duplicate statement remains; no existing module or visibility is changed.
These declarations are available through the existing statement import.
The proof cancels the numerator isomorphisms, uses sheaf tensor extensionality,
expands multiplication on sections, applies addition compatibility, and applies
the proved section-power compatibility in N. All sections of the nth power are
allowed; the argument does not assume that they are powers of the fixed section.

Split the structural addition compatibility into its own module and node. It
contains no fixed section s or coefficient sheaf F and is precisely the
power-addition part of the original node's plan, not a renamed transition theorem.
Both Lean files compiled together with the permitted lcompile.py.
The required deliver3.py --no-push dry run printed OK: compilation and
preflight passed except for the second reading, which the next worker writes.
Nothing was pushed.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Scheme.Modules.openRestrictionNumeratorIso_mul`
(`lem-sc-tensor-power-section-open-restriction-T`); its module has no direct sorry.
Added one hole in
`AlgebraicGeometry.Scheme.Modules.openRestrictionTensorPowIso_inv_add`
(`lem-sc-tensor-power-open-restriction-addition`), in the new module
`Sheaf.AlgebraicGeometry.TensorPowerOpenRestrictionAddition`.
Its entire proof is `by sorry`, with a source and complete induction/coherence
argument in its docstring and node. This is a decomposition: one hole closed,
one strictly structural hole added, net zero holes closed. The upper theorem
still depends on that hole and is not axiom-free yet.

Edge cases were checked mathematically: n=0 uses the left unitor and the
structure-ring isomorphism (including arbitrary scalars, not only 1); b=0 uses
the unit comparison; the empty open and zero sheaves impose no generator
assumption. The section s may be zero. The addition statement applies to all
open immersions, so no image-top identity is required in it.

## No longer needed

Removed the proof-only import
`Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorBilinearUniversal` from T and its
direct planned dependency `lem-pc-sites-sheaf-tensor-bilinear-universal`: the
proved sheafification adjunction and sectionwise tensor extensionality suffice.
The module remains reachable through the existing restriction tensor comparison,
and the new addition node still uses its universal-property argument; this is
no claim of whole-closure pruning. All other old proof dependencies remain used.
The original structural coherence and power-addition argument is isolated in
the new addition node. No unit statement or realized step was bypassed.

## Where the brief, the DAG or earlier work was wrong

The landing return correctly identified the duplicate private tensor_hom_ext.
Importing that exact theorem is impossible because RestrictionTensorComparison
marks it private. Removed its restatement and used the public adjunction and
sectionwise tensor extensionality directly at the point of use. This preserves
the existing module's visibility and all delivered public signatures.

The previous missing-artifact blocker is resolved: N.olean is now present and
both delivered files elaborate. The preceding report described the earlier
artifact failure; it has been replaced with this completed proof reduction.
The plan's addition/coherence step has no separate existing Lean statement;
searches of the source library, Sheaf, the imported blueprint, Lean Finder,
Loogle, and Mathlib grep found no exact statement. LeanSearch returned an
Internal Server Error, recorded as unavailable, not as a negative search.

The local Stacks TeX is unavailable. Read the official Tag 01CD and 01PW pages;
01CD states tensor-pullback functoriality and omits the proof. The recursive
coherence argument is therefore explicitly marked agent-written in proof_origin.
The ancestor script returned None because created.item is a module name; the
new node retains the item's already recorded blueprint ancestor and prepends
the item's node id to via, following the worker brief's inheritance rule.

## New nodes

`lem-sc-tensor-power-open-restriction-addition`, in
`dag/nodes/sec-curve-estimates/lem-sc-tensor-power-open-restriction-addition.json`,
records `AlgebraicGeometry.Scheme.Modules.openRestrictionTensorPowIso_inv_add` in
`lean/Sheaf/AlgebraicGeometry/TensorPowerOpenRestrictionAddition.lean`.
It isolates tensor-power addition compatibility on arbitrary pure tensor
sections. Its proof is induction on the first exponent after naturality,
associator and unitor coherence of the inverse restriction tensor comparison.
No existing statement, definition, or public interface was changed; no change
record or forced adaptation is needed.


## Second reading by U3

1. Compared the delivered T module against the repository with diff. Its sole
existing public theorem signature and docstring are byte for byte unchanged;
its existing public import is unchanged. The changes are its proof body, one
proved private helper and one plain proof import. No existing definition,
visibility or target statement changes. Verdict: pass.

2. Compiled both delivered modules in import order with lcompile.py: no errors
or warnings. Compiled scratch copies with #print axioms for the private helper,
main theorem and new addition theorem. The helper uses only propext,
Classical.choice and Quot.sound; the other two also use sorryAx, as explicitly
reported. The sole direct sorry is the named new addition theorem. Scanned all
delivered Lean source for prohibited declarations and kernel bypasses: none.
No data definition is added or changed. The inherited chosen tensor comparison
is uniquely determined as a sheaf morphism by its values on pure tensors on
every open, so it is not an arbitrary existence witness. Verdict: pass as a
decomposition, not an axiom-free proof.

3. Read the new addition statement, its proof docstring and node alongside the
actual recursive definitions of tensorPowAddIso and openRestrictionTensorPowIso.
For n=0 the formula transports an arbitrary scalar through the structure-ring
isomorphism and the left unitor; n=b=0 is scalar multiplication. For b=0 the
right unitor gives the same transport. The first successor is associator
coherence, and the general successor follows the same recursion. Zero sheaves
and empty opens cause no exception; no invertibility or generator is assumed.
The induction must establish equality of sheaf morphisms via the tensor
universal property, not assume arbitrary global sections are pure. This is
exactly the documented argument. The statement isolates the structural
addition step, omitting F and s, and is not a renamed copy of the main theorem.
Independent Lean Finder search for monoidal preservation of iterated tensor
addition, Loogle search for monoidal unit comparisons, and grep for restriction
monoidal structures found general coherence declarations but no exact theorem
for the chosen comparison. Source searches found tensorPowAddIso_inv_app_tmulSection,
which concerns powers of one fixed section and cannot handle arbitrary w here.
Read the official Stacks Tags 01CD and 01PW: the former supplies tensor-pullback
functoriality and omits its proof; the recursive expansion is correctly marked
agent-written. Closing the structural coherence hole is not a few-minute
application of an existing theorem. Verdict: pass.

4. Read the main proof from its two cancellations through the sheafification
adjunction and sectionwise tensor_ext to the numerator, addition and section
rewrites. It makes a real reduction on arbitrary sections of the nth power.
The two imports are needed: N supplies the signature's definitions and the
section compatibility; the new plain import supplies addition compatibility.
Compared old proof_deps: only the direct bilinear-universal dependency is
removed, and No longer needed records it. No module becomes unreachable by
this delivery. Read dag/units/sk-thm-curveestimate.json: the realized statement
thm-sc-proper-cohomology and the unit route are unchanged. Verdict: pass.

5. Compared the old node JSON against the delivered JSON: only proof,
proof_deps and proof_origin differ, and they follow the Lean reduction. The
new node's proof_deps are the union of its proof-step uses; its source, origin,
searches, split status, creation, blueprint ancestor, chapter, unit and Lean
record are present and match its theorem. Verdict: pass.

Changed only this report to remove a stale claim that the final T file adds
a direct bilinear-universal import, and made the new node's Lean statement
verbatim including its line breaks. No Lean proof repair was needed. Removed
the temporary axiom-probe copies before delivery. One upper hole is closed,
one lower structural hole is added: decomposition, net zero; no whole module
is pruned.
