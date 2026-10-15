## What changed

Proved `Algebra.ClosedLift.isUnit_of_isUnit_toAlgHom` in
`Sheaf.RingTheory.ProEtale.ClosedLiftUnits`, with its signature unchanged.
The proof chooses a stage representative, localizes that stage at the representative,
transports the localization to a polynomial-quotient index, and maps its unit into the colimit.
The retained-map equation is proved directly from `colimit.ι_desc`.
Updated the existing node's proof and proof origin to describe the actual Lean implementation.

The prescribed single-file compiler passes without warnings. No definitions, public imports,
or existing statements changed, and no new declarations or modules were added.
The localization argument also covers the zero ring and zero elements mapping to units:
localization at zero is allowed, with no domain or nontriviality assumption used.

## Proved and sorry left

Closed one hole: `Algebra.ClosedLift.isUnit_of_isUnit_toAlgHom`
(node `lem-exc-closed-lift-units`). Added zero holes. No `sorry` remains in the item or
elsewhere in this delivery. This is a proof from existing dependencies, not a decomposition.
The existing imported `Algebra.ClosedLift.isFiltered_index` remains an upstream obligation;
this delivery does not claim that the target import closure is already axiom-free.
The proof does not use the sorried `Algebra.ClosedLift.ι_toAlgHom` theorem.

## No longer needed

Removed all five redundant proof imports: `Mathlib.Algebra.Category.Ring.FilteredColimits`,
`Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic`,
`Mathlib.RingTheory.Localization.Away.Basic`, `Mathlib.RingTheory.Etale.Basic`, and
`WeilConjectures.RingTheory.ProEtale.ClosedLift`. Their interfaces and instances are already
supplied by the existing public import `Sheaf.RingTheory.ProEtale.ClosedLiftMap` and its
transitive dependencies. The second reader verified the proof compiles with that sole import.
A trial explicit import of `WeilConjectures.Mathlib.Algebra.Category.CommAlgCat.Basic` was
likewise unnecessary and is absent from the delivered file.

No planned dependency node is pruned: all six original proof dependencies remain needed
for the representative, filteredness, localization, extension, and etaleness arguments.
No unit statement or realized step is bypassed.

## Where the brief, the DAG or earlier work was wrong

No mathematical error found. The existing preservation instance already supplies the
underlying-set colimit argument that the DAG described by hand. The DAG omitted the
explicit transport of the localized algebra to the small polynomial-quotient model;
the proof now includes that transport using existing Mathlib declarations.


## Second reading by F2

1. Compared the complete Lean diff against the repository. The sole existing declaration,
   `Algebra.ClosedLift.isUnit_of_isUnit_toAlgHom`, retains its signature byte for byte,
   including the quotient-algebra, scalar-tower and ind-etale assumptions. No definition,
   public import, visibility, or statement changed; no change record is needed. PASS.
2. Independently compiled the submitted file and a scratch copy with the minimal import
   set and `#print axioms`. No compiler errors or warnings, no `sorry` in the delivered
   file, and no forbidden declarations or attributes. The theorem's axioms are
   `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`; the existing upstream
   `Algebra.ClosedLift.isFiltered_index` is still open and has this same axiom set.
   The proof uses `colimit.ι_desc` directly rather than the open `ι_toAlgHom` theorem.
   The existential presentation comes from the proved Mathlib finite-type theorem;
   no data is chosen from an unproved mere-existence result. PASS.
3. No statements or holes were split off and no declarations or nodes were added.
   Checked the localization construction for a zero representative and zero input ring:
   localization at zero is permitted and the lift requires exactly the supplied unit
   hypothesis, so no nontriviality assumption is hidden. PASS.
4. Read the representative, localization lift, finite-presentation and first-isomorphism
   steps against their declarations. `lift_eq` proves the compatibility of the transition
   with C; `algebraMap_isUnit`, `e.symm`, and `colimit.w` then give the asserted unit.
   Fresh Lean Finder and Loogle searches (different query wording), plus `rg` in the
   library and Mathlib, found no direct theorem replacing this argument. Removed the
   three remaining redundant proof imports after a successful minimal-import scratch
   compile. All six old proof dependencies remain used. The unit record's `realized`
   fields are unchanged (currently empty); this delivery follows the original node's
   localization route and bypasses no realized unit step. PASS after import pruning.
5. Compared both node JSON files: only `proof` and `proof_origin` differ. Each of the
   four revised steps describes the actual Lean proof, including the quotient-presentation
   transport required by `Index`. Their dependency union is exactly `proof_deps`.
   The node's mathematical statement, Lean signature, source, chapter and unit are
   unchanged. PASS.

Second-reading changes: removed the remaining three redundant proof imports and updated
this report's import list and independent review. The proof body and node edits were correct
and are retained.
