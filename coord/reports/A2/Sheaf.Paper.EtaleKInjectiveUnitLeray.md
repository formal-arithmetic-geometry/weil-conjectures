## What changed

Proved `AlgebraicGeometry.Etale.etaleKInjective_unit_leray` in
`lean/Sheaf/Paper/EtaleKInjectiveUnitLeray.lean`, with its existing signature and
visibility unchanged. Three proved private helpers establish the defining Leray
unit equation, its compatibility with the derived adjunction on an arbitrary
homotopy-category object, and the underived sectionwise identification.
Naturality at `j`, the component hypothesis `hw`, and cancellation of the
K-injective unit finish the theorem. No new public declarations, modules,
statements, definitions, or axioms were introduced.

Updated the proof and proof origin of
`lem-weil-pbc-kinjective-unit-leray` to describe this argument. Its dependency
set is unchanged: preservation of K-injectives is still used in the canonical
Leray isomorphism, although no K-injectivity assertion about `f_*J` is needed.
The unit record `sk-prop-h2` has no realized nodes for this item; the unit route
is unchanged.

Searches used msearch LeanFinder (derived adjunction unit compatibility), Loogle
(`CategoryTheory.Functor.rightDerivedUnique`), msearch grep
(`rightDerivedFunctorObjQIso|derivedη_fac_app`), and direct source searches.
The source library supplies the needed abstract compatibility equations.
The already proved private `leray_fac` argument in
`Sheaf.Paper.DerivedUnitLerayId` was adapted to an arbitrary morphism; that
module is not imported and its identity-only theorem is not used.

## Proved and sorry left

Closed one hole:
`AlgebraicGeometry.Etale.etaleKInjective_unit_leray`
(node `lem-weil-pbc-kinjective-unit-leray`).

Sorries left in the item's module: none. Holes added: none. Split-off statements:
none. The helpers `leray_fac`, `unit_leray_h`, and `sections_unit` are private and
fully proved. This is a proof, not a decomposition into new holes.

Single-file compilation and the delivery dry run check the unchanged statement,
the complete proof, imports, declaration probe, and delivery records.

## No longer needed

Removed three redundant direct proof imports, whose contents are already
publicly imported by the retained statement imports:

- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp`
- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`

No module leaves the transitive import closure, and no DAG dependency node is
pruned. All three existing public statement imports are retained. No additional
Sheaf statement module is needed.

The original first proof step, taking the adjunct of `j` and establishing
K-injectivity of `f_*J`, is unnecessary. Computing the unit--Leray equation before
inverting any units works on every homotopy-category object and avoids that step.
The preservation theorem remains a dependency of the canonical Leray construction.

## Where the brief, the DAG or earlier work was wrong

No false statement or unusable interface was found. The DAG's adjunct-first route
was longer than necessary; the updated proof records the direct naturality route.
The source library already provides the derived adjunction and composition
compatibilities, so there was no need to split off additional lemmas. The local
Stacks TeX files are absent; the proof was checked against the existing node and
the formal definitions and compatibility theorems in Mathlib and the source library.

## Second reading by A2

1. **Interfaces: pass.** Compared the sole delivered Lean module with the repository
   using `diff` and checked the complete existing theorem signature byte for byte.
   Hypotheses, conclusion, universes, visibility, and all three public imports are
   unchanged. No definitions or change records are introduced. The node diff changes
   only `proof` and `proof_origin`.
2. **Proof and axioms: pass.** Independently compiled the module with `lcompile.py`
   without errors or warnings. A scratch copy with `#print axioms` for
   `AlgebraicGeometry.Etale.etaleKInjective_unit_leray` and all three private helpers
   reports exactly `propext`, `Classical.choice`, and `Quot.sound` for each; no
   `sorryAx`. The delivered source contains no `sorry`, prohibited declaration,
   or data construction from an unproved existence theorem. One original hole is
   closed; no holes are added.
3. **Split statements: pass, none.** No new public or split-off statements, modules,
   or nodes exist. Each private helper is fully proved. Checked the defining
   composite unit, the direction of `derivedη_fac_app`, the terminal-section
   comparison, and the directions of the inverse units against the upstream source.
   The general helper needs no K-injectivity; only the final unit inversions use
   the existing hypotheses. Zero complexes/maps and identity scheme morphisms
   obey the same naturality equations, without an extra nonzero or invertibility
   assumption on `j`.
4. **Route and pruning: pass.** Independently searched with msearch grep for
   `mapDerivedCategoryRightDerivedAdjunction.unit|globalSectionsUpperStarMap`
   and with `rg` for unit--Leray and derived-unit naturality results in Sheaf and
   upstream. No existing public theorem gives this arbitrary-morphism calculation.
   The identity-only helper in `DerivedUnitLerayId` is private and does not replace
   this proof. The proof uses the upstream compatibility equations directly; no
   shorter established route was found. Retained public imports supply the actual
   statement's Leray comparison, derived adjunction, and K-injective comparison
   isomorphisms. All three removed proof imports are transitively supplied by them.
   Every old proof dependency remains used, including preservation of K-injectives
   in the canonical Leray construction, so the report correctly prunes no nodes or
   transitive modules. Checked `dag/units/sk-prop-h2.json`: its `realized` statement
   and step lists are empty, and no unit route is bypassed.
5. **DAG: pass.** Read the item node and the Lean records of all three proof
   dependencies. The new three proof steps describe the helper calculation,
   component identification, and final naturality/cancellation in the Lean proof.
   Their `uses` union equals the unchanged `proof_deps`; `proof_origin` correctly
   attributes the new proof to A2. Existing statement and node metadata are retained.

Second reading changed only this report and added an independent search record;
no repair to the Lean proof or DAG was needed. The retained theorem docstring
outlines the older valid adjunct-first argument; the delivered DAG and report
accurately describe the shorter argument actually implemented. Scratch axiom
checks are not delivery modules.
